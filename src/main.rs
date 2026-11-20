//! Organon: a tiny interpreter where the program is an RDF graph written in Turtle.
//!
//! Pipeline: source text -> tokens -> triples -> graph (arena + edges) -> run.
//!
//! Semantics (v0):
//!   - Execution begins at every `organon:Thread organon:start F` triple.
//!   - F must be declared `a organon:Function`.
//!   - A function's `organon:calls` edges run in the order they appear.
//!       - `organon:print` is a builtin that prints the function's arguments.
//!       - Any other callee is treated as a user function and run recursively.
//!   - A function's arguments are its `organon:hasArgument` targets. Each argument
//!     resolves to a value through `organon:hasValue`, or is itself a literal.

use std::collections::HashMap;
use std::env;
use std::fs;
use std::process;

// ===================================================================
// Tokenizer
// ===================================================================

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Name(String),    // prefixed name (organon:Buffer), `a`, `@prefix`, or <full IRI>
    Literal(String), // "a quoted string"
    Dot,
    Semicolon,
    Comma,
}

fn is_delimiter(c: char) -> bool {
    c.is_whitespace() || matches!(c, ';' | ',' | '"' | '#')
}

/// Returns the index just past the end of a name that starts at `start`.
/// A '.' ends the name unless more name characters follow it (so `ex:v1.2` works
/// but the final '.' in `ex:thing .` or `ex:thing.` is a statement terminator).
fn name_end(chars: &[char], start: usize) -> usize {
    let mut i = start;
    while i < chars.len() {
        let c = chars[i];
        if is_delimiter(c) {
            break;
        }
        if c == '.' {
            let next = chars.get(i + 1);
            if next.map_or(true, |&n| is_delimiter(n) || n == '.') {
                break;
            }
        }
        i += 1;
    }
    i
}

fn tokenize(src: &str) -> Result<Vec<Token>, String> {
    let chars: Vec<char> = src.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;

    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        match c {
            '#' => {
                // Comment: skip to end of line
                while i < chars.len() && chars[i] != '\n' {
                    i += 1;
                }
            }
            '.' => {
                tokens.push(Token::Dot);
                i += 1;
            }
            ';' => {
                tokens.push(Token::Semicolon);
                i += 1;
            }
            ',' => {
                tokens.push(Token::Comma);
                i += 1;
            }
            '"' => {
                i += 1;
                let mut s = String::new();
                loop {
                    match chars.get(i) {
                        None => return Err("unterminated string literal".into()),
                        Some('"') => {
                            i += 1;
                            break;
                        }
                        Some('\\') => {
                            match chars.get(i + 1) {
                                Some('n') => s.push('\n'),
                                Some('t') => s.push('\t'),
                                Some(&other) => s.push(other),
                                None => return Err("unterminated escape in string".into()),
                            }
                            i += 2;
                        }
                        Some(&other) => {
                            s.push(other);
                            i += 1;
                        }
                    }
                }
                // Skip a datatype (^^xsd:string) or language tag (@en) after a literal
                if chars.get(i) == Some(&'^') && chars.get(i + 1) == Some(&'^') {
                    i = name_end(&chars, i + 2);
                } else if chars.get(i) == Some(&'@') {
                    i = name_end(&chars, i + 1);
                }
                tokens.push(Token::Literal(s));
            }
            '<' => {
                let start = i;
                while i < chars.len() && chars[i] != '>' {
                    i += 1;
                }
                if i == chars.len() {
                    return Err("unterminated <IRI>".into());
                }
                i += 1;
                tokens.push(Token::Name(chars[start..i].iter().collect()));
            }
            _ => {
                let end = name_end(&chars, i);
                tokens.push(Token::Name(chars[i..end].iter().collect()));
                i = end;
            }
        }
    }
    Ok(tokens)
}

// ===================================================================
// Parser: tokens -> triples (supports `;` and `,` shorthand)
// ===================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Term {
    Name(String),
    Literal(String),
}

#[derive(Debug)]
struct Triple {
    subject: Term,
    predicate: String,
    object: Term,
}

fn describe(t: Option<&Token>) -> String {
    match t {
        None => "end of file".into(),
        Some(Token::Name(n)) => format!("`{n}`"),
        Some(Token::Literal(s)) => format!("\"{s}\""),
        Some(Token::Dot) => "`.`".into(),
        Some(Token::Semicolon) => "`;`".into(),
        Some(Token::Comma) => "`,`".into(),
    }
}

fn expect_name(tokens: &[Token], i: &mut usize, what: &str) -> Result<String, String> {
    match tokens.get(*i) {
        Some(Token::Name(n)) => {
            *i += 1;
            Ok(n.clone())
        }
        other => Err(format!("expected {what}, found {}", describe(other))),
    }
}

fn expect_term(tokens: &[Token], i: &mut usize) -> Result<Term, String> {
    match tokens.get(*i) {
        Some(Token::Name(n)) => {
            *i += 1;
            Ok(Term::Name(n.clone()))
        }
        Some(Token::Literal(s)) => {
            *i += 1;
            Ok(Term::Literal(s.clone()))
        }
        other => Err(format!("expected an object, found {}", describe(other))),
    }
}

fn parse(tokens: &[Token]) -> Result<Vec<Triple>, String> {
    let mut triples = Vec::new();
    let mut i = 0;

    while i < tokens.len() {
        // Skip @prefix / @base directives. v0 compares prefixed names as written,
        // so prefixes aren't expanded; they're accepted so the file stays valid Turtle.
        if let Token::Name(n) = &tokens[i] {
            if n == "@prefix" || n == "@base" {
                while i < tokens.len() && tokens[i] != Token::Dot {
                    i += 1;
                }
                i += 1;
                continue;
            }
        }

        let subject = expect_name(tokens, &mut i, "a subject")?;
        let context = |e: String| format!("in the statement about `{subject}`: {e}");

        loop {
            let predicate = expect_name(tokens, &mut i, "a predicate").map_err(context)?;
            loop {
                let object = expect_term(tokens, &mut i).map_err(context)?;
                triples.push(Triple {
                    subject: Term::Name(subject.clone()),
                    predicate: predicate.clone(),
                    object,
                });
                if tokens.get(i) == Some(&Token::Comma) {
                    i += 1; // same subject and predicate, another object
                } else {
                    break;
                }
            }
            match tokens.get(i) {
                Some(Token::Semicolon) => i += 1, // same subject, another predicate
                Some(Token::Dot) => {
                    i += 1;
                    break;
                }
                other => {
                    return Err(context(format!(
                        "expected `;` or `.` after the object, found {}. \
                         Did an earlier line end without ` .`?",
                        describe(other)
                    )));
                }
            }
        }
    }
    Ok(triples)
}

// ===================================================================
// Graph: interned nodes in an arena, labeled edges between them
// ===================================================================

#[derive(Debug, PartialEq)]
enum EdgeKind {
    Type,
    Start,
    HasArgument,
    HasValue,
    Calls,
    Other(String),
}

fn edge_kind(predicate: &str) -> EdgeKind {
    match predicate {
        "a" | "rdf:type" => EdgeKind::Type,
        "organon:start" => EdgeKind::Start,
        "organon:hasArgument" => EdgeKind::HasArgument,
        "organon:hasValue" => EdgeKind::HasValue,
        "organon:calls" => EdgeKind::Calls,
        other => EdgeKind::Other(other.to_owned()),
    }
}

struct Node {
    term: Term,
    edges: Vec<(EdgeKind, usize)>, // outgoing, in source order
}

struct Graph {
    nodes: Vec<Node>,
    index: HashMap<Term, usize>,
}

impl Graph {
    fn from_triples(triples: Vec<Triple>) -> Graph {
        let mut graph = Graph {
            nodes: Vec::new(),
            index: HashMap::new(),
        };
        for t in triples {
            let s = graph.get_or_create(t.subject);
            let o = graph.get_or_create(t.object);
            graph.nodes[s].edges.push((edge_kind(&t.predicate), o));
        }
        graph
    }

    /// Same term -> same node, so a thing defined in one place and used in
    /// another is a single node with several edges.
    fn get_or_create(&mut self, term: Term) -> usize {
        if let Some(&i) = self.index.get(&term) {
            return i;
        }
        let i = self.nodes.len();
        self.nodes.push(Node {
            term: term.clone(),
            edges: Vec::new(),
        });
        self.index.insert(term, i);
        i
    }

    fn lookup(&self, name: &str) -> Option<usize> {
        self.index.get(&Term::Name(name.to_owned())).copied()
    }

    fn name(&self, node: usize) -> String {
        match &self.nodes[node].term {
            Term::Name(n) => n.clone(),
            Term::Literal(s) => format!("\"{s}\""),
        }
    }

    /// All nodes reachable from `node` by edges of the given kind, in source order.
    fn targets(&self, node: usize, kind: &EdgeKind) -> Vec<usize> {
        self.nodes[node]
            .edges
            .iter()
            .filter(|(k, _)| k == kind)
            .map(|&(_, target)| target)
            .collect()
    }

    fn has_type(&self, node: usize, class: &str) -> bool {
        self.targets(node, &EdgeKind::Type)
            .iter()
            .any(|&t| self.name(t) == class)
    }

    /// Turn an argument node into a printable value.
    fn resolve(&self, node: usize) -> Result<String, String> {
        match &self.nodes[node].term {
            Term::Literal(s) => Ok(s.clone()),
            Term::Name(n) => match self.targets(node, &EdgeKind::HasValue).as_slice() {
                [v] => match &self.nodes[*v].term {
                    Term::Literal(s) => Ok(s.clone()),
                    Term::Name(m) => {
                        Err(format!("value of `{n}` is `{m}`, which is not a literal"))
                    }
                },
                [] => Err(format!(
                    "`{n}` is used as an argument but has no organon:hasValue"
                )),
                _ => Err(format!("`{n}` has more than one organon:hasValue")),
            },
        }
    }
}

// ===================================================================
// Interpreter
// ===================================================================

const MAX_DEPTH: usize = 64;

fn run(graph: &Graph) -> Result<(), String> {
    let thread = graph
        .lookup("organon:Thread")
        .ok_or("program has no organon:Thread")?;
    let entry_points = graph.targets(thread, &EdgeKind::Start);
    if entry_points.is_empty() {
        return Err("organon:Thread has no organon:start".into());
    }
    for f in entry_points {
        call(graph, f, 0)?;
    }
    Ok(())
}

fn call(graph: &Graph, func: usize, depth: usize) -> Result<(), String> {
    let name = graph.name(func);
    if depth > MAX_DEPTH {
        return Err(format!(
            "call depth exceeded {MAX_DEPTH} at `{name}` (infinite recursion?)"
        ));
    }
    if !graph.has_type(func, "organon:Function") {
        return Err(format!(
            "`{name}` is called but is not declared `a organon:Function`"
        ));
    }

    let args = graph.targets(func, &EdgeKind::HasArgument);
    let callees = graph.targets(func, &EdgeKind::Calls);
    if callees.is_empty() {
        eprintln!("warning: `{name}` has no organon:calls, so it does nothing");
    }

    for callee in callees {
        match graph.name(callee).as_str() {
            "organon:print" => builtin_print(graph, &args)?,
            _ => call(graph, callee, depth + 1)?,
        }
    }
    Ok(())
}

fn builtin_print(graph: &Graph, args: &[usize]) -> Result<(), String> {
    let values = args
        .iter()
        .map(|&a| graph.resolve(a))
        .collect::<Result<Vec<String>, String>>()?;
    println!("{}", values.join(" "));
    Ok(())
}

// ===================================================================
// Entry point
// ===================================================================

fn execute(src: &str) -> Result<(), String> {
    let tokens = tokenize(src)?;
    let triples = parse(&tokens)?;
    let graph = Graph::from_triples(triples);
    run(&graph)
}

fn main() {
    let path = match env::args().nth(1) {
        Some(p) => p,
        None => {
            eprintln!("usage: organon <program.ttl>");
            process::exit(2);
        }
    };
    let src = fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("could not read {path}: {e}");
        process::exit(1);
    });
    if let Err(e) = execute(&src) {
        eprintln!("error: {e}");
        process::exit(1);
    }
}
