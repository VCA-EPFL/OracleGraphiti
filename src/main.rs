use egg::{rewrite as rw, AstSize, Extractor, RecExpr, Runner, SymbolLang, *};
use serde_json::{self};
use std::io::{self, Read};
use core::panic;
use symbolic_expressions::parser::parse_str;
use symbolic_expressions::Sexp;

fn get_rules() -> Vec<Rewrite<SymbolLang, ()>> {
    vec![
        rw!("L"; "(join ?s1 ?x (join ?s2 ?y ?z))" => "(join ?s2 (join ?s1 ?x ?y) ?z)"),
        rw!("R"; "(join ?s1 (join ?s2 ?x ?y) ?z)" => "(join ?s2 ?x (join ?s1 ?y ?z))"),
        rw!("E"; "(join ?s1 (split1 ?s2 ?x) (split2 ?s3 ?x))" => "?x"),
        rw!("C"; "(join ?s1 ?x ?y)" => "(join ?s1 ?y ?x)"),
        rw!("PL"; "(join ?s1 (pure ?s2 ?x) ?y)" => "(pure ?s2 (join ?s1 ?x ?y))"),
        rw!("PR"; "(join ?s1 ?x (pure ?s2 ?y))" => "(pure ?s2 (join ?s1 ?x ?y))"),
        rw!("PE"; "(pure ?s1 (pure ?s2 ?x))" => "(pure ?s1 ?x)"),
    ]
}

#[derive(serde::Serialize)]
struct Step {
    rw: String,
    args: Vec<String>,
}

fn find_rewrite_term_and_rule(sexp1: &str, sexp2: &str) -> Option<(String,String)> {
    let term1 = parse_str(sexp1).ok()?;
    let term2 = parse_str(sexp2).ok()?;
    
    // Find the Rewrite marker in the second term
    let rewrite_pos = find_rewrite_position(&term2)?;
    
    // Get the original term from the first expression
    let result = get_term_at_position(&term1, &rewrite_pos)?;
    // And the Rewrite term from the second one, to get the rule name
    let rw= get_term_at_position(&term2, &rewrite_pos)?;
    match rw {
        Sexp::List(list) => {
            return Some((result.to_string(), list[1].to_string()));
        }
        _ => panic!("Unexpected"),
    }
    
}

fn find_rewrite_position(sexp: &Sexp) -> Option<Vec<usize>> {
    match sexp {
        Sexp::List(list) => {
            // Check if this node is a rewrite marker
            if list.len() == 3 {
                if let Sexp::String(first) = &list[0] {
                    if first == "Rewrite=>" {
                        return Some(vec![]);
                    }
                }
            }
            
            // Else search through subterms
            for (i, subterm) in list.iter().enumerate() {
                if let Some(mut pos) = find_rewrite_position(subterm) {
                    pos.insert(0, i);
                    return Some(pos);
                }
            }
            None
        }
        Sexp::String(_) => None,
        Sexp::Empty => None,
    }
}

fn get_term_at_position<'a>(sexp: &'a Sexp, position: &[usize]) -> Option<&'a Sexp> {
    if position.is_empty() {
        return Some(sexp);
    }
    
    match sexp {
        Sexp::List(list) => {
            let index = position[0];
            if index < list.len() {
                get_term_at_position(&list[index], &position[1..])
            } else {
                None
            }
        }
        Sexp::String(_) => None,
        Sexp::Empty => None,
    }
}

fn extract_args_from_sexps(repr: &str, rule: &str) -> Vec<String> {
    let parsed = symbolic_expressions::parser::parse_str(&repr).unwrap();

    // Defensive
    let list = match parsed {
        Sexp::List(l) => l,
        _ => return vec![],
    };

    if list.len() < 2 {
        return vec![];
    }

    match rule {
        // "L" => {
        //     // Expect: (join ?s1 ?x (join ?s2 ?y ?z))
        //     // s1 is at index 1
        //     // The nested join is at index 3, and its element at index 1 is s2.
        //     let s1 = list.get(1).map(|s| s.to_string()).unwrap_or_default();
        //     let s2 = if list.len() > 3 {
        //         if let Sexp::List(nested) = &list[3] {
        //             nested.get(1).map(|s| s.to_string()).unwrap_or_default()
        //         } else {
        //             "".to_string()
        //         }
        //     } else {
        //         "".to_string()
        //     };
        //     vec![s1, s2]
        // }
        // "R" => {
        //     // Expect: (join ?s1 (join ?s2 ?x ?y) ?z)
        //     // s1 is at index 1
        //     // The nested join is at index 2, and its element at index 1 is s2.
        //     let s1 = list.get(1).map(|s| s.to_string()).unwrap_or_default();
        //     let s2 = if list.len() > 2 {
        //         if let Sexp::List(nested) = &list[2] {
        //             nested.get(1).map(|s| s.to_string()).unwrap_or_default()
        //         } else {
        //             "".to_string()
        //         }
        //     } else {
        //         "".to_string()
        //     };
        //     vec![s1, s2]
        // }
        "E" | "C" | "L" | "R" | "PE" | "PL" | "PR" => {
            // For these, we only need ?s1, which is at index 1.
            let s1 = list.get(1).map(|s| s.to_string()).unwrap_or_default();
            vec![s1]
        }
        _ => vec![],
    }
}


fn explanation_to_steps(flat: &[FlatTerm<SymbolLang>]) -> Vec<Step> {
    let mut steps = Vec::new();

    // Iterate over adjacent pairs of flat terms (each pair represents one rewrite step).
    for pair in flat.windows(2) {
        let current = &pair[0];
        let next = &pair[1];

        // println!("{}\n TRANSFORM\n {}", current, next);
        let (matched,r_name) = find_rewrite_term_and_rule(&current.remove_rewrites().to_string(),&next.to_string()).unwrap();
        // println!("\n MATCHED {}: {}", r_name, matched);

        // extract the arguments at the desired positions.
        let args = extract_args_from_sexps(&matched, &r_name);

        steps.push(Step { rw: r_name, args });
    }
    steps
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let input = input.trim();

    let expr: RecExpr<SymbolLang> = input.parse().unwrap();
    let rules = get_rules();

    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&expr)
        .run(&rules);

    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_cost, end_best) = extractor.find_best(runner.roots[0]);
    let mut explanation = runner
        .explain_equivalence(&expr, &end_best);
    let explanation_steps = explanation.make_flat_explanation();
    let steps = explanation_to_steps(&explanation_steps);

    println!("{}", serde_json::to_string(&steps).unwrap());
}
