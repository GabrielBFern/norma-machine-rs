extern crate pest;
use pest::error::Error;
#[macro_use]
extern crate pest_derive;

use num_bigint::BigUint;
use num_traits::{One, Zero};

use pest::Parser;

#[derive(Parser)]
#[grammar = "norma.pest"]
pub struct NORMAParser;

use std::collections::HashMap;

#[derive(Debug)]
pub enum ASTNorma<'a> {
    Increment {
        register: &'a str,
        next_inst: Option<usize>,
    },
    Decrement {
        register: &'a str,
        next_inst: Option<usize>,
    },
    IfZeros {
        register: &'a str,
        true_inst: usize,
        false_inst: usize,
    },
}

type Program<'a> = Vec<ASTNorma<'a>>;

impl<'a> ASTNorma<'a> {
    pub fn parse(source: &'a str) -> Result<Program<'a>, Error<Rule>> {
        let mut ast = Vec::new();
        let pairs = NORMAParser::parse(Rule::program, source)?;
        for pair in pairs {
            match pair.as_rule() {
                Rule::statements => {
                    ast.push(Self::build_ast_from_statements(pair));
                }
                _ => {}
            }
        }

        Ok(ast)
    }

    fn build_ast_from_statements(pair: pest::iterators::Pair<'a, Rule>) -> Self {
        let pair = pair.into_inner().next().unwrap();
        match pair.as_rule() {
            Rule::inc => {
                let mut pair = pair.into_inner();
                let register = pair.next().unwrap().as_str();
                let next_inst = pair.next().map(|inst| inst.as_str().parse().unwrap());
                Self::Increment {
                    register,
                    next_inst,
                }
            }
            Rule::dec => {
                let mut pair = pair.into_inner();
                let register = pair.next().unwrap().as_str();
                let next_inst = pair.next().map(|inst| inst.as_str().parse().unwrap());
                Self::Decrement {
                    register,
                    next_inst,
                }
            }
            Rule::ifz => {
                let mut pair = pair.into_inner();
                let register = pair.next().unwrap().as_str();
                let true_inst = pair
                    .next()
                    .map(|inst| inst.as_str().parse().unwrap())
                    .unwrap();
                let false_inst = pair
                    .next()
                    .map(|inst| inst.as_str().parse().unwrap())
                    .unwrap();
                Self::IfZeros {
                    register,
                    true_inst,
                    false_inst,
                }
            }
            unknown_expr => panic!("Unexpected statements: {:?}", unknown_expr),
        }
    }

    fn run(&self, context: &mut Context) {
        match self {
            ASTNorma::Increment {
                register,
                next_inst,
            } => {
                context.inc(register);
                match next_inst {
                    Some(inst) => context.cursor = *inst,
                    None => context.cursor += 1,
                }
            }
            ASTNorma::Decrement {
                register,
                next_inst,
            } => {
                context.dec(register);
                match next_inst {
                    Some(inst) => context.cursor = *inst,
                    None => context.cursor += 1,
                }
            }
            ASTNorma::IfZeros {
                register,
                true_inst,
                false_inst,
            } => {
                context.cursor = if *context.get_register(register) == BigUint::zero() {
                    *true_inst
                } else {
                    *false_inst
                }
            }
        }
    }
}

pub struct NORMAInterpreter;

#[derive(Debug)]
pub struct Context {
    pub cursor: usize,
    registers: HashMap<String, BigUint>,
}

impl Context {
    pub fn new() -> Self {
        Self {
            cursor: 1,
            registers: HashMap::new(),
        }
    }

    fn inc(&mut self, register: &str) {
        let register = self.get_register(register);
        *register += BigUint::one();
    }

    fn dec(&mut self, register: &str) {
        let register = self.get_register(register);
        if !register.is_zero() {
            *register -= BigUint::one();
        }
    }

    fn get_register(&mut self, register: &str) -> &mut BigUint {
        use std::collections::hash_map::Entry;
        match self.registers.entry(register.into()) {
            Entry::Occupied(occ_entry) => occ_entry.into_mut(),
            Entry::Vacant(vac_entry) => vac_entry.insert(Zero::zero()),
        }
    }

    pub fn get_registers(&self) -> Vec<(String, BigUint)> {
        self.registers.clone().into_iter().collect()
    }

    pub fn run(&mut self, prg: &Program) {
        while self.run_bound(prg) != None {}
    }

    pub fn run_bound(&mut self, prg: &Program) -> Option<()> {
        let instruct = self.cursor;
        let stmt = prg.get(instruct);
        match stmt {
            Some(stmt) => {
                stmt.run(self);
                Some(())
            }
            None => None,
        }
    }
}

impl<'a> NORMAInterpreter {
    pub fn run(prg: &'a Program) -> Context {
        let mut context = Context::new();
        context.run(prg);
        context
    }
}

#[test]
fn test_basic() {
    // ...
}
