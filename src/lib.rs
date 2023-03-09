extern crate pest;
#[macro_use]
extern crate pest_derive;

use error::NormaMachineError;
use num_bigint::BigUint;
use num_traits::{One, Zero};

use pest::Parser;

#[derive(Parser)]
#[grammar = "norma.pest"]
struct NORMAParser;

use std::collections::HashMap;

pub mod error;

#[derive(Debug, Clone)]
enum NormaAST {
    Increment {
        register: String,
        next_inst: Option<usize>,
    },
    Decrement {
        register: String,
        next_inst: Option<usize>,
    },
    IfZeros {
        register: String,
        true_inst: usize,
        false_inst: usize,
    },
    IfNotZeros {
        register: String,
        true_inst: usize,
        false_inst: usize,
    },
    NoOp,
}

#[derive(Clone, Debug)]
pub struct NormaProgram {
    stmts: Vec<NormaAST>,
}

#[derive(Clone, Debug)]
pub struct Context {
    inst: usize,
    cursor: usize,
    registers: HashMap<String, BigUint>,
}

#[derive(Clone, Debug)]
pub struct NormaMachine {
    program: NormaProgram,
    ctx: Context,
}

impl NormaProgram {
    fn new(stmts: Vec<NormaAST>) -> NormaProgram {
        NormaProgram { stmts }
    }

    pub fn parse(source: &str) -> Result<NormaProgram, NormaMachineError> {
        if source.trim().is_empty() {
            return Err(NormaMachineError::EmptySource);
        }
        let mut stmts = Vec::new();
        let pairs = NORMAParser::parse(Rule::program, source)?;
        for pair in pairs {
            if let Rule::statements = pair.as_rule() {
                stmts.push(NormaAST::build_ast_from_statements(pair));
            }
        }

        Ok(Self::new(stmts))
    }
}

impl NormaMachine {
    pub fn new(prg: NormaProgram) -> NormaMachine {
        Self::from_context(prg, Context::default())
    }

    pub fn from_context(program: NormaProgram, ctx: Context) -> NormaMachine {
        NormaMachine { program, ctx }
    }

    pub fn run(&mut self) {
        while self.run_bound().is_some() {}
    }

    pub fn run_bound(&mut self) -> Option<()> {
        let instruct = self.ctx.get_cursor();
        let stmt = self.program.stmts.get(instruct);
        let r = match stmt {
            Some(stmt) => {
                stmt.execute(&mut self.ctx);
                Some(())
            }
            None => None,
        };
        self.ctx.inst += 1;
        r
    }

    pub fn get_context(&self) -> &Context {
        &self.ctx
    }
}

impl NormaAST {
    fn build_ast_from_statements(pair: pest::iterators::Pair<Rule>) -> Self {
        let pair = pair.into_inner().next().unwrap();
        match pair.as_rule() {
            Rule::inc => {
                let mut pair = pair.into_inner();
                let register = pair.next().unwrap().as_str().into();
                let next_inst = pair
                    .next()
                    .map(|inst| inst.as_str().parse().unwrap())
                    .map(|i: usize| i - 1);
                Self::Increment {
                    register,
                    next_inst,
                }
            }
            Rule::dec => {
                let mut pair = pair.into_inner();
                let register = pair.next().unwrap().as_str().into();
                let next_inst = pair
                    .next()
                    .map(|inst| inst.as_str().parse().unwrap())
                    .map(|i: usize| i - 1);
                Self::Decrement {
                    register,
                    next_inst,
                }
            }
            Rule::ifz => {
                let mut pair = pair.into_inner();
                let register = pair.next().unwrap().as_str().into();
                let true_inst: usize = pair
                    .next()
                    .map(|inst| inst.as_str().parse().unwrap())
                    .unwrap();
                let false_inst: usize = pair
                    .next()
                    .map(|inst| inst.as_str().parse().unwrap())
                    .unwrap();
                Self::IfZeros {
                    register,
                    true_inst: true_inst - 1,
                    false_inst: false_inst - 1,
                }
            }
            Rule::ifnz => {
                let mut pair = pair.into_inner();
                let register = pair.next().unwrap().as_str().into();
                let true_inst: usize = pair
                    .next()
                    .map(|inst| inst.as_str().parse().unwrap())
                    .unwrap();
                let false_inst: usize = pair
                    .next()
                    .map(|inst| inst.as_str().parse().unwrap())
                    .unwrap();
                Self::IfNotZeros {
                    register,
                    true_inst: true_inst - 1,
                    false_inst: false_inst - 1,
                }
            }
            Rule::blank_line => Self::NoOp,
            unknown_expr => panic!("Unexpected statements: {unknown_expr:?}"),
        }
    }

    fn execute(&self, context: &mut Context) {
        match self {
            NormaAST::Increment {
                register,
                next_inst,
            } => {
                context.inc(register);
                match next_inst {
                    Some(inst) => context.cursor = *inst,
                    None => context.cursor += 1,
                }
            }
            NormaAST::Decrement {
                register,
                next_inst,
            } => {
                context.dec(register);
                match next_inst {
                    Some(inst) => context.cursor = *inst,
                    None => context.cursor += 1,
                }
            }
            NormaAST::IfZeros {
                register,
                true_inst,
                false_inst,
            } => {
                let next = if *context.get_register(register) == BigUint::zero() {
                    *true_inst
                } else {
                    *false_inst
                };
                context.cursor = next;
            }
            NormaAST::IfNotZeros {
                register,
                true_inst,
                false_inst,
            } => {
                let next = if *context.get_register(register) != BigUint::zero() {
                    *true_inst
                } else {
                    *false_inst
                };
                context.cursor = next;
            }
            NormaAST::NoOp => context.cursor += 1,
        }
    }
}

pub struct NORMAInterpreter;

impl Context {
    fn new() -> Self {
        Self {
            inst: 0,
            cursor: 0,
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

    #[cfg(test)]
    fn get_register_read_only(&self, register: &str) -> BigUint {
        self.registers.get(register).cloned().unwrap_or_default()
    }

    fn get_register(&mut self, register: &str) -> &mut BigUint {
        use std::collections::hash_map::Entry;
        match self.registers.entry(register.into()) {
            Entry::Occupied(occ_entry) => occ_entry.into_mut(),
            Entry::Vacant(vac_entry) => vac_entry.insert(Zero::zero()),
        }
    }

    pub fn get_inst(&self) -> usize {
        self.inst
    }

    pub fn get_cursor(&self) -> usize {
        self.cursor
    }

    pub fn get_registers(&self) -> Vec<(String, BigUint)> {
        self.registers.clone().into_iter().collect()
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {

    use num_traits::ToPrimitive;

    use crate::{error::NormaMachineError, NormaMachine, NormaProgram};

    #[test]
    fn test_basic_inc() {
        let vm = parse_and_run("inc A\ninc A");
        assert_eq!(2, vm.ctx.get_register_read_only("A").to_isize().unwrap());
    }

    #[test]
    fn test_basic_dec() {
        let vm = parse_and_run("inc A\ninc A\ndec A");
        assert_eq!(1, vm.ctx.get_register_read_only("A").to_isize().unwrap());
    }

    #[test]
    fn test_basic_ifz() {
        let vm = parse_and_run("inc A\nifz A (3,4)\ninc B\ninc C");
        assert_eq!(1, vm.ctx.get_register_read_only("A").to_isize().unwrap());
        assert_eq!(0, vm.ctx.get_register_read_only("B").to_isize().unwrap());
        assert_eq!(1, vm.ctx.get_register_read_only("C").to_isize().unwrap());
        let vm = parse_and_run("inc C\nifz A (3,4)\ninc B\ninc C");
        assert_eq!(0, vm.ctx.get_register_read_only("A").to_isize().unwrap());
        assert_eq!(1, vm.ctx.get_register_read_only("B").to_isize().unwrap());
        assert_eq!(2, vm.ctx.get_register_read_only("C").to_isize().unwrap());
    }

    #[test]
    fn test_basic_ifnz() {
        let vm = parse_and_run("inc A\nifnz A (3,4)\ninc B\ninc C");
        assert_eq!(1, vm.ctx.get_register_read_only("A").to_isize().unwrap());
        assert_eq!(1, vm.ctx.get_register_read_only("B").to_isize().unwrap());
        assert_eq!(1, vm.ctx.get_register_read_only("C").to_isize().unwrap());
        let vm = parse_and_run("inc C\nifnz A (3,4)\ninc B\ninc C");
        assert_eq!(0, vm.ctx.get_register_read_only("A").to_isize().unwrap());
        assert_eq!(0, vm.ctx.get_register_read_only("B").to_isize().unwrap());
        assert_eq!(2, vm.ctx.get_register_read_only("C").to_isize().unwrap());
    }

    #[test]
    fn test_goto_after() {
        let vm = parse_and_run("inc A (10)\ninc A");
        assert_eq!(1, vm.ctx.get_register_read_only("A").to_isize().unwrap());
    }

    #[test]
    fn test_basic_inc_with_goto() {
        let vm = parse_and_run("inc A (3)\ninc A");
        assert_eq!(1, vm.ctx.get_register_read_only("A").to_isize().unwrap());
    }

    #[test]
    fn test_basic_dec_with_goto() {
        let vm = parse_and_run("inc A \ninc A\ndec A (5)\n dec A");
        assert_eq!(1, vm.ctx.get_register_read_only("A").to_isize().unwrap());
    }

    #[test]
    fn test_basic_error() {
        let error = NormaProgram::parse("example").err().unwrap();
        match error {
            NormaMachineError::Parse(_) => {}
            _ => unreachable!(),
        };

        let error = NormaProgram::parse("").err().unwrap();
        match error {
            NormaMachineError::EmptySource => {}
            _ => unreachable!(),
        };
    }

    #[test]
    fn test_comments() {
        let vm = parse_and_run("//comment");
        assert_eq!(0, vm.ctx.get_register_read_only("a").to_isize().unwrap());
        let vm = parse_and_run("inc a//comment");
        assert_eq!(1, vm.ctx.get_register_read_only("a").to_isize().unwrap());
    }

    #[test]
    fn test_comments_line_count() {
        let vm = parse_and_run("inc a (3) \n//comment\ndec a");
        assert_eq!(0, vm.ctx.get_register_read_only("a").to_isize().unwrap());
    }

    fn parse_and_run(source: &str) -> NormaMachine {
        let prg = NormaProgram::parse(source).unwrap();
        let mut vm = NormaMachine::new(prg);
        vm.run();
        vm
    }
}
