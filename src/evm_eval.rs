use core::ops::{BitAnd};
use evm_core::eval::arithmetic as arith;
use evm_core::eval::bitwise;
use primitive_types::U256;
use rand::prelude::*;
use std::ops::*;

use egg::*;
use crate::*;
use rand_pcg::Pcg64;
use std::str::FromStr;
use std::fmt;

use z3::{SatResult, ast::Ast};

// Wrap U256 so we parse correctly
#[derive(Debug, Clone, PartialOrd, Ord, Eq, PartialEq, Hash)]
pub struct WrappedU256 {
    pub value: U256,
}

impl FromStr for WrappedU256 {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match U256::from_dec_str(s) {
            Ok(v) => Ok(WrappedU256 { value: v }),
            Err(_) => Err(()),
        }
    }
}

impl Display for WrappedU256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.value)
    }
}


define_language! {
    pub enum EVM {
        "-" = Sub([Id; 2]),
        "/" = Div([Id; 2]),
        "&" = BWAnd([Id; 2]),
        "|" = BWOr([Id; 2]),
        "<<" = ShiftLeft([Id; 2]),
        ">>" = ShiftRight([Id; 2]),
        "||" = LOr([Id; 2]),
        "&&" = LAnd([Id; 2]),

        ">" = Gt([Id; 2]),
        ">=" = Ge([Id; 2]),
        "<" = Lt([Id; 2]),
        "<=" = Le([Id; 2]),
        "==" = Eq([Id; 2]),
        "s<" = Slt([Id; 2]),
        "s<=" = Sle([Id; 2]),
        "s>" = Sgt([Id; 2]),
        "s>=" = Sge([Id; 2]),

        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),

        "!" = LNot([Id; 1]),
        "~" = BWNot([Id; 1]),

        "Havoc" = Havoc, // TODO: not the same thing!
        Num(WrappedU256),
        Var(egg::Symbol),
    }
}

fn random_256(rng: &mut Pcg64) -> U256 {
    let lower = U256::from_dec_str(&rng.gen::<u128>().to_string()).unwrap();
    let dummy_vec: [Id; 2] = [Id::from(0), Id::from(0)];
    let upper = eval_evm(&EVM::ShiftLeft(dummy_vec), Some(lower), Some(U256::from_dec_str("128").unwrap())).unwrap();
    let lower_2 = U256::from_dec_str(&rng.gen::<u128>().to_string()).unwrap();
    eval_evm(&EVM::BWOr(dummy_vec), Some(lower_2), Some(upper)).unwrap()
}

impl EVM {
    pub fn new(n: U256) -> Self {
        EVM::Num(WrappedU256 { value: n })
    }

    pub fn from_u64(n: u64) -> Self {
        EVM::Num(WrappedU256 { value : U256::from_dec_str(&n.to_string()).unwrap() })
    }
}

impl From<U256> for EVM {
    fn from(t: U256) -> Self {
        Self::new(t)
    }
}

fn z3_bool_to_256<'a>(ctx: &'a z3::Context, ast: z3::ast::Bool<'a>) -> z3::ast::BV<'a> {
    ast.ite(&z3::ast::BV::from_u64(&ctx, 1 as u64, 256), &z3::ast::BV::from_u64(&ctx, 0 as u64, 256))
}

fn z3_256_to_bool<'a>(ctx: &'a z3::Context, ast: z3::ast::BV<'a>) -> z3::ast::Bool<'a> {
    ast._eq(&z3::ast::BV::from_u64(&ctx, 0 as u64, 256))
}

fn egg_to_z3<'a>(ctx: &'a z3::Context, expr: &[EVM]) -> z3::ast::BV<'a> {
    let mut buf: Vec<z3::ast::BV> = vec![];
    for node in expr.as_ref().iter() {
        match node {
            EVM::Num(n) => buf.push(z3::ast::BV::from_int(&z3::ast::Int::from_str(ctx, &n.value.to_string()).unwrap(), 256)),
            EVM::Var(v) => buf.push(z3::ast::BV::new_const(&ctx, v.to_string(), 256)),

            EVM::Sub([a, b]) => buf.push(buf[usize::from(*a)].bvsub(&buf[usize::from(*b)])),
            EVM::Div([a, b]) => buf.push(buf[usize::from(*a)].bvudiv(&buf[usize::from(*b)])),
            EVM::BWAnd([a, b]) => buf.push(buf[usize::from(*a)].bvand(&buf[usize::from(*b)])),
            EVM::BWOr([a, b]) => buf.push(buf[usize::from(*a)].bvor(&buf[usize::from(*b)])),
            EVM::ShiftLeft([a, b]) => buf.push(buf[usize::from(*a)].bvshl(&buf[usize::from(*b)])),
            EVM::ShiftRight([a, b]) => buf.push(buf[usize::from(*a)].bvlshr(&buf[usize::from(*b)])),

            EVM::LOr([a, b]) => buf.push(z3_bool_to_256(ctx, z3_256_to_bool(ctx, buf[usize::from(*a)].clone()).bitor(z3_256_to_bool(ctx, buf[usize::from(*b)].clone())))),
            EVM::LAnd([a, b]) => buf.push(z3_bool_to_256(ctx, z3_256_to_bool(ctx, buf[usize::from(*a)].clone()).bitand(z3_256_to_bool(ctx, buf[usize::from(*b)].clone())))),

            EVM::Gt([a, b]) => buf.push(z3_bool_to_256(ctx, buf[usize::from(*a)].bvugt(&buf[usize::from(*b)]))),
            EVM::Ge([a, b]) => buf.push(z3_bool_to_256(ctx, buf[usize::from(*a)].bvuge(&buf[usize::from(*b)]))),
            EVM::Lt([a, b]) => buf.push(z3_bool_to_256(ctx, buf[usize::from(*a)].bvult(&buf[usize::from(*b)]))),
            EVM::Le([a, b]) => buf.push(z3_bool_to_256(ctx, buf[usize::from(*a)].bvule(&buf[usize::from(*b)]))),
            EVM::Eq([a, b]) => buf.push(z3_bool_to_256(ctx, buf[usize::from(*a)]._eq(&buf[usize::from(*b)]))),
            EVM::Slt([a, b]) => buf.push(z3_bool_to_256(ctx, buf[usize::from(*a)].bvslt(&buf[usize::from(*b)]))),
            EVM::Sle([a, b]) => buf.push(z3_bool_to_256(ctx, buf[usize::from(*a)].bvsle(&buf[usize::from(*b)]))),
            EVM::Sgt([a, b]) => buf.push(z3_bool_to_256(ctx, buf[usize::from(*a)].bvsgt(&buf[usize::from(*b)]))),
            EVM::Sge([a, b]) => buf.push(z3_bool_to_256(ctx, buf[usize::from(*a)].bvsge(&buf[usize::from(*b)]))),

            EVM::Add([a, b]) => buf.push(buf[usize::from(*a)].bvadd(&buf[usize::from(*b)])),
            EVM::Mul([a, b]) => buf.push(buf[usize::from(*a)].bvmul(&buf[usize::from(*b)])),

            EVM::LNot([a]) => buf.push(z3_bool_to_256(ctx, z3_256_to_bool(ctx, buf[usize::from(*a)].clone()).not())),
            EVM::BWNot([a]) => buf.push(buf[usize::from(*a)].bvnot()),

            EVM::Havoc => (),
        }
    }
    buf.pop().unwrap()
}

fn evm_smt_valid(
    lhs: &egg::Pattern<EVM>,
    rhs: &egg::Pattern<EVM>,
) -> bool {
    let mut cfg = z3::Config::new();
    cfg.set_timeout_msec(10000);
    let ctx = z3::Context::new(&cfg);
    let solver = z3::Solver::new(&ctx);
    let lexpr = egg_to_z3(&ctx, EVM::instantiate(lhs).as_ref());
    let rexpr = egg_to_z3(&ctx, EVM::instantiate(rhs).as_ref());
    solver.assert(&lexpr._eq(&rexpr).not());
    match solver.check() {
        SatResult::Unsat => true,
        SatResult::Sat => {
            false
        }
        SatResult::Unknown => {
            false
        }
    }
}

impl SynthLanguage for EVM {
    type Constant = U256;

    fn eval<'a, F>(&'a self, cvec_len: usize, mut v: F) -> CVec<Self>
    where
        F: FnMut(&'a Id) -> &'a CVec<Self>,
    {
        match self {
            EVM::Var(_) => {
                vec![]
            }
            _ => {
                let mut cvec = vec![];
                for i in 0..cvec_len {
                    let first = if self.len() > 0 {
                        if v(&self.children()[0]).len() < cvec_len {
                            break;
                        }
                        v(&self.children()[0])[i].clone()
                    } else { None };
                    let second = if self.len() > 1 {
                        if v(&self.children()[1]).len() < cvec_len {
                            break;
                        }
                        v(&self.children()[1])[i].clone()
                    } else { None };
                                        
                    cvec.push(eval_evm(self, first, second))
                }
                cvec
            }
        }
    }

    fn to_var(&self) -> Option<Symbol> {
        if let EVM::Var(sym) = self {
            Some(*sym)
        } else {
            None
        }
    }

    fn mk_var(sym: Symbol) -> Self {
        EVM::Var(sym)
    }

    fn to_constant(&self) -> Option<&Self::Constant> {
        if let EVM::Num(n) = self {
            Some(&n.value)
        } else {
            None
        }
    }

    fn mk_constant(c: Self::Constant) -> Self {
        EVM::from(c)
    }

    fn init_synth(synth: &mut Synthesizer<Self>) {
        let mut consts: Vec<Option<U256>> = vec![];
        for i in 0..synth.params.important_cvec_offsets {
            consts.push(Some(U256::zero().overflowing_add(U256::from(i)).0));
            consts.push(Some(U256::zero().overflowing_sub(U256::from(i+1)).0));
        }
        consts.sort();
        consts.dedup();

        let mut consts = self_product(&consts, synth.params.variables);
        // add the necessary random values, if any
        for row in consts.iter_mut() {
            let n_samples = synth.params.n_samples;
            let vals = std::iter::repeat_with(|| random_256(&mut synth.rng));
            row.extend(vals.take(n_samples).map(Some));
        }

        let mut egraph = EGraph::new(SynthAnalysis {
            cvec_len: consts[0].len(),
            constant_fold: if synth.params.no_constant_fold {
                ConstantFoldMethod::NoFold
            } else {
                ConstantFoldMethod::CvecMatching
            },
            rule_lifting: false,
        });

        egraph.add(EVM::from_u64(0));
        egraph.add(EVM::from(U256::zero().overflowing_sub(U256::one()).0));
        egraph.add(EVM::from(U256::one()));
        egraph.add(EVM::from(U256::one().overflowing_add(U256::one()).0));

        for i in 0..synth.params.variables {
            let var = Symbol::from(letter(i));
            let id = egraph.add(EVM::Var(var));
            egraph[id].data.cvec = consts[i].clone();
        }

        synth.egraph = egraph;
    }

    fn make_layer(synth: &Synthesizer<Self>, iter: usize) -> Vec<Self> {
        let extract = Extractor::new(&synth.egraph, NumberOfOps);

        // maps ids to n_ops
        let ids: HashMap<Id, usize> = synth
            .ids()
            .map(|id| (id, extract.find_best_cost(id)))
            .collect();

        let mut to_add = vec![];
        for i in synth.ids() {
            for j in synth.ids() {
                if ids[&i] + ids[&j] + 1 != iter {
                    continue;
                }
                to_add.push(EVM::Sub([i, j]));
                to_add.push(EVM::Div([i, j]));
                to_add.push(EVM::BWAnd([i, j]));
                to_add.push(EVM::BWOr([i, j]));
                to_add.push(EVM::ShiftLeft([i, j]));
                to_add.push(EVM::ShiftRight([i, j]));
                to_add.push(EVM::LOr([i, j]));
                to_add.push(EVM::LAnd([i, j]));
                to_add.push(EVM::Gt([i, j]));
                to_add.push(EVM::Ge([i, j]));
                to_add.push(EVM::Lt([i, j]));
                to_add.push(EVM::Le([i, j]));
                to_add.push(EVM::Eq([i, j]));
                to_add.push(EVM::Slt([i, j]));
                to_add.push(EVM::Sle([i, j]));
                to_add.push(EVM::Sgt([i, j]));
                to_add.push(EVM::Sge([i, j]));
                to_add.push(EVM::Add([i, j]));
                to_add.push(EVM::Mul([i, j]));
            }
            if ids[&i] + 1 != iter {
                continue;
            }

            to_add.push(EVM::LNot([i]));
            to_add.push(EVM::BWNot([i]));
        }

        log::info!("Made a layer of {} enodes", to_add.len());
        to_add
    }

    fn is_valid(
        synth: &mut Synthesizer<Self>,
        lhs: &egg::Pattern<Self>,
        rhs: &egg::Pattern<Self>,
    ) -> bool {

        if synth.params.use_smt {
            let res = evm_smt_valid(lhs, rhs);
            println!("verifying! {} {} {}", lhs, rhs, res);
            res
        } else {
            let n = synth.params.num_fuzz;
            let mut env = HashMap::default();

            for var in lhs.vars() {
                env.insert(var, vec![]);
            }

            for var in rhs.vars() {
                env.insert(var, vec![]);
            }

            for cvec in env.values_mut() {
                cvec.reserve(n);
                for _ in 0..n {
                    let v = random_256(&mut synth.rng);
                    cvec.push(Some(v));
                }
            }

            let lvec = Self::eval_pattern(lhs, &env, n);
            let rvec = Self::eval_pattern(rhs, &env, n);

            lvec == rvec
        }
    }
}


fn bool_to_u256(b: bool) -> U256 {
    if b {
        U256::one()
    } else {
        U256::zero()
    }   
}

fn u256_to_bool(u: U256) -> bool {
    u != U256::zero()
}

pub fn eval_evm(
    op: &EVM,
    first: Option<U256>,
    second: Option<U256>,
) -> Option<U256> {
    Some(match op {
        EVM::Var(_) => None?,
        EVM::Num(n) => n.value,
        EVM::Havoc => None?,

        EVM::Sub(_) => first?.overflowing_sub(second?).0,
        EVM::Div(_) => arith::div(first?, second?),
        EVM::BWAnd(_) => first?.bitor(second?),
        EVM::BWOr(_) => first?.bitand(second?),
        EVM::ShiftLeft(_) => bitwise::shl(first?, second?),
        EVM::ShiftRight(_) => bitwise::shr(first?, second?),

        EVM::LOr(_) => bool_to_u256(u256_to_bool(first?) || u256_to_bool(second?)),
        EVM::LAnd(_) => bool_to_u256(u256_to_bool(first?) && u256_to_bool(second?)),

        EVM::Gt(_) => bool_to_u256(first?.gt(&second?)),
        EVM::Ge(_) => bool_to_u256(first?.ge(&second?)),
        EVM::Lt(_) => bool_to_u256(first?.lt(&second?)),
        EVM::Le(_) => bool_to_u256(first?.le(&second?)),
        EVM::Eq(_) => bool_to_u256(first?.eq(&second?)),

        EVM::Slt(_) => bitwise::slt(first?, second?),
        EVM::Sle(_) => if first? == second? { bool_to_u256(true) } else {bitwise::slt(first?, second?)},
        EVM::Sgt(_) => bitwise::sgt(first?, second?),
        EVM::Sge(_) => if first? == second? { bool_to_u256(true) } else {bitwise::sgt(first?, second?)},

        EVM::Add(_) => first?.overflowing_add(second?).0,
        EVM::Mul(_) => first?.overflowing_mul(second?).0,


        EVM::LNot(_) => bool_to_u256(!u256_to_bool(first?)),
        EVM::BWNot(_) => bitwise::not(first?),
    })
}

use serde_json::{Value};

pub fn get_pregenerated_rules() -> Vec<(String, String)> {
    let contents = include_str!("../out.json");
    let json = serde_json::from_str(&contents).unwrap();
    match json {
        Value::Object(map) => {
            let eqs = map.get("all_eqs").unwrap();
            if let Value::Array(rules) = eqs {
                let mut res = vec![];

                for entry in rules {
                    if let Value::Object(rule) = entry {
                        let lhs = rule.get("lhs").unwrap();
                        let rhs = rule.get("rhs").unwrap();
                        if let Value::String(lhs) = lhs {
                            if let Value::String(rhs) = rhs {
                                if let Value::Bool(bidrectional) = rule.get("bidirectional").unwrap() {
                                    res.push((lhs.to_string(), rhs.to_string()));
                                    if *bidrectional {
                                        res.push((rhs.to_string(), lhs.to_string()));
                                    }
                                }
                                
                            }
                        }
                    } else {
                        panic!("invalid entry in rules");
                    }
                }



                


                res
            } else {
                panic!("expected array from json all_eqs");
            }
        }
        _ => panic!("invalid json"),
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_evm() {

        for (lhs, rhs) in get_pregenerated_rules() {
            let lparsed: egg::Pattern<EVM> = lhs.parse().unwrap();
            let rparsed: egg::Pattern<EVM> = rhs.parse().unwrap();
            assert!(lparsed.to_string() == lhs);
            assert!(rparsed.to_string() == rhs);
            

            if !evm_smt_valid(&lparsed, &rparsed) {
                panic!("{} != {}", lhs, rhs);
            }
        }
    }
}
