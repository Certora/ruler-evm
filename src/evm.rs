use crate::*;
use rust_evm::{EVM, eval_evm, Constant, BitVar, BoolVar, Type};
use core::ops::{BitAnd};
use primitive_types::U256;
use rand::prelude::*;
use std::ops::*;
use itertools::Either;

use rand_pcg::Pcg64;
use std::collections::{HashSet};

use std::io::Read;
use std::io::Write;
use std::process::{Command, Stdio};
use std::time::Duration;

use z3::{ast::Ast};
use wait_timeout::ChildExt;


fn random_256(rng: &mut Pcg64) -> U256 {
    let lower = U256::from_dec_str(&rng.gen::<u128>().to_string()).unwrap();
    let dummy_vec: [Id; 2] = [Id::from(0), Id::from(0)];
    let upper = eval_evm(&EVM::ShiftLeft(dummy_vec), Some(Constant::Num(lower)), Some(Constant::Num(U256::from_dec_str("128").unwrap())), None).unwrap();
    let lower_2 = U256::from_dec_str(&rng.gen::<u128>().to_string()).unwrap();
    let res = eval_evm(&EVM::BWOr(dummy_vec), Some(Constant::Num(lower_2)), Some(upper), None).unwrap();
    if let Constant::Num(n) = res {
        return n
    } else {
        panic!("Got a boolean from evaluation of BWOr which is quite a bad bug I have to say")
    }
}



fn z3_bool_to_256<'a>(ctx: &'a z3::Context, ast: z3::ast::Bool<'a>) -> z3::ast::BV<'a> {
    ast.ite(&z3::ast::BV::from_u64(&ctx, 1 as u64, 256), &z3::ast::BV::from_u64(&ctx, 0 as u64, 256))
}

fn z3_256_to_bool<'a>(ctx: &'a z3::Context, ast: z3::ast::BV<'a>) -> z3::ast::Bool<'a> {
    ast._eq(&z3::ast::BV::from_u64(&ctx, 0 as u64, 256))
}

fn egg_bv_vars(vars_set: &mut HashSet<Symbol>, expr: &[EVM]) -> String {
    let mut all = vec![];
    for node in expr.as_ref().iter() {
        match node {
            EVM::BitVar(BitVar(var)) => {
                if vars_set.insert(*var) {
                    all.push(format!("(declare-const {} (_ BitVec 256))", var))
                }
            }
            EVM::BoolVar(BoolVar(var)) => {
                if vars_set.insert(*var) {
                    all.push(format!("(declare-const {} Bool)", var))
                }
            }
            _ => (),
        }
    }
    all.join("\n")
}

fn egg_to_z3<'a>(ctx: &'a z3::Context, expr: &[EVM]) -> Either<z3::ast::BV<'a>, z3::ast::Bool<'a>> {
    let mut buf: Vec<Either<z3::ast::BV<'a>, z3::ast::Bool>> = vec![];

    let get_bv = |buf: &Vec<Either<z3::ast::BV<'a>, z3::ast::Bool<'a>>>, id: &Id| -> z3::ast::BV<'a> {
        buf[usize::from(*id)].clone().left().unwrap()
    };
    let get_bool = |buf: &Vec<Either<z3::ast::BV<'a>, z3::ast::Bool<'a>>>, id: &Id| -> z3::ast::Bool<'a> {
        buf[usize::from(*id)].clone().right().unwrap()
    };

    let add_bv = |bv: z3::ast::BV<'a>, buf: &mut Vec<Either<z3::ast::BV<'a>, z3::ast::Bool<'a>>>| {
        buf.push(Either::Left(bv));
    };
    let add_bool = |bv: z3::ast::Bool<'a>, buf: &mut Vec<Either<z3::ast::BV<'a>, z3::ast::Bool<'a>>>| {
        buf.push(Either::Right(bv));
    };

    for node in expr.as_ref().iter() {
        match node {
            EVM::Constant(c) => {
                match c {
                    Constant::Bool(b) => add_bool(z3::ast::Bool::from_bool(ctx, *b), &mut buf),
                    Constant::Num(num) => add_bv(z3::ast::BV::from_int(&z3::ast::Int::from_str(ctx, &num.to_string()).unwrap(), 256), &mut buf)
                }
            }
            EVM::BitVar(v) => add_bv(z3::ast::BV::new_const(&ctx, v.to_string(), 256), &mut buf),
            EVM::BoolVar(v) => add_bool(z3::ast::Bool::new_const(&ctx, v.to_string()), &mut buf),

            EVM::Sub([a, b]) => add_bv(get_bv(&buf, a).bvsub(&get_bv(&buf, b)), &mut buf),
            EVM::Div([a, b]) => add_bv(get_bv(&buf, a).bvudiv(&get_bv(&buf, b)), &mut buf),
            EVM::BWAnd([a, b]) => add_bv(get_bv(&buf, a).bvand(&get_bv(&buf, b)), &mut buf),
            EVM::BWOr([a, b]) => add_bv(get_bv(&buf, a).bvor(&get_bv(&buf, b)), &mut buf),
            EVM::ShiftLeft([a, b]) => add_bv(get_bv(&buf, a).bvshl(&get_bv(&buf, b)), &mut buf),
            EVM::ShiftRight([a, b]) => add_bv(get_bv(&buf, a).bvlshr(&get_bv(&buf, b)), &mut buf),

            EVM::LOr([a, b]) => add_bool( get_bool(&buf, a).clone().bitor(get_bool(&buf, b).clone()), &mut buf),
            EVM::LAnd([a, b]) => add_bool(get_bool(&buf, a).clone().bitand(get_bool(&buf, b).clone()), &mut buf),

            EVM::Gt([a, b]) => add_bool(get_bv(&buf, a).bvugt(&get_bv(&buf, b)), &mut buf),
            EVM::Ge([a, b]) => add_bool(get_bv(&buf, a).bvuge(&get_bv(&buf, b)), &mut buf),
            EVM::Lt([a, b]) => add_bool(get_bv(&buf, a).bvult(&get_bv(&buf, b)), &mut buf),
            EVM::Le([a, b]) => add_bool(get_bv(&buf, a).bvule(&get_bv(&buf, b)), &mut buf),
            EVM::BoolEq([a, b]) => add_bool(get_bool(&buf, a)._eq(&get_bool(&buf, b)), &mut buf),
            EVM::BitEq([a, b]) => add_bool(get_bv(&buf, a)._eq(&get_bv(&buf, b)), &mut buf),
            EVM::Slt([a, b]) => add_bool(get_bv(&buf, a).bvslt(&get_bv(&buf, b)), &mut buf),
            EVM::Sle([a, b]) => add_bool(get_bv(&buf, a).bvsle(&get_bv(&buf, b)), &mut buf),
            EVM::Sgt([a, b]) => add_bool(get_bv(&buf, a).bvsgt(&get_bv(&buf, b)), &mut buf),
            EVM::Sge([a, b]) => add_bool(get_bv(&buf, a).bvsge(&get_bv(&buf, b)), &mut buf),

            EVM::Add([a, b]) => add_bv(get_bv(&buf, a).bvadd(&get_bv(&buf, b)), &mut buf),
            EVM::Mul([a, b]) => add_bv(get_bv(&buf, a).bvmul(&get_bv(&buf, b)), &mut buf),

            EVM::LNot([a]) => add_bool(get_bool(&buf, a).clone().not(), &mut buf),
            EVM::BWNot([a]) => add_bv(get_bv(&buf, a).bvnot(), &mut buf),
            EVM::Exp([_, _]) => panic!("Z3 can't handle exponentiation so don't enumerate it"),

            EVM::BitIte([a, b, c]) => add_bv(get_bool(&buf, a).ite(&get_bv(&buf, b), &get_bv(&buf, c)), &mut buf),
            EVM::BoolIte([a, b, c]) => add_bool(get_bool(&buf, a).ite(&get_bool(&buf, b), &get_bool(&buf, c)), &mut buf),
        }
    }
    buf.pop().unwrap()
}

fn evm_smt_valid(
    lhs: &egg::Pattern<EVM>,
    rhs: &egg::Pattern<EVM>,
) -> ValidationResult {
    let cfg = z3::Config::new();
    let ctx = z3::Context::new(&cfg);
    let mut vars_set = Default::default();
    let vars = egg_bv_vars(&mut vars_set, EVM::instantiate(lhs).as_ref());
    let vars2 = egg_bv_vars(&mut vars_set, EVM::instantiate(rhs).as_ref());
    let lexpr = egg_to_z3(&ctx, EVM::instantiate(lhs).as_ref());
    let rexpr = egg_to_z3(&ctx, EVM::instantiate(rhs).as_ref());

    let assertion = if lexpr.is_left() {
        lexpr.left().unwrap()._eq(&rexpr.left().unwrap()).not()
    } else {
        lexpr.right().unwrap()._eq(&rexpr.right().unwrap()).not()
    };
    let query = 
        vec![vars,
            vars2,
            format!("\n(assert {})", assertion),
            "(check-sat)".to_string()].join("\n");

    let mut z3_process = Command::new("z3")
        .arg("-smt2")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let z3_in = z3_process.stdin.as_mut().unwrap();
    z3_in.write_all(query.as_bytes()).unwrap();

    let z3_timeout = Duration::from_secs(1);
    let mut timed_out = false;

    let _status_code = match z3_process.wait_timeout(z3_timeout).unwrap() {
        Some(status) => status.code(),
        None => {
            timed_out = true;
            z3_process.kill().unwrap();
            z3_process.wait().unwrap().code()
        }
    };

    let mut output = String::new();
    z3_process
        .stdout
        .unwrap()
        .read_to_string(&mut output)
        .unwrap();

    if timed_out {
        ValidationResult::Unknown
    } else if output.starts_with("unsat") {
        ValidationResult::Valid
    } else {
        ValidationResult::Invalid
    }
}

impl SynthLanguage for EVM {
    type Constant = Constant;
    type Type = Type;

    fn get_type(&self) -> Self::Type {
      self.type_of()
    }


    fn eval<'a, F>(&'a self, cvec_len: usize, mut v: F) -> CVec<Self>
    where
        F: FnMut(&'a Id) -> &'a CVec<Self>,
    {
        match self {
            EVM::BitVar(_) => {
                vec![]
            }
            EVM::BoolVar(_) => {
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
                    let third = if self.len() > 2 {
                        if v(&self.children()[2]).len() < cvec_len {
                            break;
                        }
                        v(&self.children()[2])[i].clone()
                    } else { None };
                                        
                    cvec.push(eval_evm(self, first, second, third))
                }
                cvec
            }
        }
    }

    fn to_var(&self) -> Option<Symbol> {
        match self {
            EVM::BitVar(BitVar(sym)) | EVM::BoolVar(BoolVar(sym)) => Some(*sym),
            _ => None
        }
    }

    fn mk_var(sym: Symbol) -> Self {
        if sym.as_str().starts_with("bv256") {
            EVM::BitVar(BitVar(sym))
        } else if sym.as_str().starts_with("bool") {
            EVM::BoolVar(BoolVar(sym))
        } else {
            panic!("invalid variable: {}", sym)
        }
    }

    fn is_constant(&self) -> bool {
      matches!(self, EVM::Constant(_))
    }


    fn mk_constant(c: Constant, _egraph: &mut EGraph<Self, SynthAnalysis>) -> Self {
        EVM::from(c)
    }

    fn init_synth(synth: &mut Synthesizer<Self>) {
        let mut consts: Vec<Option<Constant>> = vec![];
        for i in 0..synth.params.important_cvec_offsets {
            consts.push(Some(Constant::Num(U256::zero().overflowing_add(U256::from(i)).0)));
            consts.push(Some(Constant::Num(U256::zero().overflowing_sub(U256::from(i+1)).0)));
        }
        consts.sort();
        consts.dedup();

        let cs = self_product(&consts, synth.params.variables);
        let cvec_len = cs[0].len();

        let mut egraph: EGraph<EVM, SynthAnalysis> = EGraph::new(SynthAnalysis {
            cvec_len,
            constant_fold: ConstantFoldMethod::CvecMatching,
            rule_lifting: false,
        });

        egraph.add(EVM::from_u64(0));
        egraph.add(EVM::from(U256::zero().overflowing_sub(U256::one()).0));
        egraph.add(EVM::from(U256::one()));
        egraph.add(EVM::from(U256::one().overflowing_add(U256::one()).0));
        egraph.add(EVM::from(true));
        egraph.add(EVM::from(false));

        for (i, n_vals) in cs.iter().enumerate().take(synth.params.variables) {
            let n_id = egraph.add(EVM::BitVar(BitVar(Symbol::from("bv256".to_owned() + letter(i)))));
            egraph[n_id].data.cvec = n_vals.clone();
        }

        for i in 0..synth.params.variables {
            let b_id = egraph.add(EVM::BoolVar(BoolVar(Symbol::from("bool".to_owned() + letter(i)))));
            let mut b_vals = vec![];
            for _ in 0..cvec_len {
                b_vals.push(Some(Constant::Bool(synth.rng.gen::<bool>())));
            }
            egraph[b_id].data.cvec = b_vals.clone();
        }

        synth.egraph = egraph;
    }

    fn make_layer(synth: &Synthesizer<Self>, iter: usize) -> Vec<Self> {
        let extract = Extractor::new(&synth.egraph, NumberOfOps);

        let ids: HashMap<Id, usize> = synth
                    .ids()
                    .map(|id| (id, extract.find_best_cost(id)))
                    .collect();

        let mut to_add = vec![];
        for i in synth.ids() {
            // Only enumerate bitwise operations after iter 2
            if ids[&i] >= iter || (synth.egraph[i].data.class_type == Type::Bool && iter > 2) {
                continue;
            }
            for j in synth.ids() {
                if ids[&i] + ids[&j] >= iter || (synth.egraph[j].data.class_type == Type::Bool && iter > 2) {
                    continue;
                }
                for k in synth.ids() {
                    if ids[&i] + ids[&j] + ids[&k] >= iter {
                        continue;
                    }
                    if synth.egraph[i].data.class_type == Type::Bool &&
                        synth.egraph[j].data.class_type == Type::Bit256 &&
                        synth.egraph[k].data.class_type == Type::Bit256 {
                        to_add.push(EVM::BitIte([i, j, k]))
                    }

                    if synth.egraph[i].data.class_type == Type::Bool &&
                        synth.egraph[j].data.class_type == Type::Bool &&
                        synth.egraph[k].data.class_type == Type::Bool {
                        to_add.push(EVM::BoolIte([i, j, k]))
                    }
                }

                if synth.egraph[i].data.class_type == synth.egraph[j].data.class_type {
                    if synth.egraph[i].data.class_type == Type::Bit256 {
                        to_add.push(EVM::Sub([i, j]));
                        to_add.push(EVM::Div([i, j]));
                        to_add.push(EVM::BWAnd([i, j]));
                        to_add.push(EVM::BWOr([i, j]));
                        to_add.push(EVM::ShiftLeft([i, j]));
                        to_add.push(EVM::ShiftRight([i, j]));
                        to_add.push(EVM::Gt([i, j]));
                        to_add.push(EVM::Ge([i, j]));
                        to_add.push(EVM::Lt([i, j]));
                        to_add.push(EVM::Le([i, j]));
                        to_add.push(EVM::BitEq([i, j]));
                        to_add.push(EVM::Slt([i, j]));
                        to_add.push(EVM::Sle([i, j]));
                        to_add.push(EVM::Sgt([i, j]));
                        to_add.push(EVM::Sge([i, j]));
                        to_add.push(EVM::Add([i, j]));
                        to_add.push(EVM::Mul([i, j]));
                    }
    
                    if synth.egraph[i].data.class_type == Type::Bool {
                        to_add.push(EVM::LOr([i, j]));
                        to_add.push(EVM::LAnd([i, j]));
                        to_add.push(EVM::BoolEq([i, j]));
                    }
                }
            }

            if synth.egraph[i].data.class_type == Type::Bool {
                to_add.push(EVM::LNot([i]));
            }
            if synth.egraph[i].data.class_type == Type::Bit256 {
                to_add.push(EVM::BWNot([i]));
            }
        }

        log::info!("Made a layer of {} enodes", to_add.len());
        to_add
    }

    fn validate(
        synth: &mut Synthesizer<Self>,
        lhs: &egg::Pattern<Self>,
        rhs: &egg::Pattern<Self>,
    ) -> ValidationResult {
        if synth.params.use_smt {
            evm_smt_valid(lhs, rhs)
        } else {
            let n = synth.params.num_fuzz;
            let mut env = HashMap::default();

            for var in lhs.vars() {
                env.insert(var, vec![]);
            }

            for var in rhs.vars() {
                env.insert(var, vec![]);
            }

            let mut rng = Pcg64::new(0, 0);
            for cvec in env.values_mut() {
                cvec.reserve(n);
                for _ in 0..n {
                    let v = random_256(&mut rng);
                    cvec.push(Some(Constant::Num(v)));
                }
            }

            let lvec = Self::eval_pattern(lhs, &env, n);
            let rvec = Self::eval_pattern(rhs, &env, n);

            ValidationResult::from(lvec == rvec)
        }
    }
}
