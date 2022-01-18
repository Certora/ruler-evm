use core::ops::{BitAnd};
use evm_core::eval::arithmetic as arith;
use evm_core::eval::bitwise;
use primitive_types::U256;
use rand::prelude::*;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::ops::*;

use egg::*;
use crate::*;
use std::ops::*;
use rand_pcg::Pcg64;
use rand::prelude::*;


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
        Num(U256),
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
        EVM::Num(n)
    }
}

impl From<U256> for EVM {
    fn from(t: U256) -> Self {
        Self::new(t)
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
                        v(&self.children()[0])[i].clone()
                    } else { None };
                    let second = if self.len() > 1 {
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
            Some(n)
        } else {
            None
        }
    }

    fn mk_constant(c: Self::Constant) -> Self {
        EVM::Num(c)
    }

    fn init_synth(synth: &mut Synthesizer<Self>) {
        let mut consts: Vec<Option<U256>> = vec![];
        for i in 0..synth.params.important_cvec_offsets {
            consts.push(Some(U256::zero().overflowing_add(U256::from(i)).0));
            consts.push(Some(U256::zero().overflowing_sub(U256::from((i+1))).0));
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
        });

        for i in 0..synth.params.variables {
            let var = Symbol::from(letter(i));
            let id = egraph.add(EVM::Var(var));
            egraph[id].data.cvec = consts[i].clone();
        }

        synth.egraph = egraph;
    }

    fn make_layer(synth: &Synthesizer<Self>, iter: usize) -> Vec<Self> {
        let mut extract = Extractor::new(&synth.egraph, NumberOfOps);

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
        lhs: &Pattern<Self>,
        rhs: &Pattern<Self>,
    ) -> bool {
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
        EVM::Num(n) => *n,
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
