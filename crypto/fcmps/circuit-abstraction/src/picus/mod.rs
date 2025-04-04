use core::ops::{Add, Mul, Sub};
use std::collections::{HashMap, HashSet};

use ciphersuite::group::ff::PrimeField;
use ciphersuite::Ciphersuite;
use generalized_bulletproofs::arithmetic_circuit_proof::Variable;

use crate::Circuit;

/// print picus programs
pub mod printer;
/// Picus program -> circom code
pub mod circom;

pub(crate) struct PicusContext {
  num_variables: usize,
  variable_names: HashSet<String>,
  variable_index_to_names: HashMap<usize, String>,
}

impl PicusContext {
  fn new() -> Self {
    PicusContext {
      num_variables: 0,
      variable_names: HashSet::new(),
      variable_index_to_names: HashMap::new(),
    }
  }

  /// Adds a new variable to the program context.
  fn add_variable(&mut self, name: Option<&str>) -> Result<usize, String> {
    let index = self.num_variables;
    if let Some(name) = name {
      if self.variable_names.contains(name) {
        return Err(format!("Variable name {} already exists", name));
      }
      self.variable_names.insert(name.to_string());
      self.variable_index_to_names.insert(index, name.to_string());
    }
    self.num_variables += 1;
    Ok(index)
  }

  /// Retrieves the name of a variable given its index.
  fn get_variable_name(&self, index: usize) -> Option<&String> {
    self.variable_index_to_names.get(&index)
  }

  fn get_num_variables(&self) -> usize {
    self.num_variables
  }
}

/// Represents a variable in the circuit with a unique index.
#[derive(Eq, Hash, PartialEq, Clone, Copy, PartialOrd, Ord)]
pub struct PicusVariable(usize);

#[derive(Clone)]
pub(crate) enum PicusTerm<F: PrimeField> {
  ///Hard-coded constant value.
  Constant(F),
  /// Reference to a variable in the circuit.
  Variable(PicusVariable),
}

#[derive(Clone)]
pub(crate) struct BinaryOperatorArgs<F: PrimeField> {
  left: Box<PicusExpression<F>>,
  right: Box<PicusExpression<F>>,
}

#[derive(Clone)]
pub(crate) enum PicusExpression<F: PrimeField> {
  PicusTerm(PicusTerm<F>),
  IsEqual(BinaryOperatorArgs<F>),
  Multiply(BinaryOperatorArgs<F>),
  Add(BinaryOperatorArgs<F>),
  Subtract(BinaryOperatorArgs<F>),
}

#[derive(Clone)]
pub(crate) enum PicusStatement<F: PrimeField> {
  Assert(PicusExpression<F>),
  Assume(PicusExpression<F>),
}

/// A modular component of constraints in a pcius program
pub struct PicusModule<F: PrimeField> {
  name: String,
  input_variables: HashSet<PicusVariable>,
  statements: Vec<PicusStatement<F>>,
  context: PicusContext,
}

/// A picus program
pub struct PicusProgram<F: PrimeField> {
  modules: Vec<PicusModule<F>>,
}

impl<F: PrimeField> From<PicusVariable> for PicusTerm<F> {
  fn from(val: PicusVariable) -> Self {
    PicusTerm::Variable(val)
  }
}

impl<F: PrimeField> From<PicusTerm<F>> for PicusExpression<F> {
  fn from(val: PicusTerm<F>) -> Self {
    PicusExpression::PicusTerm(val)
  }
}

impl<F: PrimeField> From<PicusVariable> for PicusExpression<F> {
  fn from(val: PicusVariable) -> Self {
    let term: PicusTerm<F> = val.into();
    term.into()
  }
}

impl<F: PrimeField> Mul for PicusExpression<F> {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    PicusExpression::Multiply(BinaryOperatorArgs { left: Box::new(self), right: Box::new(rhs) })
  }
}

impl<F: PrimeField> Add for PicusExpression<F> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    PicusExpression::Add(BinaryOperatorArgs { left: Box::new(self), right: Box::new(rhs) })
  }
}

impl<F: PrimeField> Sub for PicusExpression<F> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self::Output {
    PicusExpression::Subtract(BinaryOperatorArgs { left: Box::new(self), right: Box::new(rhs) })
  }
}

impl<F: PrimeField> PicusExpression<F> {
  pub fn equals(self, rhs: Self) -> Self {
    PicusExpression::IsEqual(BinaryOperatorArgs { left: Box::new(self), right: Box::new(rhs) })
  }
}

impl<F: PrimeField> PicusModule<F> {
  /// Create a new empty picus module
  pub fn new(name: String) -> Self {
    PicusModule {
      name,
      input_variables: HashSet::new(),
      statements: Vec::new(),
      context: PicusContext::new(),
    }
  }

  /// Number of variables in this picus module
  pub fn num_variables(&self) -> usize {
    self.context.get_num_variables()
  }

  /// Create a fresh variable
  ///
  /// If a name is provided, it must be unique or this method will produce an error
  pub fn fresh_variable(&mut self, maybe_name: Option<&str>) -> Result<PicusVariable, String> {
    self.context.add_variable(maybe_name).map(PicusVariable)
  }

  /// Mark the picus variable as an input variable. All other variables
  /// default to outputs
  pub fn mark_variable_as_input(&mut self, variable: PicusVariable) -> Result<(), String> {
    if variable.0 >= self.num_variables() {
      return Err(format!("Variable {} is not defined", variable.0));
    }
    self.input_variables.insert(variable);
    Ok(())
  }

  pub(crate) fn add_statement(&mut self, statement: PicusStatement<F>) {
    self.statements.push(statement);
  }

  /// Convert the Circuit constraints into a form compatible with Picus.
  /// This will fail if the picus module is not empty
  pub fn apply_constraints<C>(&mut self, circuit: &Circuit<C>) -> Result<(), String>
  where
    C: Ciphersuite<F = F>,
  {
    // Ensure we can support the lincombs
    let some_wv = circuit.constraints.iter().any(|constraint| !constraint.WV().is_empty());
    if some_wv {
      return Err("Constraint has WV != 0".to_string());
    }
    let some_wcg = circuit.constraints.iter().any(|constraint| !constraint.WCG().is_empty());
    if some_wcg {
      return Err("Constraint has wcg != 0".to_string());
    }

    // Make sure no existing variables
    if self.num_variables() > 0 {
      return Err(format!("Module already has {} > 0 variables defined", self.num_variables()));
    }

    // Make sure we have enough variables
    for (_vector_index, base_name) in vec!["aL", "aR", "aO"].into_iter().enumerate() {
      for i in 0..circuit.muls() {
        self.fresh_variable(Some(&format!("{}_{}", base_name, i)))?;
      }
    }

    // Apply linear constraints
    for constraint in &circuit.constraints {
      let mut var_to_coefficient: HashMap<_, _> =
        HashMap::<PicusVariable, PicusExpression<F>>::new();
      for (index, coefficient) in constraint.WL() {
        let coefficient: PicusExpression<F> = PicusTerm::Constant(*coefficient).into();
        let picus_variable =
          self.circuit_variable_to_picus_variable(&Variable::aL(*index), circuit).unwrap();
        let _ = *var_to_coefficient
          .entry(picus_variable)
          .and_modify(|old_coeff| *old_coeff = old_coeff.clone() + coefficient.clone())
          .or_insert(coefficient);
      }
      for (index, coefficient) in constraint.WR() {
        let coefficient: PicusExpression<F> = PicusTerm::Constant(*coefficient).into();
        let picus_variable =
          self.circuit_variable_to_picus_variable(&Variable::aR(*index), circuit).unwrap();
        let _ = *var_to_coefficient
          .entry(picus_variable)
          .and_modify(|old_coeff| *old_coeff = old_coeff.clone() + coefficient.clone())
          .or_insert(coefficient);
      }
      for (index, coefficient) in constraint.WO() {
        let coefficient: PicusExpression<F> = PicusTerm::Constant(*coefficient).into();
        let picus_variable =
          self.circuit_variable_to_picus_variable(&Variable::aO(*index), circuit).unwrap();
        let _ = *var_to_coefficient
          .entry(picus_variable)
          .and_modify(|old_coeff| *old_coeff = old_coeff.clone() + coefficient.clone())
          .or_insert(coefficient);
      }
      let terms = (0..self.num_variables())
        .filter_map(|picus_index| {
          var_to_coefficient
            .get(&PicusVariable(picus_index))
            .map(|coeff| (PicusVariable(picus_index), coeff.clone()))
        })
        .map(|(variable, coefficient)| coefficient * variable.into())
        .collect::<Vec<PicusExpression<C::F>>>();
      let maybe_sum = terms.into_iter().reduce(|cumulative_sum, expr| cumulative_sum + expr);
      let sum = match maybe_sum {
        Some(sum) => sum,
        None => continue,
      };

      let negative_c: PicusExpression<F> = PicusTerm::Constant(constraint.c().neg()).into();
      self.statements.push(PicusStatement::Assert(sum.equals(negative_c)));
    }
    // Apply quadratic constraints
    for i in 0..circuit.muls() {
      let aL: PicusExpression<F> =
        self.circuit_variable_to_picus_variable(&Variable::aL(i), circuit).unwrap().into();
      let aR: PicusExpression<F> =
        self.circuit_variable_to_picus_variable(&Variable::aR(i), circuit).unwrap().into();
      let aO: PicusExpression<F> =
        self.circuit_variable_to_picus_variable(&Variable::aO(i), circuit).unwrap().into();
      self.statements.push(PicusStatement::Assert((aL * aR).equals(aO)));
    }

    Ok(())
  }

  /// Get the Picus Variable associated to the circuit variable, or None if there is none
  #[must_use]
  pub fn circuit_variable_to_picus_variable<C: Ciphersuite>(
    &self,
    var: &Variable,
    circuit: &Circuit<C>,
  ) -> Option<PicusVariable> {
    let picus_index = match var {
      Variable::aL(index) => Some(*index),
      Variable::aR(index) => Some(*index + circuit.muls()),
      Variable::aO(index) => Some(*index + 2 * circuit.muls()),
      Variable::CG { commitment: _, index: _ } => None,
      Variable::V(_) => None,
    };
    picus_index.map(PicusVariable)
  }
}

impl<F: PrimeField> PicusProgram<F> {
  /// Create a new picus program from the provided modulus
  pub fn new(modules: Vec<PicusModule<F>>) -> Self {
    PicusProgram { modules }
  }
}

#[cfg(test)]
mod tests {

  use ciphersuite::{Ciphersuite, Secp256k1};
  use generalized_bulletproofs::arithmetic_circuit_proof::LinComb;

  use crate::{
    picus::{PicusModule, PicusProgram},
    Circuit,
  };

  // https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/index-seo.php?xkey=PRIMES____SECP256K1-GROUP-PRIME
  // 115792089237316195423570985008687907852837564279074904382605163141518161494337
  type C = Secp256k1;
  type F = <C as Ciphersuite>::F;

  #[test]
  fn test_picus_program_display() -> Result<(), String> {
    let mut module: PicusModule<F> = PicusModule::new("main".to_string());
    let var0 = module.fresh_variable(Some("var0"))?;
    let _var1 = module.fresh_variable(Some("var1"))?;
    module.mark_variable_as_input(var0)?;
    let program = PicusProgram::new(vec![module]);
    assert_eq!(
      program.to_string(),
      "(prime-number 115792089237316195423570985008687907852837564279074904382605163141518161494337)
(begin-module main)
  (input var0)
  (output var1)
(end-module)\n"
    );
    Ok(())
  }

  #[test]
  fn test_circuit_to_picus() -> Result<(), String> {
    let mut circuit: Circuit<C> = Circuit::<C> { constraints: vec![], muls: 0, prover: None };
    let (l, r, o) = circuit.mul(None, None, None);
    let lincomb = LinComb::empty().term(F::ONE, l).term(F::ONE, r).term(F::ONE.negate(), o);
    circuit.constrain_equal_to_zero(lincomb);

    let mut module: PicusModule<F> = PicusModule::new("main".to_string());
    module.apply_constraints(&circuit);
    module.mark_variable_as_input(module.circuit_variable_to_picus_variable(&l, &circuit).unwrap());
    module.mark_variable_as_input(module.circuit_variable_to_picus_variable(&r, &circuit).unwrap());

    let program = PicusProgram::new(vec![module]);
    let program_text = program.to_string();
    assert_eq!(
      program_text,
      "(prime-number 115792089237316195423570985008687907852837564279074904382605163141518161494337)
(begin-module main)
  (input aL_0)
  (input aR_0)
  (output aO_0)
  (assert (= (+ (+ (* 1 aL_0) (* 1 aR_0)) (* 115792089237316195423570985008687907852837564279074904382605163141518161494336 aO_0)) 0))
  (assert (= (* aL_0 aR_0) aO_0))
(end-module)\n"
    );
    Ok(())
  }

  #[test]
  fn test_circuit_to_picus_inverse() -> Result<(), String> {
    let mut circuit: Circuit<C> = Circuit::<C> { constraints: vec![], muls: 0, prover: None };
    let (l, r, o) = circuit.mul(None, None, None);
    let lincomb = LinComb::empty().term(F::ONE, l).term(F::ONE, r).term(F::ONE.negate(), o);
    circuit.constrain_equal_to_zero(lincomb);
    circuit.inverse(Some(l.into()), None);

    let mut module: PicusModule<F> = PicusModule::new("main".to_string());
    module.apply_constraints(&circuit);
    module.mark_variable_as_input(module.circuit_variable_to_picus_variable(&l, &circuit).unwrap());
    module.mark_variable_as_input(module.circuit_variable_to_picus_variable(&r, &circuit).unwrap());

    let program = PicusProgram::new(vec![module]);
    let program_text = program.to_string();
    assert_eq!(
      program_text,
      "(prime-number 115792089237316195423570985008687907852837564279074904382605163141518161494337)
(begin-module main)
  (input aL_0)
  (input aR_0)
  (output aL_1)
  (output aR_1)
  (output aO_0)
  (output aO_1)
  (assert (= (+ (+ (* 1 aL_0) (* 1 aR_0)) (* 115792089237316195423570985008687907852837564279074904382605163141518161494336 aO_0)) 0))
  (assert (= (+ (* 1 aL_0) (* 115792089237316195423570985008687907852837564279074904382605163141518161494336 aL_1)) 0))
  (assert (= (* 1 aO_1) 1))
  (assert (= (* aL_0 aR_0) aO_0))
  (assert (= (* aL_1 aR_1) aO_1))
(end-module)\n",
    );
    Ok(())
  }
}
