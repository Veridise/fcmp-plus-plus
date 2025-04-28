use core::cmp::max;
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
/// Utilities for handling/printing fields
pub mod field_utils;

pub(crate) struct PicusVariableInfo {
  is_input: bool,
  name: Option<String>,
}

impl PicusVariableInfo {
  pub(crate) fn new(name: Option<&str>) -> PicusVariableInfo {
    PicusVariableInfo { is_input: false, name: name.map(|x| x.to_string()) }
  }
}

pub(crate) struct PicusContext {
  variable_info: Vec<PicusVariableInfo>,
  variable_name_to_index: HashMap<String, usize>,
}

impl PicusContext {
  fn new() -> Self {
    PicusContext { variable_info: vec![], variable_name_to_index: HashMap::new() }
  }

  /// Adds a new variable to the program context.
  fn add_variable(&mut self, name: Option<&str>) -> Result<usize, String> {
    let index = self.variable_info.len();
    self.variable_info.push(PicusVariableInfo::new(name));
    if let Some(name) = name {
      self.variable_name_to_index.insert(name.to_string(), index);
    }
    Ok(index)
  }

  /// Retrieve a variable by its name
  fn get_variable_by_name(&self, name: &str) -> Option<PicusVariable> {
    self.variable_name_to_index.get(name).cloned().map(PicusVariable)
  }

  /// Retrieves the name of a variable given its index.
  fn get_variable_name(&self, index: usize) -> Option<String> {
    self.variable_info.get(index).and_then(|variable_info| variable_info.name.clone())
  }

  fn get_num_variables(&self) -> usize {
    self.variable_info.len()
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
    PicusModule { name, statements: Vec::new(), context: PicusContext::new() }
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
    self.context.variable_info[variable.0].is_input = true;
    Ok(())
  }

  pub(crate) fn add_statement(&mut self, statement: PicusStatement<F>) {
    self.statements.push(statement);
  }

  /// Create a Picus module from several circuits
  ///
  /// The aL_i * aR_i == aO_i constraint is **removed** for the first num_unconstrained_rows-many
  /// rows. From these first num_unconstrained_rows, only referenced variables (i.e. in the input_vars
  /// or in the assumes/asserts) will be created
  pub fn from_circuits<C: Ciphersuite<F = F>>(
    name: String,
    assumes: Vec<Circuit<C>>,
    asserts: Vec<Circuit<C>>,
    num_unconstrained_rows: usize,
    input_vars: Vec<Variable>,
  ) -> Result<Self, String> {
    let mut module = PicusModule::<C::F>::new(name);

    let max_n_rows =
      assumes.iter().chain(asserts.iter()).map(|circuit| circuit.muls()).reduce(max).unwrap_or(0);
    assert!(max_n_rows >= num_unconstrained_rows, "More input rows than rows!");

    // Make picus variables for all the input variables
    for input_var in input_vars {
      let picus_var = module.circuit_var_get_or_create_picus_var(&input_var);
      module.mark_variable_as_input(picus_var)?;
    }

    // Make picus variables for all the non-input rows (we'll need these for the quadratic constraints)
    for variable_type in vec![Variable::aL, Variable::aR, Variable::aO] {
      for i in num_unconstrained_rows..max_n_rows {
        let circuit_var: Variable = variable_type(i);
        module.circuit_var_get_or_create_picus_var(&circuit_var);
      }
    }

    for assume in assumes {
      module.build_statements_from_circuit(&assume, num_unconstrained_rows, true)?;
    }
    for assertion in asserts {
      module.build_statements_from_circuit(&assertion, num_unconstrained_rows, false)?;
    }

    Ok(module)
  }

  /// Convert Circuit constraints into Picus
  ///
  /// Use Assert statements if assume=False, or Assume statements if assume is true
  ///
  /// Uses the names aL_*, aR_*, aO_* for the corresponding circuit variables, creating
  /// them if necessary
  fn build_statements_from_circuit<C>(
    &mut self,
    circuit: &Circuit<C>,
    num_input_rows: usize,
    assume: bool,
  ) -> Result<(), String>
  where
    C: Ciphersuite<F = F>,
  {
    // ensure number of input rows is sensible
    if num_input_rows > circuit.muls() {
      return Err(format!("Too many input rows: '{}' > '{}'", num_input_rows, circuit.muls()));
    }

    // Ensure we can support the lincombs
    let some_wv = circuit.constraints.iter().any(|constraint| !constraint.WV().is_empty());
    if some_wv {
      return Err("Constraint has WV != 0".to_string());
    }

    let statement_constructor =
      if assume { PicusStatement::Assume } else { PicusStatement::Assert };

    // Apply linear constraints
    //
    // Use get-or-create since we may reference variables from input rows, which have not been
    // created in the above loop.
    // This strategy ensures we only include input variables which are referenced in the constraint,
    // or which later are explicitly declared as inputs via the "mark_variable_as_input" method.
    //
    // This is a bit of a hack so that we can easily create circuits that have e.g. 1 or 2 inputs.
    // Otherwise, we create aL0, aR0, and aO0, only use aL0/aR0, and leave the accidentally created
    // aO0 as an under-constrained value
    for constraint in &circuit.constraints {
      let mut var_to_coefficient: HashMap<_, _> =
        HashMap::<PicusVariable, PicusExpression<F>>::new();
      // compute coefficient for each variable
      let ws_and_vars: [(_, fn(usize) -> Variable); 3] = [
        (constraint.WL(), Variable::aL),
        (constraint.WR(), Variable::aR),
        (constraint.WO(), Variable::aO),
      ];
      for (w, var_cnstr) in ws_and_vars {
        for (index, coefficient) in w {
          let coefficient: PicusExpression<F> = PicusTerm::Constant(*coefficient).into();
          let picus_variable = self.circuit_var_get_or_create_picus_var(&var_cnstr(*index));
          let _ = *var_to_coefficient
            .entry(picus_variable)
            .and_modify(|old_coeff| *old_coeff = old_coeff.clone() + coefficient.clone())
            .or_insert(coefficient);
        }
      }

      // Now handle WCGs
      for (outer_index, weights) in constraint.WCG().iter().enumerate() {
        for (inner_index, coefficient) in weights {
          let coefficient: PicusExpression<F> = PicusTerm::Constant(*coefficient).into();
          let circuit_var = Variable::CG{commitment: outer_index, index: *inner_index};
          let picus_variable = self.circuit_var_get_or_create_picus_var(&circuit_var);
          let _ = *var_to_coefficient
            .entry(picus_variable)
            .and_modify(|old_coeff| *old_coeff = old_coeff.clone() + coefficient.clone())
            .or_insert(coefficient);
        }
      }

      // Scale the variables by their coefficients
      let terms = (0..self.num_variables())
        .filter_map(|picus_index| {
          var_to_coefficient
            .get(&PicusVariable(picus_index))
            .map(|coeff| (PicusVariable(picus_index), coeff.clone()))
        })
        .map(|(variable, coefficient)| coefficient * variable.into())
        .collect::<Vec<PicusExpression<C::F>>>();
      // Add the variables together
      let maybe_sum = terms.into_iter().reduce(|cumulative_sum, expr| cumulative_sum + expr);
      let sum = match maybe_sum {
        Some(sum) => sum,
        None => continue,
      };

      // Constraint sum(coeff * scalar) + c == 0
      let negative_c: PicusExpression<F> = PicusTerm::Constant(constraint.c().neg()).into();
      self.statements.push(statement_constructor(sum.equals(negative_c)));
    }
    // Apply quadratic constraints
    for i in num_input_rows..circuit.muls() {
      let aL: PicusExpression<F> = self.circuit_var_to_picus_var(&Variable::aL(i)).unwrap().into();
      let aR: PicusExpression<F> = self.circuit_var_to_picus_var(&Variable::aR(i)).unwrap().into();
      let aO: PicusExpression<F> = self.circuit_var_to_picus_var(&Variable::aO(i)).unwrap().into();
      self.statements.push(statement_constructor((aL * aR).equals(aO)));
    }

    Ok(())
  }

  /// Get the Picus variable name associated to the provided circuit variable
  pub fn circuit_var_to_name(var: &Variable) -> String {
    match var {
      Variable::aL(index) => format!("aL_{}", index),
      Variable::aR(index) => format!("aR_{}", index),
      Variable::aO(index) => format!("aO_{}", index),
      Variable::CG { commitment, index} => format!("aCG_{}_{}", commitment, index),
      Variable::V(_index) => unimplemented!(),
    }
  }

  /// Get the Picus Variable associated to the circuit variable, or None if there is none
  #[must_use]
  pub fn circuit_var_to_picus_var(&self, var: &Variable) -> Option<PicusVariable> {
    let name = PicusModule::<F>::circuit_var_to_name(var);
    self.context.get_variable_by_name(&name)
  }

  /// Get or create the picus variable
  pub fn circuit_var_get_or_create_picus_var(&mut self, var: &Variable) -> PicusVariable {
    let name = PicusModule::<F>::circuit_var_to_name(var);
    match self.circuit_var_to_picus_var(var) {
      None => self.fresh_variable(Some(&name)).expect("Name existence already checked"),
      Some(var) => var,
    }
  }
}

impl<F: PrimeField> PicusProgram<F> {
  /// Create a new picus program from the provided modulus
  pub fn new(modules: Vec<PicusModule<F>>) -> Self {
    PicusProgram { modules }
  }

  /// Deconstruct this program into its vector of modules
  pub fn modules(self) -> Vec<PicusModule<F>> {
    self.modules
  }
}

#[cfg(test)]
mod tests {

  use ciphersuite::{Ciphersuite, Secp256k1};
  use generalized_bulletproofs::arithmetic_circuit_proof::{LinComb, Variable};

  use crate::{
    picus::{field_utils::PrintableBigint, PicusModule, PicusProgram},
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
    let mut circuit: Circuit<C> = Circuit::<C> { constraints: vec![], muls: 2, prover: None };
    let (l, r, o) = (Variable::aL(0), Variable::aR(0), Variable::aO(1));
    let lincomb = LinComb::empty().term(F::ONE, l).term(F::ONE, r).term(F::ONE.negate(), o);
    circuit.constrain_equal_to_zero(lincomb);

    let module: PicusModule<F> =
      PicusModule::<F>::from_circuits("main".to_string(), vec![], vec![circuit], 1, vec![l, r])?;

    let negative_one = PrintableBigint::from_field(&-F::ONE).to_string();
    let program = PicusProgram::new(vec![module]);
    let program_text = program.to_string();
    assert_eq!(
      program_text,
      format!("(prime-number 115792089237316195423570985008687907852837564279074904382605163141518161494337)
(begin-module main)
  (input aL_0)
  (input aR_0)
  (output aL_1)
  (output aO_1)
  (output aR_1)
  (assert (= (+ (+ (* 1 aL_0) (* 1 aR_0)) (* {} aO_1)) 0))
  (assert (= (* aL_1 aR_1) aO_1))
(end-module)\n", negative_one
    ));
    Ok(())
  }

  #[test]
  fn test_circuit_to_picus_inverse() -> Result<(), String> {
    let mut circuit: Circuit<C> = Circuit::<C> { constraints: vec![], muls: 1, prover: None };
    let (l, r, o) = (Variable::aL(0), Variable::aR(0), Variable::aO(0));
    let lincomb = LinComb::empty().term(F::ONE, l).term(F::ONE, r).term(F::ONE.negate(), o);
    circuit.constrain_equal_to_zero(lincomb);
    circuit.inverse(Some(l.into()), None);

    let module: PicusModule<F> =
      PicusModule::<F>::from_circuits("main".to_string(), vec![], vec![circuit], 1, vec![l, r])?;

    let program = PicusProgram::new(vec![module]);
    let negative_one = PrintableBigint::from_field(&-F::ONE).to_string();
    let program_text = program.to_string();
    assert_eq!(
      program_text,
      format!("(prime-number 115792089237316195423570985008687907852837564279074904382605163141518161494337)
(begin-module main)
  (input aL_0)
  (input aR_0)
  (output aL_1)
  (output aO_0)
  (output aO_1)
  (output aR_1)
  (assert (= (+ (+ (* 1 aL_0) (* 1 aR_0)) (* {} aO_0)) 0))
  (assert (= (+ (* 1 aL_0) (* {} aL_1)) 0))
  (assert (= (* 1 aO_1) 1))
  (assert (= (* aL_1 aR_1) aO_1))
(end-module)\n", negative_one, negative_one
    ));
    Ok(())
  }
}
