use core::fmt;
use core::fmt::{Display, Formatter};
use core::ops::{Add, Mul, Sub};
use std::collections::{HashMap, HashSet};

use ciphersuite::group::ff::{Field, PrimeField};
use ciphersuite::Ciphersuite;
use crypto_bigint::{Encoding, NonZero, U256};
use generalized_bulletproofs::arithmetic_circuit_proof::Variable;

use crate::Circuit;

struct PicusContext {
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
    match name {
      Some(name) => {
        if self.variable_names.contains(name) {
          return Err(format!("Variable name {} already exists", name));
        }
        self.variable_names.insert(name.to_string());
        self.variable_index_to_names.insert(index, name.to_string());
      }
      _ => {}
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
#[derive(Eq, Hash, PartialEq, Clone, Copy)]
struct PicusVariable(usize);

#[derive(Clone)]
enum PicusTerm<F: PrimeField> {
  ///Hard-coded constant value.
  Constant(F),
  /// Reference to a variable in the circuit.
  Variable(PicusVariable),
}

#[derive(Clone)]
struct BinaryOperatorArgs<F: PrimeField> {
  left: Box<PicusExpression<F>>,
  right: Box<PicusExpression<F>>,
}

#[derive(Clone)]
enum PicusExpression<F: PrimeField> {
  PicusTerm(PicusTerm<F>),
  IsEqual(BinaryOperatorArgs<F>),
  Multiply(BinaryOperatorArgs<F>),
  Add(BinaryOperatorArgs<F>),
  Subtract(BinaryOperatorArgs<F>),
}

enum PicusStatement<F: PrimeField> {
  Assert(PicusExpression<F>),
  Assume(PicusExpression<F>),
}

pub struct PicusModule<F: PrimeField> {
  name: String,
  input_variables: HashSet<PicusVariable>,
  statements: Vec<PicusStatement<F>>,
  context: PicusContext,
}

pub struct PicusProgram<F: PrimeField> {
  modules: Vec<PicusModule<F>>,
}

impl<F: PrimeField> Into<PicusTerm<F>> for PicusVariable {
    fn into(self) -> PicusTerm<F> {
      PicusTerm::Variable(self)
    }
}

impl<F: PrimeField> Into<PicusExpression<F>> for PicusTerm<F> {
    fn into(self) -> PicusExpression<F> {
      PicusExpression::PicusTerm(self)
    }
}

impl<F: PrimeField> Into<PicusExpression<F>> for PicusVariable {
    fn into(self) -> PicusExpression<F> {
      let term: PicusTerm<F> = self.into();
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
  pub fn is_equal(self, rhs: Self) -> Self {
    PicusExpression::IsEqual(BinaryOperatorArgs { left: Box::new(self), right: Box::new(rhs) })
  }
}

impl<F: PrimeField> PicusModule<F> {
  pub fn new(name: String) -> Self {
    PicusModule {
      name,
      input_variables: HashSet::new(),
      statements: Vec::new(),
      context: PicusContext::new(),
    }
  }

  pub fn num_variables(&self) -> usize {
    self.context.get_num_variables()
  }

  #[must_use]
  pub fn fresh_variable(&mut self, maybe_name: Option<&str>) -> Result<PicusVariable, String> {
    self.context.add_variable(maybe_name).map(|var| PicusVariable(var))
  }

  #[must_use]
  pub fn mark_variable_as_input(&mut self, variable: PicusVariable) -> Result<(), String> {
    if variable.0 >= self.num_variables() {
      return Err(format!("Variable {} is not defined", variable.0));
    }
    self.input_variables.insert(variable);
    Ok(())
  }

  #[must_use]
  pub fn apply_constraints<C>(&mut self, circuit: &Circuit<C>) -> Result<(), String>
  where C: Ciphersuite<F = F>
  {
    // Ensure we can support the lincombs
    let some_wv = circuit.constraints.iter().any(|constraint| constraint.WV().len() > 0);
    if some_wv {
      return Err("Constraint has WV != 0".to_string());
    }
    let some_wcg = circuit.constraints.iter().any(|constraint| constraint.WCG().len() > 0);
    if some_wcg {
      return Err("Constraint has wcg != 0".to_string());
    }

    // Make sure we have enough variables
    for base_name in vec!["aL", "aR", "aO"] {
      for i in self.num_variables()..circuit.muls() {
        self.fresh_variable(Some(&format!("{}_{}", base_name, i)))?;
      }
    }

    // Apply linear constraints
    let zero: PicusExpression<F> = PicusTerm::Constant(<C::F as Field>::ZERO).into();
    for constraint in &circuit.constraints {
      let mut var_to_coefficient: HashMap<_, _> = HashMap::<PicusVariable, PicusExpression<F>>::new();
      for (index, coefficient) in constraint.WL() {
        let picus_variable = self.circuit_variable_to_picus_variable(&Variable::aL(*index), circuit).unwrap();
        let _ = *var_to_coefficient.entry(picus_variable).or_insert(zero.clone());
      }
      for (index, coefficient) in constraint.WR() {
        let picus_variable = self.circuit_variable_to_picus_variable(&Variable::aR(*index), circuit).unwrap();
        let _ = *var_to_coefficient.entry(picus_variable).or_insert(zero.clone());
      }
      for (index, coefficient) in constraint.WO() {
        let picus_variable = self.circuit_variable_to_picus_variable(&Variable::aO(*index), circuit).unwrap();
        let _ = *var_to_coefficient.entry(picus_variable).or_insert(zero.clone());
      }
      let terms = var_to_coefficient.into_iter()
          .map(|(variable, coefficient)| coefficient * variable.into())
        .collect::<Vec<PicusExpression<C::F>>>();
      let maybe_sum = terms.into_iter()
        .reduce(|cumulative_sum, expr| cumulative_sum + expr);
      let sum = match maybe_sum {
          Some(sum) => sum,
          None => continue,
      };
      self.statements.push(PicusStatement::Assert(sum.is_equal(zero.clone())));
    }
    // Apply quadratic constraints
    for i in 0..circuit.muls() {
      let aL: PicusExpression<F> = self.circuit_variable_to_picus_variable(&Variable::aL(i), circuit).unwrap().into();
      let aR: PicusExpression<F> = self.circuit_variable_to_picus_variable(&Variable::aR(i), circuit).unwrap().into();
      let aO: PicusExpression<F> = self.circuit_variable_to_picus_variable(&Variable::aO(i), circuit).unwrap().into();
      self.statements.push(
        PicusStatement::Assert((aL * aR).is_equal(aO))
      );
    }

    Ok(())
  }

  #[must_use]
  fn circuit_variable_to_picus_variable<C: Ciphersuite>(&self, var: &Variable, circuit: &Circuit<C>) -> Option<PicusVariable> {
    let picus_index = match var {
        Variable::aL(index) => Some(*index),
        Variable::aR(index) => Some(*index + circuit.muls()),
        Variable::aO(index) => Some(*index + 2 * circuit.muls()),
        Variable::CG { commitment, index } => None,
        Variable::V(_) => None,
    };
    picus_index.map(|index| PicusVariable(index))
  }
}

impl<F: PrimeField> PicusProgram<F> {
  pub fn new(modules: Vec<PicusModule<F>>) -> Self {
    PicusProgram { modules }
  }
}

trait DisplayWithContext {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result;
}

/// A generic wrapper type that pairs an object with its context.
struct WithContext<'a, 'b, T: ?Sized> {
  pub value: &'a T,
  pub context: &'b PicusContext,
}

/// Implement standard Display for the wrapper by calling the object's DisplayWithContext implementation.
impl<'a, 'b, T> Display for Box<WithContext<'a, 'b, T>>
where
  T: DisplayWithContext,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    self.value.fmt(f, self.context)
  }
}

/// Trait auto-implemented for any struct which can be displayed with a context.
pub trait WithContextExt {
  fn with<'a, 'b>(&'a self, context: &'b PicusContext) -> Box<WithContext<'a, 'b, Self>> {
    Box::new(WithContext { value: self, context })
  }
}

impl<T: DisplayWithContext> WithContextExt for T {}

impl DisplayWithContext for PicusVariable {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result {
    match context.get_variable_name(self.0) {
      Some(name) => write!(f, "{}", name),
      None => {
        if self.0 >= context.get_num_variables() {
          Err(fmt::Error)
        } else {
          write!(f, "var_{}", self.0)
        }
      }
    }
  }
}

fn bigint_to_decimal(bigint: U256) -> String {
  let mut bigint = bigint;
  let mut digits: Vec<String> = vec![];
  let ten = NonZero::new(U256::from_u8(10u8)).unwrap();
  while bigint > U256::ZERO {
    let (quotient, remainder) = bigint.div_rem(&ten);
    let remainder: u64 = remainder.as_words()[0];
    digits.push(remainder.to_string());
    bigint = quotient;
  }
  let decimal_representation = digits.into_iter().rev().collect::<Vec<String>>().join("");
  return decimal_representation;
}

impl<F: PrimeField> DisplayWithContext for PicusTerm<F> {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result {
    match self {
      PicusTerm::Constant(value) => {
        let repr = value.to_repr();
        let repr_bytes: &[u8] = repr.as_ref();
        let bigint: U256 = U256::from_le_bytes(repr_bytes.try_into().unwrap());
        let decimal_representation = bigint_to_decimal(bigint);
        write!(f, "{}", decimal_representation)
      }
      PicusTerm::Variable(variable) => write!(f, "{}", variable.with(context)),
    }
  }
}

impl<F: PrimeField> DisplayWithContext for PicusExpression<F> {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result {
    match self {
      PicusExpression::PicusTerm(term) => term.fmt(f, context),
      PicusExpression::IsEqual(args) => {
        write!(f, "(= {} {})", args.left.with(context), args.right.with(context))
      }
      PicusExpression::Multiply(args) => {
        write!(f, "(* {} {})", args.left.with(context), args.right.with(context))
      }
      PicusExpression::Add(args) => {
        write!(f, "(+ {} {})", args.left.with(context), args.right.with(context))
      }
      PicusExpression::Subtract(args) => {
        write!(f, "(- {} {})", args.left.with(context), args.right.with(context))
      }
    }
  }
}

impl<F: PrimeField> DisplayWithContext for PicusStatement<F> {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result {
    match self {
      PicusStatement::Assert(expression) => write!(f, "  (assert {})", expression.with(context))?,
      PicusStatement::Assume(expression) => write!(f, "  (assume {})", expression.with(context))?,
    }
    Ok(())
  }
}

impl<F: PrimeField> Display for PicusModule<F> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "(begin-module {})\n", self.name)?;

    // Print declarations
    for variable in &self.input_variables {
      write!(f, "  (input {})\n", variable.with(&self.context))?;
    }
    for variable_index in (0..self.num_variables())
      .filter(|&index| !self.input_variables.contains(&PicusVariable(index)))
    {
      write!(f, "  (output {})\n", PicusVariable(variable_index).with(&self.context))?;
    }

    // Print statements
    for statement in &self.statements {
      write!(f, "{}\n", statement.with(&self.context))?;
    }

    write!(f, "(end-module)")?;
    Ok(())
  }
}

impl<F: PrimeField> Display for PicusProgram<F> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    let modulus: U256 = U256::from_be_hex(F::MODULUS);
    let decimal_representation = bigint_to_decimal(modulus);
    write!(f, "(prime-number {})\n", decimal_representation)?;
    for module in &self.modules {
      write!(f, "{}\n", module)?;
    }
    Ok(())
  }
}

// pub fn compile_to_picus(circuit: &Circuit) -> String {}
//
mod tests {
  use crate::picus::{PicusProgram, PicusModule};
  use ciphersuite::{Ciphersuite, Secp256k1};

  // https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/index-seo.php?xkey=PRIMES____SECP256K1-GROUP-PRIME
  // 115792089237316195423570985008687907852837564279074904382605163141518161494337
  type F = <Secp256k1 as Ciphersuite>::F;

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
}
