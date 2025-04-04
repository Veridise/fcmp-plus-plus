use core::fmt::{self, Display, Formatter};

use ciphersuite::group::ff::PrimeField;
use crypto_bigint::{NonZero, U256, Encoding};

use super::{
  PicusContext, PicusExpression, PicusModule, PicusProgram, PicusStatement, PicusTerm,
  PicusVariable,
};

trait DisplayWithContext {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result;
}

/// A generic wrapper type that pairs an object with its context.
pub(crate) struct WithContext<'a, 'b, T: ?Sized> {
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
/// This allows us to use the write!() macro by just appending .with(&context)
pub(crate) trait WithContextExt {
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
  if bigint.eq(&U256::ZERO) {
    return "0".to_string();
  }
  let mut bigint = bigint;
  let mut digits: Vec<String> = vec![];
  let ten = NonZero::new(U256::from_u8(10u8)).unwrap();
  while bigint > U256::ZERO {
    let (quotient, remainder) = bigint.div_rem(&ten);
    let remainder: u64 = remainder.as_words()[0];
    digits.push(remainder.to_string());
    bigint = quotient;
  }

  let digits = digits.into_iter().rev().collect::<Vec<String>>();
  digits.join("")
}

impl<F: PrimeField> DisplayWithContext for PicusTerm<F> {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result {
    match self {
      PicusTerm::Constant(value) => {
        let repr = value.to_repr();
        let repr_bytes: &[u8] = repr.as_ref();
        // TODO: depending on the field implementation, repr may be little-endian.
        let bigint: U256 = U256::from_be_bytes(repr_bytes.try_into().unwrap());
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
    writeln!(f, "(begin-module {})", self.name)?;

    // Print declarations
    let mut sorted_inputs = self.input_variables.iter().cloned().collect::<Vec<_>>();
    sorted_inputs.sort();
    for variable in sorted_inputs {
      writeln!(f, "  (input {})", variable.with(&self.context))?;
    }
    for variable_index in (0..self.num_variables())
      .filter(|&index| !self.input_variables.contains(&PicusVariable(index)))
    {
      writeln!(f, "  (output {})", PicusVariable(variable_index).with(&self.context))?;
    }

    // Print statements
    for statement in &self.statements {
      writeln!(f, "{}", statement.with(&self.context))?;
    }

    write!(f, "(end-module)")?;
    Ok(())
  }
}

impl<F: PrimeField> Display for PicusProgram<F> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    let modulus: U256 = U256::from_be_hex(F::MODULUS);
    let decimal_representation = bigint_to_decimal(modulus);
    writeln!(f, "(prime-number {})", decimal_representation)?;
    for module in &self.modules {
      writeln!(f, "{}", module)?;
    }
    Ok(())
  }
}
