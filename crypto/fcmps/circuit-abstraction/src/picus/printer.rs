use core::fmt::{self, Display, Formatter};

use ciphersuite::group::ff::PrimeField;

use crate::picus::field_utils::PrintableBigint;

use super::{
  field_utils::fmt_modulus, PicusContext, PicusExpression, PicusModule, PicusProgram,
  PicusStatement, PicusTerm, PicusVariable,
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

impl<F: PrimeField> DisplayWithContext for PicusTerm<F> {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result {
    match self {
      PicusTerm::Constant(value) => {
        let decimal_representation = PrintableBigint::from_field(value).to_string();
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
    let mut sorted_vars = self.context.variable_info.iter().enumerate().collect::<Vec<_>>();
    sorted_vars.sort_by(|(var_index1, var_info1), (var_index2, var_info2)| {
      (!var_info1.is_input, &var_info1.name).cmp(&(!var_info2.is_input, &var_info2.name))
    });
    for (var_index, var_info) in sorted_vars {
      let modifier = if var_info.is_input { "input" } else { "output" };
      writeln!(f, "  ({} {})", modifier, PicusVariable(var_index).with(&self.context))?;
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
    let decimal_representation = fmt_modulus(F::MODULUS);
    writeln!(f, "(prime-number {})", decimal_representation)?;
    for module in &self.modules {
      writeln!(f, "{}", module)?;
    }
    Ok(())
  }
}
