///|
// Preserve the public display format from the former Show derivation.
pub impl Show for TypeRef with fn output(self, logger) {
  match self {
    Named(v0) => {
      logger.write_string("Named(")
      logger.write_object(v0)
      logger.write_string(")")
    }
    App(v0, v1) => {
      logger.write_string("App(")
      logger.write_object(v0)
      logger.write_string(", ")
      logger.write_iter(v1.iter())
      logger.write_string(")")
    }
  }
}

///|
// Preserve the public display format from the former Show derivation.
pub impl Show for Term with fn output(self, logger) {
  match self {
    Var(v0) => {
      logger.write_string("Var(")
      logger.write_object(v0)
      logger.write_string(")")
    }
    Ctor(v0, v1) => {
      logger.write_string("Ctor(")
      logger.write_object(v0)
      logger.write_string(", ")
      logger.write_iter(v1.iter())
      logger.write_string(")")
    }
  }
}

///|
// Preserve the public display format from the former Show derivation.
pub impl Show for ParamMode with fn output(self, logger) {
  match self {
    In => logger.write_string("In")
    Out => logger.write_string("Out")
  }
}

///|
// Preserve the public display format from the former Show derivation.
pub impl Show for ParamSpec with fn output(self, logger) {
  logger.write_string("{name: ")
  logger.write_object(self.name)
  logger.write_string(", ty: ")
  logger.write_object(self.ty)
  logger.write_string(", mode: ")
  logger.write_object(self.mode)
  logger.write_string("}")
}

///|
// Preserve the public display format from the former Show derivation.
pub impl Show for BinderSpec with fn output(self, logger) {
  logger.write_string("{name: ")
  logger.write_object(self.name)
  logger.write_string(", ty: ")
  logger.write_object(self.ty)
  logger.write_string("}")
}

///|
// Preserve the public display format from the former Show derivation.
pub impl Show for HypothesisSpec with fn output(self, logger) {
  match self {
    RelCall(v0, v1) => {
      logger.write_string("RelCall(")
      logger.write_object(v0)
      logger.write_string(", ")
      logger.write_iter(v1.iter())
      logger.write_string(")")
    }
    Predicate(v0, v1) => {
      logger.write_string("Predicate(")
      logger.write_object(v0)
      logger.write_string(", ")
      logger.write_iter(v1.iter())
      logger.write_string(")")
    }
  }
}

///|
// Preserve the public display format from the former Show derivation.
pub impl Show for ConstructorSpec with fn output(self, logger) {
  logger.write_string("{name: ")
  logger.write_object(self.name)
  logger.write_string(", binders: ")
  logger.write_iter(self.binders.iter())
  logger.write_string(", hypotheses: ")
  logger.write_iter(self.hypotheses.iter())
  logger.write_string(", conclusion: ")
  logger.write_iter(self.conclusion.iter())
  logger.write_string(", weight: ")
  logger.write_object(self.weight)
  logger.write_string("}")
}

///|
// Preserve the public display format from the former Show derivation.
pub impl Show for VarRef with fn output(self, logger) {
  logger.write_string("{name: ")
  logger.write_object(self.name)
  logger.write_string("}")
}

///|
// Preserve the public display format from the former Show derivation.
pub impl Show for ConstructorBody with fn output(self, logger) {
  logger.write_string("{hypotheses: ")
  logger.write_iter(self.hypotheses.iter())
  logger.write_string(", conclusion: ")
  logger.write_iter(self.conclusion.iter())
  logger.write_string("}")
}

///|
// Preserve the public display format from the former Show derivation.
pub impl Show for Scope with fn output(self, logger) {
  logger.write_string("{vars: ")
  logger.write_iter(self.vars.iter())
  logger.write_string("}")
}
