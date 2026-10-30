///|
// Preserve the public display format from the former Show derivation.
pub impl Show for UnificationError with fn output(self, logger) {
  match self {
    UnknownIdentifier(v0) => {
      logger.write_string("UnknownIdentifier(")
      logger.write_object(v0)
      logger.write_string(")")
    }
    MissingConstraint(v0) => {
      logger.write_string("MissingConstraint(")
      logger.write_object(v0)
      logger.write_string(")")
    }
    UnificationFailure(v0) => {
      logger.write_string("UnificationFailure(")
      logger.write_object(v0)
      logger.write_string(")")
    }
  }
}

///|
// Preserve the public display format from the former Show derivation.
pub impl Show for Pattern with fn output(self, logger) {
  match self {
    PVar(v0) => {
      logger.write_string("PVar(")
      logger.write_object(v0)
      logger.write_string(")")
    }
    PCtor(v0, v1) => {
      logger.write_string("PCtor(")
      logger.write_object(v0)
      logger.write_string(", ")
      logger.write_iter(v1.iter())
      logger.write_string(")")
    }
  }
}

///|
// Preserve the public display format from the former Show derivation.
pub impl Show for Range with fn output(self, logger) {
  match self {
    Undef(v0) => {
      logger.write_string("Undef(")
      logger.write_object(v0)
      logger.write_string(")")
    }
    Fixed => logger.write_string("Fixed")
    Link(v0) => {
      logger.write_string("Link(")
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
