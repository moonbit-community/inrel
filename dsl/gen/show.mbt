///|
// Preserve the public display format from the former Show derivation.
pub impl Show for CompileOptions with fn output(self, logger) {
  logger.write_string("{aux_name: ")
  logger.write_object(self.aux_name)
  logger.write_string(", size_var: ")
  logger.write_object(self.size_var)
  logger.write_string(", succ_size_var: ")
  logger.write_object(self.succ_size_var)
  logger.write_string("}")
}
