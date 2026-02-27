///|
/// Error type for generator compilation and hypothesis emission.
pub(all) suberror GenCompileError {
  GenCompileError(String)
}

///|
fn[T] fail_gen(msg : String) -> T raise GenCompileError {
  raise GenCompileError(msg)
}

///|
/// Error type for executing generated generator AST directly in MoonBit.
pub(all) suberror GenRuntimeError {
  GenRuntimeError(String)
}

///|
fn[T] fail_runtime(msg : String) -> T raise GenRuntimeError {
  raise GenRuntimeError(msg)
}
