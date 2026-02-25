///|
/// Error type for generator compilation and hypothesis emission.
pub(all) suberror GenCompileError {
  GenCompileError(String)
}

///|
fn[T] fail_gen(msg : String) -> T raise GenCompileError {
  raise GenCompileError(msg)
}
