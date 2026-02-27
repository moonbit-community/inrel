///|
/// Constructor case for `DenotationEnvBuilder`.
pub(all) struct DenCtorCase[T] {
  name : String
  build_out : (Array[DenValue[T]]) -> T?
  split : (T) -> Array[DenValue[T]]?
}

///|
/// Call case for `DenotationEnvBuilder`.
pub(all) struct DenCallCase[T] {
  name : String
  run : (Array[DenValue[T]]) -> DenValue[T]? raise GenRuntimeError
}

///|
/// Fluent builder for `DenotationEnv[T]`.
///
/// Typical flow:
/// `den_out_env_builder().with_ctor(...).with_arbitrary(...).build()`
pub(all) struct DenotationEnvBuilder[T] {
  ctor_cases : Array[DenCtorCase[T]]
  call_cases : Array[DenCallCase[T]]
  arbitrary_case : (String, @spec.TypeRef?, Int, @splitmix.RandomState) -> DenValue[
    T,
  ]? raise GenRuntimeError
  eq_out : (T, T) -> Bool
  to_output : (DenValue[T]) -> T? raise GenRuntimeError
}

///|
fn[T] den_default_arbitrary(
  _bind_name : String,
  _ty : @spec.TypeRef?,
  _size : Int,
  _rs : @splitmix.RandomState,
) -> DenValue[T]? {
  None
}

///|
fn[T] den_output_from_den_out(value : DenValue[T]) -> T? {
  match value {
    DenOut(out) => Some(out)
    _ => None
  }
}

///|
/// Builder with custom equality and output decoding.
pub fn[T] den_env_builder(
  eq_out : (T, T) -> Bool,
  to_output : (DenValue[T]) -> T? raise GenRuntimeError,
) -> DenotationEnvBuilder[T] {
  {
    ctor_cases: [],
    call_cases: [],
    arbitrary_case: (bind_name, ty, size, rs) => {
      den_default_arbitrary(bind_name, ty, size, rs)
    },
    eq_out,
    to_output,
  }
}

///|
/// Builder where outputs are expected as `DenOut(out)` and `T : Eq`.
pub fn[T : Eq] den_out_env_builder() -> DenotationEnvBuilder[T] {
  den_env_builder((lhs, rhs) => lhs == rhs, value => {
    den_output_from_den_out(value)
  })
}

///|
pub fn[T] DenotationEnvBuilder::with_ctor(
  self : DenotationEnvBuilder[T],
  name : String,
  build_out : (Array[DenValue[T]]) -> T?,
  split : (T) -> Array[DenValue[T]]?,
) -> DenotationEnvBuilder[T] {
  let next_ctor_cases = self.ctor_cases.copy()
  next_ctor_cases.push({ name, build_out, split })
  {
    ctor_cases: next_ctor_cases,
    call_cases: self.call_cases,
    arbitrary_case: self.arbitrary_case,
    eq_out: self.eq_out,
    to_output: self.to_output,
  }
}

///|
pub fn[T] DenotationEnvBuilder::with_call(
  self : DenotationEnvBuilder[T],
  name : String,
  run : (Array[DenValue[T]]) -> DenValue[T]? raise GenRuntimeError,
) -> DenotationEnvBuilder[T] {
  let next_call_cases = self.call_cases.copy()
  next_call_cases.push({ name, run })
  {
    ctor_cases: self.ctor_cases,
    call_cases: next_call_cases,
    arbitrary_case: self.arbitrary_case,
    eq_out: self.eq_out,
    to_output: self.to_output,
  }
}

///|
pub fn[T] DenotationEnvBuilder::with_arbitrary(
  self : DenotationEnvBuilder[T],
  arbitrary_case : (String, @spec.TypeRef?, Int, @splitmix.RandomState) -> DenValue[
    T,
  ]? raise GenRuntimeError,
) -> DenotationEnvBuilder[T] {
  {
    ctor_cases: self.ctor_cases,
    call_cases: self.call_cases,
    arbitrary_case,
    eq_out: self.eq_out,
    to_output: self.to_output,
  }
}

///|
pub fn[T] DenotationEnvBuilder::with_eq_out(
  self : DenotationEnvBuilder[T],
  eq_out : (T, T) -> Bool,
) -> DenotationEnvBuilder[T] {
  {
    ctor_cases: self.ctor_cases,
    call_cases: self.call_cases,
    arbitrary_case: self.arbitrary_case,
    eq_out,
    to_output: self.to_output,
  }
}

///|
pub fn[T] DenotationEnvBuilder::with_to_output(
  self : DenotationEnvBuilder[T],
  to_output : (DenValue[T]) -> T? raise GenRuntimeError,
) -> DenotationEnvBuilder[T] {
  {
    ctor_cases: self.ctor_cases,
    call_cases: self.call_cases,
    arbitrary_case: self.arbitrary_case,
    eq_out: self.eq_out,
    to_output,
  }
}

///|
fn[T] den_builder_use_ctor(
  ctor_cases : Array[DenCtorCase[T]],
  name : String,
  args : Array[DenValue[T]],
) -> DenValue[T]? {
  ctor_cases.fold(init=None, (acc, case_) => {
    guard acc is None else { acc }
    if case_.name == name {
      (case_.build_out)(args).map(out => DenOut(out))
    } else {
      None
    }
  })
}

///|
fn[T] den_builder_split_ctor(
  ctor_cases : Array[DenCtorCase[T]],
  value : DenValue[T],
  name : String,
) -> Array[DenValue[T]]? {
  guard value is DenOut(out) else { None }
  ctor_cases.fold(init=None, (acc, case_) => {
    guard acc is None else { acc }
    if case_.name == name {
      (case_.split)(out)
    } else {
      None
    }
  })
}

///|
fn[T] den_builder_call(
  call_cases : Array[DenCallCase[T]],
  name : String,
  args : Array[DenValue[T]],
) -> DenValue[T]? raise GenRuntimeError {
  call_cases.fold(init=None, (acc, case_) => {
    guard acc is None else { acc }
    if case_.name == name {
      (case_.run)(args)
    } else {
      None
    }
  })
}

///|
pub fn[T] DenotationEnvBuilder::build(
  self : DenotationEnvBuilder[T],
) -> DenotationEnv[T] {
  {
    use_ctor: (name, args) => den_builder_use_ctor(self.ctor_cases, name, args),
    split_ctor: (value, name) => {
      den_builder_split_ctor(self.ctor_cases, value, name)
    },
    call: (name, args) => den_builder_call(self.call_cases, name, args),
    arbitrary: (bind_name, ty, size, rs) => {
      (self.arbitrary_case)(bind_name, ty, size, rs)
    },
    eq: (lhs, rhs) => den_eq_with(self.eq_out, lhs, rhs),
    to_output: value => (self.to_output)(value),
  }
}
