///|
/// Denotational value domain for typed generator evaluation.
pub(all) enum DenValue[T] {
  DenInt(Int32)
  DenBool(Bool)
  DenString(String)
  DenOut(T)
  DenCtor(String, Array[DenValue[T]])
  DenTuple(Array[DenValue[T]])
}

///|
/// Higher-order semantic environment for evaluating `GenNode` directly.
///
/// The environment tells the evaluator how to:
/// - build/match user constructors (e.g. `Tree` constructors),
/// - evaluate user calls/predicates,
/// - sample non-builtin values,
/// - compare values and extract typed outputs.
pub(all) struct DenotationEnv[T] {
  use_ctor : (String, Array[DenValue[T]]) -> DenValue[T]? raise GenRuntimeError
  split_ctor : (DenValue[T], String) -> Array[DenValue[T]]? raise GenRuntimeError
  call : (String, Array[DenValue[T]]) -> DenValue[T]? raise GenRuntimeError
  arbitrary : (String, @spec.TypeRef?, Int32, @splitmix.RandomState) -> DenValue[
    T,
  ]? raise GenRuntimeError
  eq : (DenValue[T], DenValue[T]) -> Bool raise GenRuntimeError
  to_output : (DenValue[T]) -> T? raise GenRuntimeError
}

///|
fn[A, B] map_option(values : Array[A], f : (A) -> B?) -> Array[B]? {
  values.fold(init=Some([]), (acc, value) => {
    guard acc is Some(out) else { None }
    guard f(value) is Some(mapped) else { None }
    out.push(mapped)
    Some(out)
  })
}

///|
fn[T] runtime_to_den(value : RuntimeValue) -> DenValue[T] {
  match value {
    RuntimeInt(x) => DenInt(x)
    RuntimeBool(x) => DenBool(x)
    RuntimeString(x) => DenString(x)
    RuntimeCtor(name, args) =>
      DenCtor(name, args.map(arg => runtime_to_den(arg)))
    RuntimeTuple(values) => DenTuple(values.map(value => runtime_to_den(value)))
  }
}

///|
fn[T] den_to_runtime(
  value : DenValue[T],
  out_to_runtime : (T) -> RuntimeValue?,
) -> RuntimeValue? {
  match value {
    DenInt(x) => Some(RuntimeInt(x))
    DenBool(x) => Some(RuntimeBool(x))
    DenString(x) => Some(RuntimeString(x))
    DenOut(out) => out_to_runtime(out)
    DenCtor(name, args) => {
      guard map_option(args, arg => den_to_runtime(arg, out_to_runtime))
        is Some(runtime_args) else {
        None
      }
      Some(RuntimeCtor(name, runtime_args))
    }
    DenTuple(values) => {
      guard map_option(values, value => den_to_runtime(value, out_to_runtime))
        is Some(runtime_values) else {
        None
      }
      Some(RuntimeTuple(runtime_values))
    }
  }
}

///|
fn[T] den_array_eq_with(
  eq_out : (T, T) -> Bool,
  lhs : Array[DenValue[T]],
  rhs : Array[DenValue[T]],
) -> Bool {
  if lhs.length() != rhs.length() {
    false
  } else {
    let mut ok = true
    for i in 0..<lhs.length() {
      if !den_eq_with(eq_out, lhs[i], rhs[i]) {
        ok = false
        break
      }
    }
    ok
  }
}

///|
fn[T] den_eq_with(
  eq_out : (T, T) -> Bool,
  lhs : DenValue[T],
  rhs : DenValue[T],
) -> Bool {
  match (lhs, rhs) {
    (DenInt(lv), DenInt(rv)) => lv == rv
    (DenBool(lv), DenBool(rv)) => lv == rv
    (DenString(lv), DenString(rv)) => lv == rv
    (DenOut(lv), DenOut(rv)) => eq_out(lv, rv)
    (DenCtor(ln, la), DenCtor(rn, ra)) =>
      ln == rn && den_array_eq_with(eq_out, la, ra)
    (DenTuple(la), DenTuple(ra)) => den_array_eq_with(eq_out, la, ra)
    _ => false
  }
}

///|
fn den_runtime_identity(value : RuntimeValue) -> RuntimeValue? {
  Some(value)
}

///|
fn den_split_runtime_ctor(
  value : DenValue[RuntimeValue],
  name : String,
) -> Array[DenValue[RuntimeValue]]? {
  match (value, name) {
    (DenInt(0), "O") => Some([])
    (DenInt(n), "S") if n > 0 => Some([DenInt(n - 1)])
    (DenCtor(value_name, args), name) =>
      if value_name == name {
        Some(args)
      } else {
        None
      }
    (value, name) => {
      guard den_to_runtime(value, den_runtime_identity) is Some(runtime_value) else {
        None
      }
      match (runtime_value, name) {
        (RuntimeInt(0), "O") => Some([])
        (RuntimeInt(n), "S") => if n > 0 { Some([DenInt(n - 1)]) } else { None }
        (RuntimeCtor(value_name, args), name) =>
          if value_name == name {
            Some(args.map(arg => runtime_to_den(arg)))
          } else {
            None
          }
        _ => None
      }
    }
  }
}

///|
/// Default denotational environment over `RuntimeValue`.
///
/// This is useful as a bridge when users want denotational evaluation first,
/// then decode externally.
pub fn runtime_denotation_env() -> DenotationEnv[RuntimeValue] {
  {
    use_ctor: (name, args) => {
      guard map_option(args, arg => den_to_runtime(arg, den_runtime_identity))
        is Some(runtime_args) else {
        None
      }
      Some(runtime_to_den(apply_ctor(name, runtime_args)))
    },
    split_ctor: (value, name) => den_split_runtime_ctor(value, name),
    call: (_name, _args) => None,
    arbitrary: (_bind_name, ty, size, rs) => {
      Some(runtime_to_den(default_sample_for_type(ty, size, rs)))
    },
    eq: (lhs, rhs) => den_eq_with((x, y) => x == y, lhs, rhs),
    to_output: value => den_to_runtime(value, den_runtime_identity),
  }
}

///|
/// Denotational generator (`Gen[T]`) evaluated from `GenNode`.
pub(all) struct Gen[T] {
  generator : MoonBitGenerator
  env : DenotationEnv[T]
}

///|
/// Evaluate a compiled generator AST to a typed denotational generator.
pub fn[T] MoonBitGenerator::eval(
  self : MoonBitGenerator,
  env : DenotationEnv[T],
) -> Gen[T] {
  { generator: self, env, }
}

///|
/// Compile relation and immediately obtain denotational generator.
pub fn[T] compile_relation_to_gen(
  rel : @spec.RelationSpec,
  env : DenotationEnv[T],
  options~ : CompileOptions = default_compile_options(),
) -> Gen[T] raise {
  compile_relation_to_moonbit_generator(rel, options~).eval(env)
}

///|
fn[T] den_nat_to_int(value : DenValue[T]) -> Int32? {
  match value {
    DenInt(x) => Some(x)
    DenCtor("O", []) => Some(0)
    DenCtor("S", [pred]) => den_nat_to_int(pred).map(x => x + 1)
    _ => None
  }
}

///|
fn[T] den_expect_int(
  value : DenValue[T],
  context : String,
) -> Int32 raise GenRuntimeError {
  guard den_nat_to_int(value) is Some(x) else {
    fail_runtime("Expected Int/Nat in \{context}")
  }
  x
}

///|
fn[T] den_expect_bool(
  value : DenValue[T],
  context : String,
) -> Bool raise GenRuntimeError {
  guard value is DenBool(x) else { fail_runtime("Expected Bool in \{context}") }
  x
}

///|
fn[T] den_builtin_ctor(
  name : String,
  args : Array[DenValue[T]],
) -> DenValue[T]? {
  match (name, args) {
    ("O", []) => Some(DenInt(0))
    ("S", [pred]) => den_nat_to_int(pred).map(x => DenInt(x + 1))
    _ => None
  }
}

///|
fn[T] den_builtin_arbitrary(
  ty : @spec.TypeRef?,
  size : Int32,
  rs : @splitmix.RandomState,
) -> DenValue[T]? {
  match ty {
    Some(@spec.Named("Nat"))
    | Some(@spec.Named("Int"))
    | Some(@spec.Named("Atom")) => {
      let x : Int32 = @quickcheck.Arbitrary::arbitrary(size, rs)
      Some(DenInt(x))
    }
    Some(@spec.Named("Bool")) => {
      let x : Bool = @quickcheck.Arbitrary::arbitrary(size, rs)
      Some(DenBool(x))
    }
    Some(@spec.Named("String")) => {
      let x : String = @quickcheck.Arbitrary::arbitrary(size, rs)
      Some(DenString(x))
    }
    _ => None
  }
}

///|
fn[T] den_builtin_call(
  eq : (DenValue[T], DenValue[T]) -> Bool raise GenRuntimeError,
  name : String,
  args : Array[DenValue[T]],
) -> DenValue[T]? raise GenRuntimeError {
  match name {
    "=" | "==" => {
      guard args.length() == 2 else {
        fail_runtime("`\{name}` expects 2 arguments, got \{args.length()}")
      }
      Some(DenBool(eq(args[0], args[1])))
    }
    "!=" => {
      guard args.length() == 2 else {
        fail_runtime("`!=` expects 2 arguments, got \{args.length()}")
      }
      Some(DenBool(!eq(args[0], args[1])))
    }
    "<" => {
      guard args.length() == 2 else {
        fail_runtime("`<` expects 2 arguments, got \{args.length()}")
      }
      let lhs = den_expect_int(args[0], "builtin `<` lhs")
      let rhs = den_expect_int(args[1], "builtin `<` rhs")
      Some(DenBool(lhs < rhs))
    }
    "<=" => {
      guard args.length() == 2 else {
        fail_runtime("`<=` expects 2 arguments, got \{args.length()}")
      }
      let lhs = den_expect_int(args[0], "builtin `<=` lhs")
      let rhs = den_expect_int(args[1], "builtin `<=` rhs")
      Some(DenBool(lhs <= rhs))
    }
    ">" => {
      guard args.length() == 2 else {
        fail_runtime("`>` expects 2 arguments, got \{args.length()}")
      }
      let lhs = den_expect_int(args[0], "builtin `>` lhs")
      let rhs = den_expect_int(args[1], "builtin `>` rhs")
      Some(DenBool(lhs > rhs))
    }
    ">=" => {
      guard args.length() == 2 else {
        fail_runtime("`>=` expects 2 arguments, got \{args.length()}")
      }
      let lhs = den_expect_int(args[0], "builtin `>=` lhs")
      let rhs = den_expect_int(args[1], "builtin `>=` rhs")
      Some(DenBool(lhs >= rhs))
    }
    "&&" => {
      guard args.length() == 2 else {
        fail_runtime("`&&` expects 2 arguments, got \{args.length()}")
      }
      let lhs = den_expect_bool(args[0], "builtin `&&` lhs")
      let rhs = den_expect_bool(args[1], "builtin `&&` rhs")
      Some(DenBool(lhs && rhs))
    }
    "||" => {
      guard args.length() == 2 else {
        fail_runtime("`||` expects 2 arguments, got \{args.length()}")
      }
      let lhs = den_expect_bool(args[0], "builtin `||` lhs")
      let rhs = den_expect_bool(args[1], "builtin `||` rhs")
      Some(DenBool(lhs || rhs))
    }
    "+" => {
      guard args.length() == 2 else {
        fail_runtime("`+` expects 2 arguments, got \{args.length()}")
      }
      let lhs = den_expect_int(args[0], "builtin `+` lhs")
      let rhs = den_expect_int(args[1], "builtin `+` rhs")
      Some(DenInt(lhs + rhs))
    }
    "-" => {
      guard args.length() == 2 else {
        fail_runtime("`-` expects 2 arguments, got \{args.length()}")
      }
      let lhs = den_expect_int(args[0], "builtin `-` lhs")
      let rhs = den_expect_int(args[1], "builtin `-` rhs")
      Some(DenInt(lhs - rhs))
    }
    "*" => {
      guard args.length() == 2 else {
        fail_runtime("`*` expects 2 arguments, got \{args.length()}")
      }
      let lhs = den_expect_int(args[0], "builtin `*` lhs")
      let rhs = den_expect_int(args[1], "builtin `*` rhs")
      Some(DenInt(lhs * rhs))
    }
    "/" => {
      guard args.length() == 2 else {
        fail_runtime("`/` expects 2 arguments, got \{args.length()}")
      }
      let lhs = den_expect_int(args[0], "builtin `/` lhs")
      let rhs = den_expect_int(args[1], "builtin `/` rhs")
      guard rhs != 0 else { fail_runtime("Division by zero in builtin `/`") }
      Some(DenInt(lhs / rhs))
    }
    _ => None
  }
}

///|
fn[T] den_bind_pattern_args(
  env : DenotationEnv[T],
  env_values : @ihashmap.HashMap[String, DenValue[T]],
  patterns : Array[PatternAst],
  values : Array[DenValue[T]],
  idx : Int32,
) -> @ihashmap.HashMap[String, DenValue[T]]? raise GenRuntimeError {
  if idx >= patterns.length() {
    Some(env_values)
  } else {
    guard den_bind_pattern(env, env_values, patterns[idx], values[idx])
      is Some(next) else {
      None
    }
    den_bind_pattern_args(env, next, patterns, values, idx + 1)
  }
}

///|
fn[T] den_bind_pattern(
  env : DenotationEnv[T],
  env_values : @ihashmap.HashMap[String, DenValue[T]],
  pattern : PatternAst,
  value : DenValue[T],
) -> @ihashmap.HashMap[String, DenValue[T]]? raise GenRuntimeError {
  match (pattern, value) {
    (PVar(name), value) =>
      match env_values.get(name) {
        Some(bound) =>
          if (env.eq)(bound, value) {
            Some(env_values)
          } else {
            None
          }
        None => Some(env_values.add(name, value))
      }
    (PCtor("O", []), DenInt(0)) => Some(env_values)
    (PCtor("S", [pred]), DenInt(n)) =>
      if n > 0 {
        den_bind_pattern(env, env_values, pred, DenInt(n - 1))
      } else {
        None
      }
    (PCtor(name, patterns), DenCtor(value_name, values)) =>
      if name == value_name && patterns.length() == values.length() {
        den_bind_pattern_args(env, env_values, patterns, values, 0)
      } else {
        None
      }
    (PCtor(name, patterns), value) => {
      guard (env.split_ctor)(value, name) is Some(values) else { None }
      guard patterns.length() == values.length() else {
        fail_runtime(
          "split_ctor arity mismatch for \{name}: expected \{patterns.length()}, got \{values.length()}",
        )
      }
      den_bind_pattern_args(env, env_values, patterns, values, 0)
    }
  }
}

///|
priv struct DenotationExec[T] {
  generator : MoonBitGenerator
  env : DenotationEnv[T]
  rs : @splitmix.RandomState
}

///|
fn[T] DenotationExec::sample_value(
  self : DenotationExec[T],
  bind_name : String,
  size : Int32,
) -> DenValue[T]? raise GenRuntimeError {
  let ty = self.generator.var_types.get(bind_name)
  match den_builtin_arbitrary(ty, size, self.rs) {
    Some(value) => Some(value)
    None => (self.env.arbitrary)(bind_name, ty, size, self.rs)
  }
}

///|
fn[T] DenotationExec::eval_expr(
  self : DenotationExec[T],
  env_values : @ihashmap.HashMap[String, DenValue[T]],
  expr : ExprAst,
  size : Int32,
) -> DenValue[T] raise GenRuntimeError {
  match expr {
    Var(name) => {
      guard env_values.get(name) is Some(value) else {
        fail_runtime("Unbound variable in denotational eval: \{name}")
      }
      value
    }
    Ctor(name, args) => {
      let values = args.map(arg => self.eval_expr(env_values, arg, size))
      match den_builtin_ctor(name, values) {
        Some(value) => value
        None =>
          match (self.env.use_ctor)(name, values) {
            Some(value) => value
            None => DenCtor(name, values)
          }
      }
    }
    Call(name, args) => {
      let values = args.map(arg => self.eval_expr(env_values, arg, size))
      match den_builtin_call(self.env.eq, name, values) {
        Some(value) => value
        None =>
          match (self.env.call)(name, values) {
            Some(value) => value
            None =>
              fail_runtime(
                "Unknown call/predicate in denotational eval: \{name}",
              )
          }
      }
    }
  }
}

///|
fn[T] DenotationExec::eval_guard(
  self : DenotationExec[T],
  env_values : @ihashmap.HashMap[String, DenValue[T]],
  guard_ast : GuardAst,
  size : Int32,
) -> Bool raise GenRuntimeError {
  match guard_ast {
    Eq(lhs, rhs) =>
      (self.env.eq)(
        self.eval_expr(env_values, lhs, size),
        self.eval_expr(env_values, rhs, size),
      )
    Decidable(expr) =>
      den_expect_bool(
        self.eval_expr(env_values, expr, size),
        "decidable guard in denotational eval",
      )
  }
}

///|
fn[T] DenotationExec::run_aux(
  self : DenotationExec[T],
  size : Int32,
  inputs : Array[DenValue[T]],
) -> Array[DenValue[T]]? raise GenRuntimeError {
  guard inputs.length() == self.generator.input_names.length() else {
    fail_runtime(
      "Input arity mismatch: expected \{self.generator.input_names.length()}, got \{inputs.length()}",
    )
  }

  let mut env_values : @ihashmap.HashMap[String, DenValue[T]] = @ihashmap.HashMap::new()
  self.generator.input_names
  .iter2()
  .each((i, name) => env_values = env_values.add(name, inputs[i]))

  if size <= 0 {
    self.eval_node(self.generator.zero_case, env_values, 0)
  } else {
    self.eval_node(self.generator.succ_case, env_values, size)
  }
}

///|
fn[T] DenotationExec::eval_backtrack(
  self : DenotationExec[T],
  cases : Array[WeightedCaseAst],
  env_values : @ihashmap.HashMap[String, DenValue[T]],
  size : Int32,
) -> Array[DenValue[T]]? raise GenRuntimeError {
  let remaining = cases.copy()
  while !remaining.is_empty() {
    let idx = pick_weighted_index(remaining, self.rs)
    let chosen = remaining[idx]
    remaining.remove(idx) |> ignore
    guard self.eval_node(chosen.body, env_values, size) is Some(outputs) else {
      continue
    }
    return Some(outputs)
  }
  None
}

///|
fn[T] DenotationExec::eval_bind_source(
  self : DenotationExec[T],
  bind_name : String,
  source : BindSourceAst,
  env_values : @ihashmap.HashMap[String, DenValue[T]],
  size : Int32,
) -> DenValue[T]? raise GenRuntimeError {
  match source {
    Arbitrary => self.sample_value(bind_name, size)
    ArbitraryST(param, predicate) => {
      let max_tries = 32
      for _ in 0..<max_tries {
        guard self.sample_value(bind_name, size) is Some(candidate) else {
          continue
        }
        let env_with_candidate = env_values.add(param, candidate)
        if den_expect_bool(
            self.eval_expr(env_with_candidate, predicate, size),
            "arbitraryST predicate",
          ) {
          return Some(candidate)
        }
      }
      None
    }
    RecursiveCall(name, args) => {
      guard name == self.generator.aux_name else {
        fail_runtime(
          "Unknown recursive entrypoint `\{name}` (expected \{self.generator.aux_name})",
        )
      }
      let inputs = args.map(arg => self.eval_expr(env_values, arg, size))
      let next_size = if size <= 0 { 0 } else { size - 1 }
      guard self.run_aux(next_size, inputs) is Some(outputs) else { None }
      match outputs {
        [value] => Some(value)
        _ =>
          fail_runtime(
            "Recursive call expected one output, got \{outputs.length()} outputs",
          )
      }
    }
    Expr(code) =>
      fail_runtime(
        "Bind source `Expr(\{code})` is not executable in denotational eval",
      )
  }
}

///|
fn[T] DenotationExec::eval_node(
  self : DenotationExec[T],
  node : GenNode,
  env_values : @ihashmap.HashMap[String, DenValue[T]],
  size : Int32,
) -> Array[DenValue[T]]? raise GenRuntimeError {
  match node {
    RetNone => None
    RetSome(values) =>
      Some(values.map(value => self.eval_expr(env_values, value, size)))
    Backtrack(cases) => self.eval_backtrack(cases, env_values, size)
    MatchPattern(scrutinee, pattern, on_match, on_fail) => {
      guard env_values.get(scrutinee) is Some(value) else {
        fail_runtime(
          "Missing scrutinee variable for pattern match: \{scrutinee}",
        )
      }
      match den_bind_pattern(self.env, env_values, pattern, value) {
        Some(env_on_match) => self.eval_node(on_match, env_on_match, size)
        None => self.eval_node(on_fail, env_values, size)
      }
    }
    IfGuard(guard_ast, on_true, on_false) =>
      if self.eval_guard(env_values, guard_ast, size) {
        self.eval_node(on_true, env_values, size)
      } else {
        self.eval_node(on_false, env_values, size)
      }
    Bind(_, bind_name, source, next) => {
      guard self.eval_bind_source(bind_name, source, env_values, size)
        is Some(value) else {
        None
      }
      self.eval_node(next, env_values.add(bind_name, value), size)
    }
  }
}

///|
fn[T] den_output(
  env : DenotationEnv[T],
  value : DenValue[T],
) -> T? raise GenRuntimeError {
  match value {
    DenOut(out) => Some(out)
    _ => (env.to_output)(value)
  }
}

///|
/// Run denotational generator and return raw denotational outputs.
pub fn[T] Gen::run_values(
  self : Gen[T],
  size : Int32,
  inputs : Array[DenValue[T]],
  rs : @splitmix.RandomState,
) -> Array[DenValue[T]]? raise GenRuntimeError {
  let exec : DenotationExec[T] = {
    generator: self.generator,
    env: self.env,
    rs,
  }
  exec.run_aux(size, inputs)
}

///|
/// Run denotational generator and decode every output through `DenotationEnv`.
pub fn[T] Gen::run(
  self : Gen[T],
  size : Int32,
  inputs : Array[DenValue[T]],
  rs : @splitmix.RandomState,
) -> Array[T]? raise GenRuntimeError {
  guard self.run_values(size, inputs, rs) is Some(outputs) else { None }
  outputs.fold(init=Some([]), (acc, value) => {
    guard acc is Some(decoded) else { None }
    guard den_output(self.env, value) is Some(out) else { None }
    decoded.push(out)
    Some(decoded)
  })
}

///|
/// Single-output runner for denotational generator.
pub fn[T] Gen::run_one(
  self : Gen[T],
  size : Int32,
  inputs : Array[DenValue[T]],
  rs : @splitmix.RandomState,
) -> T? raise GenRuntimeError {
  guard self.run(size, inputs, rs) is Some(outputs) else { None }
  guard outputs is [out] else {
    fail_runtime(
      "run_one expects exactly one output, got \{outputs.length()} outputs",
    )
  }
  Some(out)
}

///|
/// Arity-1 helper with `RuntimeEncode` input conversion.
pub fn[T, In1 : RuntimeEncode] Gen::run1(
  self : Gen[T],
  size : Int32,
  input1 : In1,
  rs : @splitmix.RandomState,
) -> T? raise GenRuntimeError {
  self.run_one(size, [runtime_to_den(In1::to_runtime(input1))], rs)
}

///|
/// Arity-2 helper with `RuntimeEncode` input conversion.
pub fn[T, In1 : RuntimeEncode, In2 : RuntimeEncode] Gen::run2(
  self : Gen[T],
  size : Int32,
  input1 : In1,
  input2 : In2,
  rs : @splitmix.RandomState,
) -> T? raise GenRuntimeError {
  self.run_one(
    size,
    [
      runtime_to_den(In1::to_runtime(input1)),
      runtime_to_den(In2::to_runtime(input2)),
    ],
    rs,
  )
}
