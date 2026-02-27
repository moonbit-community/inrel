///|
/// Runtime value domain for direct execution of generated generator AST.
pub(all) enum RuntimeValue {
  RuntimeInt(Int)
  RuntimeBool(Bool)
  RuntimeString(String)
  RuntimeCtor(String, Array[RuntimeValue])
  RuntimeTuple(Array[RuntimeValue])
} derive(Eq, ToJson, Debug)

///|
fn RuntimeValue::render(self : RuntimeValue) -> String {
  match self {
    RuntimeInt(x) => x.to_string()
    RuntimeBool(x) => x.to_string()
    RuntimeString(x) => "\"\{x}\""
    RuntimeTuple(values) => {
      let body = values.map(value => value.render()).join(", ")
      "(\{body})"
    }
    RuntimeCtor(name, args) =>
      if args.is_empty() {
        name
      } else {
        let body = args.map(value => value.render()).join(", ")
        "\{name}(\{body})"
      }
  }
}

///|
pub impl Show for RuntimeValue with output(self, logger) {
  logger.write_string(self.render())
}

///|
/// Conversion from MoonBit values into runtime AST values.
pub(open) trait RuntimeEncode {
  to_runtime(Self) -> RuntimeValue
}

///|
/// Conversion from runtime AST values back to MoonBit values.
pub(open) trait RuntimeDecode {
  from_runtime(RuntimeValue) -> Self?
}

///|
pub impl RuntimeEncode for RuntimeValue with to_runtime(self : RuntimeValue) {
  self
}

///|
pub impl RuntimeDecode for RuntimeValue with from_runtime(value : RuntimeValue) {
  Some(value)
}

///|
pub impl RuntimeEncode for Int with to_runtime(self : Int) {
  RuntimeInt(self)
}

///|
pub impl RuntimeDecode for Int with from_runtime(value : RuntimeValue) {
  nat_to_int(value)
}

///|
pub impl RuntimeEncode for Bool with to_runtime(self : Bool) {
  RuntimeBool(self)
}

///|
pub impl RuntimeDecode for Bool with from_runtime(value : RuntimeValue) {
  match value {
    RuntimeBool(x) => Some(x)
    _ => None
  }
}

///|
pub impl RuntimeEncode for String with to_runtime(self : String) {
  RuntimeString(self)
}

///|
pub impl RuntimeDecode for String with from_runtime(value : RuntimeValue) {
  match value {
    RuntimeString(x) => Some(x)
    _ => None
  }
}

///|
/// Executable MoonBit-level generator compiled from `RelationSpec`.
///
/// It reuses Figure 1 / Figure 4 AST, but runs it directly instead of rendering
/// Rocq-like source text.
pub(all) struct MoonBitGenerator {
  aux_name : String
  input_names : Array[String]
  output_arity : Int
  var_types : @ihashmap.HashMap[String, @spec.TypeRef]
  zero_case : GenNode
  succ_case : GenNode
}

///|
fn upsert_var_type(
  var_types : @ihashmap.HashMap[String, @spec.TypeRef],
  name : String,
  ty : @spec.TypeRef,
) -> @ihashmap.HashMap[String, @spec.TypeRef] raise GenCompileError {
  match var_types.get(name) {
    None => var_types.add(name, ty)
    Some(existing) if existing == ty => var_types
    Some(existing) =>
      fail_gen(
        "Conflicting binder/parameter type for `\{name}`: \{existing} vs \{ty}",
      )
  }
}

///|
fn relation_var_types(
  rel : @spec.RelationSpec,
) -> @ihashmap.HashMap[String, @spec.TypeRef] raise GenCompileError {
  let mut var_types : @ihashmap.HashMap[String, @spec.TypeRef] = @ihashmap.HashMap::new()
  rel.params.each(param => {
    var_types = upsert_var_type(var_types, param.name, param.ty)
  })
  rel.constructors.each(ctor => {
    ctor.binders.each(binder => {
      var_types = upsert_var_type(var_types, binder.name, binder.ty)
    })
  })
  var_types
}

///|
/// Compile a relation into an executable MoonBit generator function.
///
/// This keeps the existing compilation pipeline:
/// `RelationSpec -> BoundedGeneratorAst -> executable evaluator`.
pub fn compile_relation_to_moonbit_generator(
  rel : @spec.RelationSpec,
  options? : CompileOptions = default_compile_options(),
) -> MoonBitGenerator raise {
  let ast = compile_relation_to_bounded_generator(rel, options~)
  {
    aux_name: ast.aux_name,
    input_names: ast.inputs,
    output_arity: rel.output_positions().length(),
    var_types: relation_var_types(rel),
    zero_case: ast.zero_case,
    succ_case: ast.succ_case,
  }
}

///|
fn default_sample_for_type(
  ty : @spec.TypeRef?,
  size : Int,
  rs : @splitmix.RandomState,
) -> RuntimeValue {
  match ty {
    Some(@spec.Named("Nat"))
    | Some(@spec.Named("Int"))
    | Some(@spec.Named("Atom")) => {
      let x : Int = @quickcheck.Arbitrary::arbitrary(size, rs)
      RuntimeInt(x)
    }
    Some(@spec.Named("Bool")) => {
      let x : Bool = @quickcheck.Arbitrary::arbitrary(size, rs)
      RuntimeBool(x)
    }
    Some(@spec.Named("String")) => {
      let x : String = @quickcheck.Arbitrary::arbitrary(size, rs)
      RuntimeString(x)
    }
    Some(@spec.Named(name)) | Some(@spec.App(name, _)) => RuntimeCtor(name, [])
    None => {
      let x : Int = @quickcheck.Arbitrary::arbitrary(size, rs)
      RuntimeInt(x)
    }
  }
}

///|
fn nat_to_int(value : RuntimeValue) -> Int? {
  match value {
    RuntimeInt(x) => Some(x)
    RuntimeCtor("O", []) => Some(0)
    RuntimeCtor("S", [pred]) =>
      match nat_to_int(pred) {
        Some(x) => Some(x + 1)
        None => None
      }
    _ => None
  }
}

///|
fn expect_int(
  value : RuntimeValue,
  context : String,
) -> Int raise GenRuntimeError {
  guard nat_to_int(value) is Some(x) else {
    fail_runtime("Expected Int/Nat in \{context}, got \{value}")
  }
  x
}

///|
fn expect_bool(
  value : RuntimeValue,
  context : String,
) -> Bool raise GenRuntimeError {
  guard value is RuntimeBool(x) else {
    fail_runtime("Expected Bool in \{context}, got \{value}")
  }
  x
}

///|
fn apply_ctor(name : String, args : Array[RuntimeValue]) -> RuntimeValue {
  match (name, args) {
    ("O", []) => RuntimeInt(0)
    ("S", [pred]) =>
      match nat_to_int(pred) {
        Some(x) => RuntimeInt(x + 1)
        None => RuntimeCtor(name, args)
      }
    _ => RuntimeCtor(name, args)
  }
}

///|
fn eval_builtin_call(
  name : String,
  args : Array[RuntimeValue],
) -> RuntimeValue? raise GenRuntimeError {
  match name {
    "=" | "==" => {
      guard args.length() == 2 else {
        fail_runtime("`\{name}` expects 2 arguments, got \{args.length()}")
      }
      Some(RuntimeBool(args[0] == args[1]))
    }
    "!=" => {
      guard args.length() == 2 else {
        fail_runtime("`!=` expects 2 arguments, got \{args.length()}")
      }
      Some(RuntimeBool(args[0] != args[1]))
    }
    "<" => {
      guard args.length() == 2 else {
        fail_runtime("`<` expects 2 arguments, got \{args.length()}")
      }
      let lhs = expect_int(args[0], "builtin `<` lhs")
      let rhs = expect_int(args[1], "builtin `<` rhs")
      Some(RuntimeBool(lhs < rhs))
    }
    "<=" => {
      guard args.length() == 2 else {
        fail_runtime("`<=` expects 2 arguments, got \{args.length()}")
      }
      let lhs = expect_int(args[0], "builtin `<=` lhs")
      let rhs = expect_int(args[1], "builtin `<=` rhs")
      Some(RuntimeBool(lhs <= rhs))
    }
    ">" => {
      guard args.length() == 2 else {
        fail_runtime("`>` expects 2 arguments, got \{args.length()}")
      }
      let lhs = expect_int(args[0], "builtin `>` lhs")
      let rhs = expect_int(args[1], "builtin `>` rhs")
      Some(RuntimeBool(lhs > rhs))
    }
    ">=" => {
      guard args.length() == 2 else {
        fail_runtime("`>=` expects 2 arguments, got \{args.length()}")
      }
      let lhs = expect_int(args[0], "builtin `>=` lhs")
      let rhs = expect_int(args[1], "builtin `>=` rhs")
      Some(RuntimeBool(lhs >= rhs))
    }
    "&&" => {
      guard args.length() == 2 else {
        fail_runtime("`&&` expects 2 arguments, got \{args.length()}")
      }
      let lhs = expect_bool(args[0], "builtin `&&` lhs")
      let rhs = expect_bool(args[1], "builtin `&&` rhs")
      Some(RuntimeBool(lhs && rhs))
    }
    "||" => {
      guard args.length() == 2 else {
        fail_runtime("`||` expects 2 arguments, got \{args.length()}")
      }
      let lhs = expect_bool(args[0], "builtin `||` lhs")
      let rhs = expect_bool(args[1], "builtin `||` rhs")
      Some(RuntimeBool(lhs || rhs))
    }
    "+" => {
      guard args.length() == 2 else {
        fail_runtime("`+` expects 2 arguments, got \{args.length()}")
      }
      let lhs = expect_int(args[0], "builtin `+` lhs")
      let rhs = expect_int(args[1], "builtin `+` rhs")
      Some(RuntimeInt(lhs + rhs))
    }
    "-" => {
      guard args.length() == 2 else {
        fail_runtime("`-` expects 2 arguments, got \{args.length()}")
      }
      let lhs = expect_int(args[0], "builtin `-` lhs")
      let rhs = expect_int(args[1], "builtin `-` rhs")
      Some(RuntimeInt(lhs - rhs))
    }
    "*" => {
      guard args.length() == 2 else {
        fail_runtime("`*` expects 2 arguments, got \{args.length()}")
      }
      let lhs = expect_int(args[0], "builtin `*` lhs")
      let rhs = expect_int(args[1], "builtin `*` rhs")
      Some(RuntimeInt(lhs * rhs))
    }
    "/" => {
      guard args.length() == 2 else {
        fail_runtime("`/` expects 2 arguments, got \{args.length()}")
      }
      let rhs = expect_int(args[1], "builtin `/` rhs")
      guard rhs != 0 else { fail_runtime("Division by zero in builtin `/`") }
      Some(RuntimeInt(expect_int(args[0], "builtin `/` lhs") / rhs))
    }
    _ => None
  }
}

///|
fn add_binding(
  env : @ihashmap.HashMap[String, RuntimeValue],
  name : String,
  value : RuntimeValue,
) -> @ihashmap.HashMap[String, RuntimeValue] {
  env.add(name, value)
}

///|
fn bind_pattern_args(
  env : @ihashmap.HashMap[String, RuntimeValue],
  patterns : Array[PatternAst],
  values : Array[RuntimeValue],
  idx : Int,
) -> @ihashmap.HashMap[String, RuntimeValue]? {
  if idx >= patterns.length() {
    Some(env)
  } else {
    guard bind_pattern(env, patterns[idx], values[idx]) is Some(next) else {
      None
    }
    bind_pattern_args(next, patterns, values, idx + 1)
  }
}

///|
fn bind_pattern(
  env : @ihashmap.HashMap[String, RuntimeValue],
  pattern : PatternAst,
  value : RuntimeValue,
) -> @ihashmap.HashMap[String, RuntimeValue]? {
  match (pattern, value) {
    (PVar(name), value) =>
      match env.get(name) {
        Some(bound) => if bound == value { Some(env) } else { None }
        None => Some(add_binding(env, name, value))
      }
    (PCtor("O", []), RuntimeInt(0)) => Some(env)
    (PCtor("S", [pred]), RuntimeInt(n)) =>
      if n > 0 {
        bind_pattern(env, pred, RuntimeInt(n - 1))
      } else {
        None
      }
    (PCtor(name, patterns), RuntimeCtor(value_name, values)) => {
      guard name == value_name && patterns.length() == values.length() else {
        None
      }
      bind_pattern_args(env, patterns, values, 0)
    }
    _ => None
  }
}

///|
fn pick_weighted_index(
  cases : Array[WeightedCaseAst],
  rs : @splitmix.RandomState,
) -> Int {
  guard !cases.is_empty() else { 0 }
  let total = cases.fold(init=0, (acc, c) => {
    acc + (if c.weight > 0 { c.weight } else { 1 })
  })
  let mut remaining = rs.next_positive_int() % total
  for i, c in cases {
    let w = if c.weight > 0 { c.weight } else { 1 }
    if remaining < w {
      return i
    }
    remaining -= w
  }
  cases.length() - 1
}

///|
priv struct RuntimeExecContext {
  generator : MoonBitGenerator
  rs : @splitmix.RandomState
}

///|
fn RuntimeExecContext::sample_value(
  self : RuntimeExecContext,
  bind_name : String,
  size : Int,
) -> RuntimeValue {
  default_sample_for_type(
    self.generator.var_types.get(bind_name),
    size,
    self.rs,
  )
}

///|
fn RuntimeExecContext::eval_expr(
  self : RuntimeExecContext,
  env : @ihashmap.HashMap[String, RuntimeValue],
  expr : ExprAst,
  size : Int,
) -> RuntimeValue raise GenRuntimeError {
  match expr {
    Var(name) =>
      match env.get(name) {
        Some(value) => value
        None => fail_runtime("Unbound variable in runtime evaluation: \{name}")
      }
    Ctor(name, args) => {
      let values = args.map(arg => self.eval_expr(env, arg, size))
      apply_ctor(name, values)
    }
    Call(name, args) => {
      let values = args.map(arg => self.eval_expr(env, arg, size))
      match eval_builtin_call(name, values) {
        Some(value) => value
        None =>
          fail_runtime(
            "Unknown predicate/function in runtime evaluation: \{name}",
          )
      }
    }
  }
}

///|
fn RuntimeExecContext::eval_decidable(
  self : RuntimeExecContext,
  env : @ihashmap.HashMap[String, RuntimeValue],
  expr : ExprAst,
  size : Int,
) -> Bool raise GenRuntimeError {
  expect_bool(self.eval_expr(env, expr, size), "decidable guard")
}

///|
fn RuntimeExecContext::eval_guard(
  self : RuntimeExecContext,
  env : @ihashmap.HashMap[String, RuntimeValue],
  guard_ast : GuardAst,
  size : Int,
) -> Bool raise GenRuntimeError {
  match guard_ast {
    Eq(lhs, rhs) =>
      self.eval_expr(env, lhs, size) == self.eval_expr(env, rhs, size)
    Decidable(expr) => self.eval_decidable(env, expr, size)
  }
}

///|
fn RuntimeExecContext::run_aux(
  self : RuntimeExecContext,
  size : Int,
  inputs : Array[RuntimeValue],
) -> Array[RuntimeValue]? raise GenRuntimeError {
  guard inputs.length() == self.generator.input_names.length() else {
    fail_runtime(
      "Input arity mismatch: expected \{self.generator.input_names.length()}, got \{inputs.length()}",
    )
  }

  let mut env : @ihashmap.HashMap[String, RuntimeValue] = @ihashmap.HashMap::new()
  for i, name in self.generator.input_names {
    env = env.add(name, inputs[i])
  }

  if size <= 0 {
    self.eval_node(self.generator.zero_case, env, 0)
  } else {
    self.eval_node(self.generator.succ_case, env, size)
  }
}

///|
fn RuntimeExecContext::eval_backtrack(
  self : RuntimeExecContext,
  cases : Array[WeightedCaseAst],
  env : @ihashmap.HashMap[String, RuntimeValue],
  size : Int,
) -> Array[RuntimeValue]? raise GenRuntimeError {
  let remaining = cases.copy()
  while !remaining.is_empty() {
    let idx = pick_weighted_index(remaining, self.rs)
    let chosen = remaining[idx]
    remaining.remove(idx) |> ignore
    guard self.eval_node(chosen.body, env, size) is Some(outputs) else {
      continue
    }
    return Some(outputs)
  }
  None
}

///|
fn RuntimeExecContext::eval_bind_source(
  self : RuntimeExecContext,
  bind_name : String,
  source : BindSourceAst,
  env : @ihashmap.HashMap[String, RuntimeValue],
  size : Int,
) -> RuntimeValue? raise GenRuntimeError {
  match source {
    Arbitrary => Some(self.sample_value(bind_name, size))
    ArbitraryST(param, predicate) => {
      let max_tries = 32
      for _ in 0..<max_tries {
        let candidate = self.sample_value(bind_name, size)
        let env_with_candidate = env.add(param, candidate)
        if self.eval_decidable(env_with_candidate, predicate, size) {
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
      let inputs = args.map(arg => self.eval_expr(env, arg, size))
      let next_size = if size <= 0 { 0 } else { size - 1 }
      guard self.run_aux(next_size, inputs) is Some(outputs) else { None }
      match outputs {
        [output] => Some(output)
        _ =>
          fail_runtime(
            "Recursive call expected a single output, got \{outputs.length()} outputs",
          )
      }
    }
    Expr(code) =>
      fail_runtime(
        "Bind source `Expr(\{code})` is not executable in runtime interpreter",
      )
  }
}

///|
fn RuntimeExecContext::eval_node(
  self : RuntimeExecContext,
  node : GenNode,
  env : @ihashmap.HashMap[String, RuntimeValue],
  size : Int,
) -> Array[RuntimeValue]? raise GenRuntimeError {
  match node {
    RetNone => None
    RetSome(values) =>
      Some(values.map(value => self.eval_expr(env, value, size)))
    Backtrack(cases) => self.eval_backtrack(cases, env, size)
    MatchPattern(scrutinee, pattern, on_match, on_fail) => {
      guard env.get(scrutinee) is Some(value) else {
        fail_runtime(
          "Missing scrutinee variable for pattern match: \{scrutinee}",
        )
      }
      match bind_pattern(env, pattern, value) {
        Some(env_on_match) => self.eval_node(on_match, env_on_match, size)
        None => self.eval_node(on_fail, env, size)
      }
    }
    IfGuard(guard_ast, on_true, on_false) =>
      if self.eval_guard(env, guard_ast, size) {
        self.eval_node(on_true, env, size)
      } else {
        self.eval_node(on_false, env, size)
      }
    Bind(_, bind_name, source, next) => {
      guard self.eval_bind_source(bind_name, source, env, size) is Some(value) else {
        None
      }
      self.eval_node(next, env.add(bind_name, value), size)
    }
  }
}

///|
/// Execute with an explicit random state.
pub fn MoonBitGenerator::run(
  self : MoonBitGenerator,
  size : Int,
  inputs : Array[RuntimeValue],
  rs : @splitmix.RandomState,
) -> Array[RuntimeValue]? raise GenRuntimeError {
  let ctx : RuntimeExecContext = { generator: self, rs }
  ctx.run_aux(size, inputs)
}

///|
/// Execute once with a seed-created random state.
pub fn MoonBitGenerator::run_seeded(
  self : MoonBitGenerator,
  size : Int,
  inputs : Array[RuntimeValue],
  seed? : UInt64 = 37,
) -> Array[RuntimeValue]? raise GenRuntimeError {
  self.run(size, inputs, @splitmix.new(seed~))
}

///|
/// Execute and decode all outputs to a MoonBit type.
pub fn[Out : RuntimeDecode] MoonBitGenerator::run_as(
  self : MoonBitGenerator,
  size : Int,
  inputs : Array[RuntimeValue],
  rs : @splitmix.RandomState,
) -> Array[Out]? raise GenRuntimeError {
  guard self.run(size, inputs, rs) is Some(outputs) else { None }
  outputs.fold(init=Some([]), (acc, value) => {
    guard acc is Some(decoded) else { None }
    guard Out::from_runtime(value) is Some(out_value) else { None }
    decoded.push(out_value)
    Some(decoded)
  })
}

///|
/// Convenience for single-output relations.
pub fn MoonBitGenerator::run_one(
  self : MoonBitGenerator,
  size : Int,
  inputs : Array[RuntimeValue],
  rs : @splitmix.RandomState,
) -> RuntimeValue? raise GenRuntimeError {
  guard self.output_arity == 1 else {
    fail_runtime(
      "run_one expects a single output relation, got \{self.output_arity}",
    )
  }
  guard self.run(size, inputs, rs) is Some(outputs) else { None }
  guard outputs is [value] else {
    fail_runtime("Internal output arity mismatch: expected 1 runtime value")
  }
  Some(value)
}

///|
/// Single-output typed execution using a decoder trait.
pub fn[Out : RuntimeDecode] MoonBitGenerator::run_one_as(
  self : MoonBitGenerator,
  size : Int,
  inputs : Array[RuntimeValue],
  rs : @splitmix.RandomState,
) -> Out? raise GenRuntimeError {
  guard self.run_one(size, inputs, rs) is Some(value) else { None }
  Out::from_runtime(value)
}

///|
/// Single-input + single-output convenience API.
pub fn[In1 : RuntimeEncode, Out : RuntimeDecode] MoonBitGenerator::run_one1(
  self : MoonBitGenerator,
  size : Int,
  input1 : In1,
  rs : @splitmix.RandomState,
) -> Out? raise GenRuntimeError {
  guard self.input_names.length() == 1 else {
    fail_runtime(
      "run_one1 expects arity 1 inputs, got \{self.input_names.length()}",
    )
  }
  self.run_one_as(size, [In1::to_runtime(input1)], rs)
}

///|
/// Two-input + single-output convenience API.
pub fn[In1 : RuntimeEncode, In2 : RuntimeEncode, Out : RuntimeDecode] MoonBitGenerator::run_one2(
  self : MoonBitGenerator,
  size : Int,
  input1 : In1,
  input2 : In2,
  rs : @splitmix.RandomState,
) -> Out? raise GenRuntimeError {
  guard self.input_names.length() == 2 else {
    fail_runtime(
      "run_one2 expects arity 2 inputs, got \{self.input_names.length()}",
    )
  }
  self.run_one_as(size, [In1::to_runtime(input1), In2::to_runtime(input2)], rs)
}
