///|
enum Ty {
  NatTy
  Arrow(Ty, Ty)
} derive(Eq, Debug)

///|
enum Ctx {
  CtxNil
  CtxCons(Ty, Ctx)
} derive(Eq)

///|
enum Tm {
  Var(Int32)
  Lit(Int32)
  Lam(Ty, Tm)
  App(Tm, Tm)
  Add(Tm, Tm)
  Mul(Tm, Tm)
} derive(Eq)

///|
fn wrap_paren(need_paren : Bool, s : String) -> String {
  if need_paren {
    "(\{s})"
  } else {
    s
  }
}

///|
fn Ty::pretty_prec(self : Ty, outer_prec : Int32) -> String {
  match self {
    NatTy => "Nat"
    Arrow(left, right) => {
      let left_text = left.pretty_prec(1)
      let right_text = right.pretty_prec(0)
      wrap_paren(outer_prec > 0, "\{left_text} -> \{right_text}")
    }
  }
}

///|
impl Show for Ty with fn to_string(self) {
  self.pretty_prec(0)
}

///|
impl Show for Ty with fn output(self, logger) {
  logger.write_string(self.to_string())
}

///|
fn pretty_var_name(depth : Int32, index : Int32) -> String {
  if index < depth {
    "x\{depth - 1 - index}"
  } else {
    "v\{index - depth}"
  }
}

///|
fn Tm::pretty_prec(self : Tm, depth : Int32, outer_prec : Int32) -> String {
  match self {
    Tm::Var(index) => pretty_var_name(depth, index)
    Lit(n) => n.to_string()
    Lam(arg_ty, body) => {
      let name = "x\{depth}"
      let body_text = body.pretty_prec(depth + 1, 0)
      wrap_paren(outer_prec > 0, "fun (\{name} : \{arg_ty}) => \{body_text}")
    }
    Add(lhs, rhs) => {
      let lhs_text = lhs.pretty_prec(depth, 1)
      let rhs_text = rhs.pretty_prec(depth, 2)
      wrap_paren(outer_prec > 1, "\{lhs_text} + \{rhs_text}")
    }
    Mul(lhs, rhs) => {
      let lhs_text = lhs.pretty_prec(depth, 2)
      let rhs_text = rhs.pretty_prec(depth, 3)
      wrap_paren(outer_prec > 2, "\{lhs_text} * \{rhs_text}")
    }
    App(f, x) => {
      let f_text = f.pretty_prec(depth, 3)
      let x_text = x.pretty_prec(depth, 4)
      wrap_paren(outer_prec > 3, "\{f_text} \{x_text}")
    }
  }
}

///|
impl Show for Tm with fn to_string(self) {
  self.pretty_prec(0, 0)
}

///|
impl Show for Tm with fn output(self, logger) {
  logger.write_string(self.to_string())
}

///|
fn ty_to_den(ty : Ty) -> DenValue[Tm] {
  match ty {
    NatTy => DenCtor("NatTy", [])
    Arrow(left, right) => DenCtor("Arrow", [ty_to_den(left), ty_to_den(right)])
  }
}

///|
fn den_to_ty(value : DenValue[Tm]) -> Ty? {
  match value {
    DenCtor("NatTy", []) => Some(NatTy)
    DenCtor("Arrow", [left, right]) => {
      guard den_to_ty(left) is Some(left_ty) else { None }
      guard den_to_ty(right) is Some(right_ty) else { None }
      Some(Arrow(left_ty, right_ty))
    }
    _ => None
  }
}

///|
fn ctx_to_den(ctx : Ctx) -> DenValue[Tm] {
  match ctx {
    CtxNil => DenCtor("CtxNil", [])
    CtxCons(head, tail) =>
      DenCtor("CtxCons", [ty_to_den(head), ctx_to_den(tail)])
  }
}

///|
fn den_to_ctx(value : DenValue[Tm]) -> Ctx? {
  match value {
    DenCtor("CtxNil", []) => Some(CtxNil)
    DenCtor("CtxCons", [head, tail]) => {
      guard den_to_ty(head) is Some(head_ty) else { None }
      guard den_to_ctx(tail) is Some(tail_ctx) else { None }
      Some(CtxCons(head_ty, tail_ctx))
    }
    _ => None
  }
}

///|
fn lookup_ctx(ctx : Ctx, index : Int32) -> Ty? {
  guard index >= 0 else { None }
  match (ctx, index) {
    (CtxNil, _) => None
    (CtxCons(head, _), 0) => Some(head)
    (CtxCons(_, tail), n) => lookup_ctx(tail, n - 1)
  }
}

///|
fn infer_type(ctx : Ctx, tm : Tm) -> Ty? {
  match tm {
    Tm::Var(i) => lookup_ctx(ctx, i)
    Lit(_) => Some(NatTy)
    Lam(arg_ty, body) =>
      infer_type(CtxCons(arg_ty, ctx), body).map(body_ty => {
        Arrow(arg_ty, body_ty)
      })
    App(f, x) => {
      guard infer_type(ctx, f) is Some(Arrow(arg_ty, ret_ty)) else { None }
      guard infer_type(ctx, x) is Some(x_ty) else { None }
      if x_ty == arg_ty {
        Some(ret_ty)
      } else {
        None
      }
    }
    Add(lhs, rhs) | Mul(lhs, rhs) =>
      match (infer_type(ctx, lhs), infer_type(ctx, rhs)) {
        (Some(NatTy), Some(NatTy)) => Some(NatTy)
        _ => None
      }
  }
}

///|
enum EvalValue {
  VNat(Int32)
  VClos(Ty, Tm, Array[EvalValue])
}

///|
fn EvalValue::pretty(self : EvalValue) -> String {
  match self {
    VNat(n) => n.to_string()
    VClos(arg_ty, body, env) =>
      "closure(\{Lam(arg_ty, body)}, env_size=\{env.length()})"
  }
}

///|
impl Show for EvalValue with fn to_string(self) {
  self.pretty()
}

///|
impl Show for EvalValue with fn output(self, logger) {
  logger.write_string(self.to_string())
}

///|
fn eval_env_prepend(
  head : EvalValue,
  tail : Array[EvalValue],
) -> Array[EvalValue] {
  let env : Array[EvalValue] = [head]
  env.append(tail)
  env
}

///|
fn eval_tm(tm : Tm, env : Array[EvalValue]) -> EvalValue? {
  match tm {
    Tm::Var(index) => env.get(index)
    Lit(n) => Some(VNat(n))
    Lam(arg_ty, body) => Some(VClos(arg_ty, body, env.copy()))
    App(f, x) =>
      match (eval_tm(f, env), eval_tm(x, env)) {
        (Some(VClos(_arg_ty, body, clos_env)), Some(arg_val)) =>
          eval_tm(body, eval_env_prepend(arg_val, clos_env))
        _ => None
      }
    Add(lhs, rhs) =>
      match (eval_tm(lhs, env), eval_tm(rhs, env)) {
        (Some(VNat(x)), Some(VNat(y))) => Some(VNat(x + y))
        _ => None
      }
    Mul(lhs, rhs) =>
      match (eval_tm(lhs, env), eval_tm(rhs, env)) {
        (Some(VNat(x)), Some(VNat(y))) => Some(VNat(x * y))
        _ => None
      }
  }
}

///|
fn value_matches_type_shape(value : EvalValue, ty : Ty) -> Bool {
  match (value, ty) {
    (VNat(n), NatTy) => n == n
    (VClos(_, _, _), Arrow(_, _)) => true
    _ => false
  }
}

///|
fn tm_has_var(tm : Tm) -> Bool {
  match tm {
    Tm::Var(_) => true
    Lit(_) => false
    Lam(_, body) => tm_has_var(body)
    App(f, x) => tm_has_var(f) || tm_has_var(x)
    Add(lhs, rhs) => tm_has_var(lhs) || tm_has_var(rhs)
    Mul(lhs, rhs) => tm_has_var(lhs) || tm_has_var(rhs)
  }
}

///|
fn tm_has_arith(tm : Tm) -> Bool {
  match tm {
    Tm::Var(_) => false
    Lit(_) => false
    Lam(_, body) => tm_has_arith(body)
    App(f, x) => tm_has_arith(f) || tm_has_arith(x)
    Add(_, _) | Mul(_, _) => true
  }
}

///|
fn sample_ty_den(size : Int32, rs : @splitmix.RandomState) -> DenValue[Tm] {
  if size <= 0 || rs.next_positive_int() % 3 == 0 {
    DenCtor("NatTy", [])
  } else {
    let next = size - 1
    DenCtor("Arrow", [sample_ty_den(next, rs), sample_ty_den(next, rs)])
  }
}

///|
fn lambda_tm_env() -> DenotationEnv[Tm] {
  den_out_env_builder()
  .with_ctor(
    "Var",
    args => {
      match args {
        [DenInt(i)] if i >= 0 => Some(Tm::Var(i))
        _ => None
      }
    },
    tm => {
      match tm {
        Tm::Var(i) => Some([DenInt(i)])
        _ => None
      }
    },
  )
  .with_ctor(
    "Lit",
    args => {
      match args {
        [DenInt(x)] => Some(Lit(x))
        _ => None
      }
    },
    tm => {
      match tm {
        Lit(x) => Some([DenInt(x)])
        _ => None
      }
    },
  )
  .with_ctor(
    "Lam",
    args => {
      match args {
        [arg_ty, DenOut(body)] => den_to_ty(arg_ty).map(arg => Lam(arg, body))
        _ => None
      }
    },
    tm => {
      match tm {
        Lam(arg_ty, body) => Some([ty_to_den(arg_ty), DenOut(body)])
        _ => None
      }
    },
  )
  .with_ctor(
    "App",
    args => {
      match args {
        [DenOut(f), DenOut(x)] => Some(App(f, x))
        _ => None
      }
    },
    tm => {
      match tm {
        App(f, x) => Some([DenOut(f), DenOut(x)])
        _ => None
      }
    },
  )
  .with_ctor(
    "Add",
    args => {
      match args {
        [DenOut(lhs), DenOut(rhs)] => Some(Add(lhs, rhs))
        _ => None
      }
    },
    tm => {
      match tm {
        Add(lhs, rhs) => Some([DenOut(lhs), DenOut(rhs)])
        _ => None
      }
    },
  )
  .with_ctor(
    "Mul",
    args => {
      match args {
        [DenOut(lhs), DenOut(rhs)] => Some(Mul(lhs, rhs))
        _ => None
      }
    },
    tm => {
      match tm {
        Mul(lhs, rhs) => Some([DenOut(lhs), DenOut(rhs)])
        _ => None
      }
    },
  )
  .with_call("lookup", args => {
    match args {
      [ctx_val, DenInt(i), ty_val] => {
        guard den_to_ctx(ctx_val) is Some(ctx) else { Some(DenBool(false)) }
        guard den_to_ty(ty_val) is Some(ty) else { Some(DenBool(false)) }
        Some(DenBool(lookup_ctx(ctx, i) == Some(ty)))
      }
      _ => fail_runtime("lookup expects 3 arguments")
    }
  })
  .with_arbitrary((_bind_name, ty, size, rs) => {
    match ty {
      Some(@spec.Named("Ty")) => Some(sample_ty_den(size, rs))
      _ => None
    }
  })
  .build()
}

///|
fn stlc_wt_relation_spec() -> @spec.RelationSpec {
  @spec.inductive(
    "stlc_wt",
    [
      @spec.in_param("depth", @spec.ty("Nat")),
      @spec.in_param("ctx", @spec.ty("Ctx")),
      @spec.in_param("ty", @spec.ty("Ty")),
      @spec.out_param("tm", @spec.ty("Tm")),
    ],
    [
      @spec.forall1(
        "WtLit",
        @spec.binder("k", @spec.ty("Nat")),
        k => {
          @spec.body([
            @spec.ctor("O", []),
            @spec.v("ctx"),
            @spec.ctor("NatTy", []),
            @spec.ctor("Lit", [k.term()]),
          ])
        },
        weight=1,
      ),
      @spec.forall1(
        "WtVar",
        @spec.binder("i", @spec.ty("Nat")),
        i => {
          @spec.body(
            [
              @spec.ctor("O", []),
              @spec.v("ctx"),
              @spec.v("ty"),
              @spec.ctor("Var", [i.term()]),
            ],
            hypotheses=[
              @spec.pred("lookup", [@spec.v("ctx"), i.term(), @spec.v("ty")]),
            ],
          )
        },
        weight=1,
      ),
      @spec.constructor_scoped(
        "WtLam",
        [
          @spec.binder("n", @spec.ty("Nat")),
          @spec.binder("a", @spec.ty("Ty")),
          @spec.binder("b", @spec.ty("Ty")),
          @spec.binder("body", @spec.ty("Tm")),
        ],
        scope => {
          let n = scope.v("n").term()
          let a = scope.v("a").term()
          let b = scope.v("b").term()
          let body = scope.v("body").term()
          @spec.body(
            [
              @spec.ctor("S", [n]),
              @spec.v("ctx"),
              @spec.ctor("Arrow", [a, b]),
              @spec.ctor("Lam", [a, body]),
            ],
            hypotheses=[
              @spec.rel("stlc_wt", [
                n,
                @spec.ctor("CtxCons", [a, @spec.v("ctx")]),
                b,
                body,
              ]),
            ],
          )
        },
        weight=3,
      ),
      @spec.constructor_scoped(
        "WtApp",
        [
          @spec.binder("n", @spec.ty("Nat")),
          @spec.binder("a", @spec.ty("Ty")),
          @spec.binder("b", @spec.ty("Ty")),
          @spec.binder("f", @spec.ty("Tm")),
          @spec.binder("x", @spec.ty("Tm")),
        ],
        scope => {
          let n = scope.v("n").term()
          let a = scope.v("a").term()
          let b = scope.v("b").term()
          let f = scope.v("f").term()
          let x = scope.v("x").term()
          @spec.body(
            [@spec.ctor("S", [n]), @spec.v("ctx"), b, @spec.ctor("App", [f, x])],
            hypotheses=[
              @spec.rel("stlc_wt", [
                n,
                @spec.v("ctx"),
                @spec.ctor("Arrow", [a, b]),
                f,
              ]),
              @spec.rel("stlc_wt", [n, @spec.v("ctx"), a, x]),
            ],
          )
        },
        weight=5,
      ),
      @spec.forall3(
        "WtAdd",
        @spec.binder("n", @spec.ty("Nat")),
        @spec.binder("lhs", @spec.ty("Tm")),
        @spec.binder("rhs", @spec.ty("Tm")),
        (n, lhs, rhs) => {
          let nat = @spec.ctor("NatTy", [])
          @spec.body(
            [
              @spec.ctor("S", [n.term()]),
              @spec.v("ctx"),
              nat,
              @spec.ctor("Add", [lhs.term(), rhs.term()]),
            ],
            hypotheses=[
              @spec.rel("stlc_wt", [n.term(), @spec.v("ctx"), nat, lhs.term()]),
              @spec.rel("stlc_wt", [n.term(), @spec.v("ctx"), nat, rhs.term()]),
            ],
          )
        },
        weight=4,
      ),
      @spec.forall3(
        "WtMul",
        @spec.binder("n", @spec.ty("Nat")),
        @spec.binder("lhs", @spec.ty("Tm")),
        @spec.binder("rhs", @spec.ty("Tm")),
        (n, lhs, rhs) => {
          let nat = @spec.ctor("NatTy", [])
          @spec.body(
            [
              @spec.ctor("S", [n.term()]),
              @spec.v("ctx"),
              nat,
              @spec.ctor("Mul", [lhs.term(), rhs.term()]),
            ],
            hypotheses=[
              @spec.rel("stlc_wt", [n.term(), @spec.v("ctx"), nat, lhs.term()]),
              @spec.rel("stlc_wt", [n.term(), @spec.v("ctx"), nat, rhs.term()]),
            ],
          )
        },
        weight=4,
      ),
    ],
  )
}

///|
test "integration: generate STLC well-typed lambda calculus ast" {
  let gen = try! compile_relation_to_gen(
    stlc_wt_relation_spec(),
    lambda_tm_env(),
  )
  let cases : Array[(Ctx, Ty)] = [
    (CtxNil, NatTy),
    (CtxNil, Arrow(NatTy, NatTy)),
    (CtxCons(NatTy, CtxNil), NatTy),
    (CtxCons(Arrow(NatTy, NatTy), CtxCons(NatTy, CtxNil)), NatTy),
    (CtxCons(NatTy, CtxCons(NatTy, CtxNil)), Arrow(NatTy, NatTy)),
  ]

  let mut saw_var = false
  let mut saw_arith = false
  for case in cases {
    let (ctx, ty) = case
    for seed in 1..<=80 {
      guard gen.run_one(
          8,
          [DenInt(4), ctx_to_den(ctx), ty_to_den(ty)],
          @splitmix.RandomState(seed=seed.to_uint64()),
        )
        is Some(tm) else {
        fail("generator returned None for ctx=\{ctx}, ty=\{ty}, seed=\{seed}")
      }
      if tm_has_var(tm) {
        saw_var = true
      }
      if tm_has_arith(tm) {
        saw_arith = true
      }
      assert_eq(infer_type(ctx, tm), Some(ty))
    }
  }
  assert_true(saw_var)
  assert_true(saw_arith)
}

///|
test "typing/eval: Add and Mul are well-typed Nat arithmetic" {
  let arith_tm = Add(Mul(Lit(2), Lit(3)), Add(Lit(4), Lit(5)))
  assert_eq(infer_type(CtxNil, arith_tm), Some(NatTy))
  guard eval_tm(arith_tm, []) is Some(VNat(15)) else {
    fail("arith eval mismatch")
  }
  assert_eq(arith_tm.to_string(), "2 * 3 + (4 + 5)")

  let plus1 = Lam(NatTy, Add(Var(0), Lit(1)))
  let applied = App(plus1, Lit(7))
  assert_eq(infer_type(CtxNil, applied), Some(NatTy))
  guard eval_tm(applied, []) is Some(VNat(8)) else {
    fail("application eval mismatch")
  }
}

///|
test "evaluation: STLC well-typed closed terms never go wrong" {
  let gen = try! compile_relation_to_gen(
    stlc_wt_relation_spec(),
    lambda_tm_env(),
  )
  let closed_targets : Array[Ty] = [
    NatTy,
    Arrow(NatTy, NatTy),
    Arrow(Arrow(NatTy, NatTy), Arrow(NatTy, NatTy)),
  ]
  for ty in closed_targets {
    for seed in 1..<=120 {
      guard gen.run_one(
          9,
          [DenInt(5), ctx_to_den(CtxNil), ty_to_den(ty)],
          @splitmix.RandomState(seed=seed.to_uint64()),
        )
        is Some(tm) else {
        fail("generator returned None for closed target ty=\{ty}, seed=\{seed}")
      }
      assert_eq(infer_type(CtxNil, tm), Some(ty))
      guard eval_tm(tm, []) is Some(value) else { fail("stuck term: \{tm}") }
      println("term: \{tm}")
      println("evaluated to: \{value}")
      assert_true(value_matches_type_shape(value, ty))
    }
  }
}

///|
pub extend Ctx with Eq::{not_equal, equal}

///|
pub extend Ctx with Show::{to_string, output}

///|
pub extend Tm with Eq::{not_equal, equal}

///|
pub extend Ty with Debug::{to_repr}

///|
pub extend Ty with Eq::{not_equal, equal}

///|
impl Show for Ctx with fn output(self, logger) {
  match self {
    CtxNil => logger.write_string("CtxNil")
    CtxCons(ty, ctx) => logger <+ "CtxCons(\{ty}, \{ctx})"
  }
}

///|
extend Ty with Show::{to_string}

///|
extend Tm with Show::{to_string}

///|
extend EvalValue with Show::{to_string}
