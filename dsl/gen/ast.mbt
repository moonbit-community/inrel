///|
/// Pattern AST for emitted generator code.
///
/// Correspondence (paper Figure 2):
/// `Pattern = Unknown | C Pattern`
pub(all) enum PatternAst {
  PVar(String)
  PCtor(String, Array[PatternAst])
} derive(Eq, ToJson)

///|
/// Expression AST used by generator code nodes.
pub(all) enum ExprAst {
  Var(String)
  Ctor(String, Array[ExprAst])
  Call(String, Array[ExprAst])
} derive(Eq, ToJson)

///|
/// Boolean guard/check nodes for generated code.
///
/// `Eq` corresponds to checks from `emit_equalities` in Figure 4.
/// `Decidable` corresponds to runtime checks `if (S e)? then ... else ret None`.
pub(all) enum GuardAst {
  Eq(ExprAst, ExprAst)
  Decidable(ExprAst)
} derive(Eq, ToJson)

///|
/// Monadic bind flavor in emitted code.
///
/// - `Do`  -> `do!`
/// - `DoM` -> `doM!`
pub(all) enum BindFlavor {
  Do
  DoM
} derive(Eq, ToJson)

///|
/// Source expression for a bind in emitted generator code.
pub(all) enum BindSourceAst {
  Arbitrary
  ArbitraryST(String, ExprAst)
  RecursiveCall(String, Array[String])
  Expr(String)
} derive(Eq, ToJson)

///|
/// Weighted branch used in `backtrack`.
///
/// Correspondence (paper Section 4.3):
/// `backtrack [ ... (wC, gC) ... ]`
pub(all) struct WeightedCaseAst {
  weight : Int
  body : GenNode
} derive(Eq, ToJson)

///|
/// AST for generated code shape from Sections 4.3-4.7.
pub(all) enum GenNode {
  RetNone
  RetSome(Array[ExprAst])
  Backtrack(Array[WeightedCaseAst])
  MatchPattern(String, PatternAst, GenNode, GenNode)
  IfGuard(GuardAst, GenNode, GenNode)
  Bind(BindFlavor, String, BindSourceAst, GenNode)
} derive(Eq, ToJson)

///|
/// Top-level bounded generator AST.
///
/// Correspondence (paper Section 4.3):
/// `Fixpoint aux_arb size in1 ... inn := match size with | O => ... | S size' => ... end`
pub(all) struct BoundedGeneratorAst {
  aux_name : String
  size_var : String
  inputs : Array[String]
  succ_size_var : String
  zero_case : GenNode
  succ_case : GenNode
} derive(Eq, ToJson)

///|
fn indent(level : Int) -> String {
  let sb = StringBuilder::new()
  for _ in 0..<level {
    sb.write_string("  ")
  }
  sb.to_string()
}

///|
fn push_lines(dst : Array[String], src : Array[String]) -> Unit {
  for line in src {
    dst.push(line)
  }
}

///|
fn PatternAst::render(self : PatternAst) -> String {
  match self {
    PVar(name) => name
    PCtor(name, args) =>
      if args.is_empty() {
        name
      } else {
        let rendered = args.map(arg => {
          match arg {
            PVar(_) => arg.render()
            PCtor(_, _) => "(\{arg.render()})"
          }
        })
        let args_text = rendered.join(" ")
        "\{name} \{args_text}"
      }
  }
}

///|
fn is_infix_symbol(name : String) -> Bool {
  match name {
    "<"
    | "<="
    | ">"
    | ">="
    | "="
    | "!="
    | "=="
    | "+"
    | "-"
    | "*"
    | "/"
    | "&&"
    | "||" => true
    _ => false
  }
}

///|
fn ExprAst::render(self : ExprAst) -> String {
  match self {
    Var(name) => name
    Ctor(name, args) =>
      if args.is_empty() {
        name
      } else {
        let args_text = args.map(arg => arg.render()).join(" ")
        "(\{name} \{args_text})"
      }
    Call(name, args) =>
      if args.length() == 2 && is_infix_symbol(name) {
        let left = args[0].render()
        let right = args[1].render()
        "\{left} \{name} \{right}"
      } else if args.is_empty() {
        name
      } else {
        let args_text = args.map(arg => arg.render()).join(" ")
        "\{name} \{args_text}"
      }
  }
}

///|
fn GuardAst::render(self : GuardAst) -> String {
  match self {
    Eq(lhs, rhs) => "(\{lhs.render()} = \{rhs.render()})?"
    Decidable(expr) => "(\{expr.render()})?"
  }
}

///|
fn BindSourceAst::render(self : BindSourceAst) -> String {
  match self {
    Arbitrary => "arbitrary"
    ArbitraryST(param, predicate) =>
      "arbitraryST (fun \{param} => \{predicate.render()})"
    RecursiveCall(name, args) =>
      if args.is_empty() {
        name
      } else {
        let args_text = args.join(" ")
        "\{name} \{args_text}"
      }
    Expr(code) => code
  }
}

///|
fn render_some_payload(values : Array[ExprAst]) -> String {
  if values.length() == 0 {
    "()"
  } else if values.length() == 1 {
    values[0].render()
  } else {
    let values_text = values.map(value => value.render()).join(", ")
    "(\{values_text})"
  }
}

///|
fn GenNode::render_lines(self : GenNode, level : Int) -> Array[String] {
  let i = indent(level)
  match self {
    RetNone => ["\{i}ret None"]
    RetSome(values) => ["\{i}ret (Some \{render_some_payload(values)})"]
    Bind(kind, name, source, next) => {
      let head = match kind {
        Do => "\{i}do! \{name} <- \{source.render()};"
        DoM => "\{i}doM! \{name} <- \{source.render()};"
      }
      let lines : Array[String] = [head]
      push_lines(lines, next.render_lines(level))
      lines
    }
    IfGuard(cond, on_true, on_false) => {
      let lines : Array[String] = ["\{i}if \{cond.render()} then"]
      push_lines(lines, on_true.render_lines(level + 1))
      lines.push("\{i}else")
      push_lines(lines, on_false.render_lines(level + 1))
      lines
    }
    MatchPattern(scrutinee, pattern, on_match, on_fail) => {
      let lines : Array[String] = ["\{i}match \{scrutinee} with"]
      lines.push("\{i}| \{pattern.render()} =>")
      push_lines(lines, on_match.render_lines(level + 1))
      lines.push("\{i}| _ =>")
      push_lines(lines, on_fail.render_lines(level + 1))
      lines
    }
    Backtrack(cases) => {
      let lines : Array[String] = ["\{i}backtrack ["]
      for idx, c in cases {
        let start = if idx == 0 {
          "\{i}  (\{c.weight},"
        } else {
          "\{i}  ; (\{c.weight},"
        }
        lines.push(start)
        push_lines(lines, c.body.render_lines(level + 2))
        lines.push("\{i}  )")
      }
      lines.push("\{i}]")
      lines
    }
  }
}

///|
pub fn GenNode::to_paper_string(self : GenNode) -> String {
  self.render_lines(0).join("\n")
}

///|
pub fn BoundedGeneratorAst::to_paper_string(
  self : BoundedGeneratorAst,
) -> String {
  let args = if self.inputs.is_empty() {
    ""
  } else {
    let inputs_text = self.inputs.join(" ")
    " \{inputs_text}"
  }
  let lines : Array[String] = [
    "Fixpoint \{self.aux_name} \{self.size_var}\{args} :=",
    "  match \{self.size_var} with",
    "  | O =>",
  ]
  push_lines(lines, self.zero_case.render_lines(2))
  lines.push("  | S \{self.succ_size_var} =>")
  push_lines(lines, self.succ_case.render_lines(2))
  lines.push("  end.")
  lines.join("\n")
}

///|
pub impl Show for PatternAst with output(self, logger) {
  logger.write_string(self.render())
}

///|
pub impl Show for ExprAst with output(self, logger) {
  logger.write_string(self.render())
}

///|
pub impl Show for GuardAst with output(self, logger) {
  logger.write_string(self.render())
}

///|
pub impl Show for BindSourceAst with output(self, logger) {
  logger.write_string(self.render())
}

///|
pub impl Show for GenNode with output(self, logger) {
  logger.write_string(self.to_paper_string())
}

///|
pub impl Show for BoundedGeneratorAst with output(self, logger) {
  logger.write_string(self.to_paper_string())
}
