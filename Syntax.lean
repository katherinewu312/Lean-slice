import Monad

namespace Slice

open MeasureTheory ProbabilityTheory

-- ---------------------------------------------------------------------------
-- Expression AST
-- ---------------------------------------------------------------------------

-- Probabilities in discrete(...) must sum to 1.
def DiscreteProbs : Type := {probs : List Prob // probs.sum = 1}

/-- Fixed index set for discrete parameters. -/
abbrev DiscreteParam : Type := Nat

/-- Table of discrete parameters fixed at setup time. -/
axiom discreteProbsOf : DiscreteParam → DiscreteProbs

/--
Slice expressions.
-/
inductive Expr where
  | var       : String → Expr
  | const     : ℝ → Expr
  | trueE     : Expr
  | falseE    : Expr
  | finconst  : (n : ℕ) → Fin n → Expr
  | discrete  : DiscreteParam → Expr
  | diverge   : Expr
  | letE      : String → Expr → Expr → Expr
  | lt        : Expr → Expr → Expr
  | ifE       : Expr → Expr → Expr → Expr
  | uniform   : Expr → Expr → Expr
  /-
  | trueE     : Expr
  | falseE    : Expr
  | sample    : SampleOp → Expr → Expr → Expr
  | discrete  : (probs : List Prob) → ValidProbs probs → Expr
  | cmp       : CmpOp → Expr → Expr → Expr
  | andE      : Expr → Expr → Expr
  | orE       : Expr → Expr → Expr
  | notE      : Expr → Expr
  | pair      : Expr → Expr → Expr
  | fstE      : Expr → Expr
  | sndE      : Expr → Expr
  | funE      : String → Expr → Expr
  | app       : Expr → Expr → Expr
  | finConst  : Nat → Nat → Expr
  | finCmp    : CmpOp → Expr → Expr → Nat → Expr
  | finEq     : Expr → Expr → Nat → Expr
  | observe   : Expr → Expr
  | fixE      : String → String → Expr → Expr
  | nil       : Expr
  | cons      : Expr → Expr → Expr
  | matchList : Expr → Expr → String → String → Expr → Expr
  | unit      : Expr
  | seq       : Expr → Expr → Expr
  | runtimeError : String → Expr
  -/

-- ---------------------------------------------------------------------------
-- Syntactic values and substitution
-- ---------------------------------------------------------------------------

/-- Syntactic values: closed, fully-reduced expressions. -/
def isValue : Expr → Bool
  | .const _      => true
  | .trueE        => true
  | .falseE       => true
  | .finconst _ _ => true
  /-
  | .finConst _ _ => true
  | .funE _ _     => true
  | .fixE _ _ _   => true
  | .unit         => true
  | .nil          => true
  | .pair e1 e2   => isValue e1 && isValue e2
  | .cons h t     => isValue h  && isValue t
  -/
  | _             => false

/-- Capture-avoiding substitution (alpha-renaming assumed). -/
partial def subst (x : String) (v : Expr) : Expr → Expr
  | .var y          => if x = y then v else .var y
  | .const r        => .const r
  | .trueE          => .trueE
  | .falseE         => .falseE
  | .finconst n k   => .finconst n k
  | .discrete ps    => .discrete ps
  | .diverge        => .diverge
  | .letE y e1 e2   =>
      if x = y then .letE y (subst x v e1) e2
      else .letE y (subst x v e1) (subst x v e2)
  | .lt e1 e2           => .lt (subst x v e1) (subst x v e2)
  | .ifE c t f          => .ifE  (subst x v c) (subst x v t) (subst x v f)
  | .uniform e1 e2  => .uniform (subst x v e1) (subst x v e2)
  /-
  | .sample d e1 e2     => .sample d (subst x v e1) (subst x v e2)
  | .discrete ps hps    => .discrete ps hps
  | .cmp op e1 e2       => .cmp op (subst x v e1) (subst x v e2)
  | .andE e1 e2         => .andE (subst x v e1) (subst x v e2)
  | .orE  e1 e2         => .orE  (subst x v e1) (subst x v e2)
  | .notE e             => .notE (subst x v e)
  | .pair e1 e2         => .pair (subst x v e1) (subst x v e2)
  | .fstE e             => .fstE (subst x v e)
  | .sndE e             => .sndE (subst x v e)
  | .funE y body        =>
      if x = y then .funE y body else .funE y (subst x v body)
  | .app e1 e2          => .app (subst x v e1) (subst x v e2)
  | .finConst k n       => .finConst k n
  | .finCmp op e1 e2 n  => .finCmp op (subst x v e1) (subst x v e2) n
  | .finEq e1 e2 n      => .finEq (subst x v e1) (subst x v e2) n
  | .observe e          => .observe (subst x v e)
  | .fixE f y body      =>
      if x = f ∨ x = y then .fixE f y body else .fixE f y (subst x v body)
  | .nil                => .nil
  | .cons h t           => .cons (subst x v h) (subst x v t)
  | .matchList e nb y ys cb =>
      let e'  := subst x v e
      let nb' := subst x v nb
      if x = y ∨ x = ys then .matchList e' nb' y ys cb
      else .matchList e' nb' y ys (subst x v cb)
  | .unit               => .unit
  | .seq e1 e2          => .seq (subst x v e1) (subst x v e2)
  | .runtimeError s     => .runtimeError s
  -/



end Slice
