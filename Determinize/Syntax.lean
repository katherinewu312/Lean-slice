import Mathlib.Data.Real.Basic

namespace Determinize

/-- Float mode: expectation reasoning (`E`) or general (`G`). -/
inductive Mode where
  | E : Mode
  | G : Mode
deriving DecidableEq, Repr

/-- Types -/
inductive Ty where
  | unit : Ty
  | bool : Ty
  | float : Mode → Ty
deriving DecidableEq, Repr

/-- Expressions for now:
`var`, float literals, booleans, `let`, comparison, arithmetic, `if`,
uniform, gaussian, poisson, exponential, beta, gamma. -/
inductive Expr where
  | var : String → Expr
  | const : ℝ → Expr
  | trueE : Expr
  | falseE : Expr
  | letE : String → Expr → Expr → Expr
  | lt : Expr → Expr → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | ifE : Expr → Expr → Expr → Expr
  | uniform : Expr → Expr → Expr
  | gaussian : Expr → Expr → Expr
  | poisson : Expr → Expr
  | exponential : Expr → Expr
  | beta : Expr → Expr → Expr
  | gamma : Expr → Expr → Expr

/-- Substitution for the current fragment -/
def subst (x : String) (v : Expr) : Expr → Expr
  | .var y =>
      if x = y then v else .var y
  | .const c =>
      .const c
  | .trueE =>
      .trueE
  | .falseE =>
      .falseE
  | .letE y e1 e2 =>
      if x = y then
        .letE y (subst x v e1) e2
      else
        .letE y (subst x v e1) (subst x v e2)
  | .lt e1 e2 =>
      .lt (subst x v e1) (subst x v e2)
  | .add e1 e2 =>
      .add (subst x v e1) (subst x v e2)
  | .mul e1 e2 =>
      .mul (subst x v e1) (subst x v e2)
  | .ifE c t f =>
      .ifE (subst x v c) (subst x v t) (subst x v f)
  | .uniform e1 e2 =>
      .uniform (subst x v e1) (subst x v e2)
  | .gaussian e1 e2 =>
      .gaussian (subst x v e1) (subst x v e2)
  | .poisson e =>
      .poisson (subst x v e)
  | .exponential e =>
      .exponential (subst x v e)
  | .beta e1 e2 =>
      .beta (subst x v e1) (subst x v e2)
  | .gamma e1 e2 =>
      .gamma (subst x v e1) (subst x v e2)

end Determinize
