import Mathlib.Data.Real.Basic

namespace Determinize

/-- Float mode: expectation reasoning (`E`) or general (`G`). -/
inductive Mode where
  | E : Mode
  | G : Mode
deriving DecidableEq, Repr

/-- Types. -/
inductive Ty where
  | unit : Ty
  | bool : Ty
  | float : Mode → Ty
deriving DecidableEq, Repr

/-- Mode preorder (`G ≼ E`, and reflexive). -/
inductive ModeLE : Mode → Mode → Prop where
  | refl (m : Mode) : ModeLE m m
  | g_le_e : ModeLE .G .E

infix:50 " ≼ " => ModeLE

lemma modeLe_trans {m1 m2 m3 : Mode} (h12 : m1 ≼ m2) (h23 : m2 ≼ m3) : m1 ≼ m3 := by
  cases h12 with
  | refl m =>
      simpa using h23
  | g_le_e =>
      cases h23 with
      | refl =>
          exact ModeLE.g_le_e

/-- Type subtyping for modes and standard type structure. -/
inductive TySub : Ty → Ty → Prop where
  | refl {τ : Ty} : TySub τ τ
  | float {m1 m2 : Mode} :
      m1 ≼ m2 →
      TySub (.float m1) (.float m2)

infix:50 " <: " => TySub

/-- Typed expressions. -/
inductive TExpr : Ty → Type where
  | var {τ : Ty} (x : String) : TExpr τ
  | unitE : TExpr .unit
  | const {m : Mode} (c : ℝ) : TExpr (.float m)
  | trueE : TExpr .bool
  | falseE : TExpr .bool
  | letE {τ1 τ2 : Ty} (x : String) (e1 : TExpr τ1) (e2 : TExpr τ2) : TExpr τ2
  | lt {m1 m2 : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ .G → m2 ≼ .G → TExpr .bool
  | add {m1 m2 m : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ m → m2 ≼ m → TExpr (.float m)
  | mulG {m1 m2 m : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ .G → m2 ≼ .G → TExpr (.float m)
  | mulConstL {m1 m2 m : Mode}
      (c : ℝ) (e : TExpr (.float m2)) :
      m1 ≼ m → m2 ≼ m → TExpr (.float m)
  | mulConstR {m1 m2 m : Mode}
      (e : TExpr (.float m1)) (c : ℝ) :
      m1 ≼ m → m2 ≼ m → TExpr (.float m)
  | ifE {τ : Ty} (c : TExpr .bool) (t f : TExpr τ) : TExpr τ
  | uniform {m1 m2 m : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ m → m2 ≼ m → TExpr (.float m)
  | gaussian {m1 m2 m : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ m → m2 ≼ .G → TExpr (.float m)
  | poisson {m1 m : Mode}
      (e1 : TExpr (.float m1)) :
      m1 ≼ m → TExpr (.float m)
  | exponential {m1 m : Mode}
      (e1 : TExpr (.float m1)) :
      m1 ≼ .G → TExpr (.float m)
  | beta {m1 m2 m : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ .G → m2 ≼ .G → TExpr (.float m)
  | gamma {m1 m2 m : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ m → m2 ≼ .G → TExpr (.float m)

namespace TExpr

/-- Type-preserving substitution for the named-variable presentation. -/
def subst {σ τ : Ty} (x : String) (v : TExpr σ) : TExpr τ → TExpr τ
  | .var y =>
      if x = y then
        if h : σ = τ then
          cast (congrArg TExpr h) v
        else
          .var y
      else
        .var y
  | .unitE =>
      .unitE
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
  | .lt e1 e2 h1 h2 =>
      .lt (subst x v e1) (subst x v e2) h1 h2
  | .add e1 e2 h1 h2 =>
      .add (subst x v e1) (subst x v e2) h1 h2
  | .mulG e1 e2 h1 h2 =>
      .mulG (subst x v e1) (subst x v e2) h1 h2
  | .mulConstL c e h1 h2 =>
      .mulConstL c (subst x v e) h1 h2
  | .mulConstR e c h1 h2 =>
      .mulConstR (subst x v e) c h1 h2
  | .ifE c t f =>
      .ifE (subst x v c) (subst x v t) (subst x v f)
  | .uniform e1 e2 h1 h2 =>
      .uniform (subst x v e1) (subst x v e2) h1 h2
  | .gaussian e1 e2 h1 h2 =>
      .gaussian (subst x v e1) (subst x v e2) h1 h2
  | .poisson e h =>
      .poisson (subst x v e) h
  | .exponential e h =>
      .exponential (subst x v e) h
  | .beta e1 e2 h1 h2 =>
      .beta (subst x v e1) (subst x v e2) h1 h2
  | .gamma e1 e2 h1 h2 =>
      .gamma (subst x v e1) (subst x v e2) h1 h2

/-- Numeric values. -/
def floatValue? : {m : Mode} → TExpr (.float m) → Option ℝ
  | _, .const c =>
      some c
  | _, _ =>
      none

/-- Boolean values. -/
def boolValue? : TExpr .bool → Option Bool
  | .trueE =>
      some true
  | .falseE =>
      some false
  | _ =>
      none

/-- Unit values. -/
def unitValue? : TExpr .unit → Option Unit
  | .unitE =>
      some ()
  | _ =>
      none

/-- Syntactic values in the intrinsically typed fragment. -/
def isValue : {τ : Ty} → TExpr τ → Bool
  | .unit, e =>
      (unitValue? e).isSome
  | .bool, e =>
      (boolValue? e).isSome
  | .float _, e =>
      (floatValue? e).isSome

end TExpr

end Determinize
