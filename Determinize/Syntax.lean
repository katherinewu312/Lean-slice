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
  | list : Ty → Ty
  | pair : Ty → Ty → Ty
  | sum : Ty → Ty → Ty
  | arrow : Ty → Ty → Ty
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

/-- Subtypes. -/
inductive Sub : Ty → Ty → Type where
  | unit : Sub .unit .unit
  | bool : Sub .bool .bool
  | list {τ : Ty} :
      Sub (.list τ) (.list τ)
  | pair {τ1 τ2 : Ty} :
      Sub (.pair τ1 τ2) (.pair τ1 τ2)
  | sum {τ1 τ2 : Ty} :
      Sub (.sum τ1 τ2) (.sum τ1 τ2)
  | arrow {τ1 τ2 : Ty} :
      Sub (.arrow τ1 τ2) (.arrow τ1 τ2)
  | float {m1 m2 : Mode} :
      m1 ≼ m2 →
      Sub (.float m1) (.float m2)

infix:50 " <: " => Sub

/-- Typed expressions. -/
inductive TExpr : Ty → Type where
  | var {τ : Ty} (x : String) : TExpr τ
  | lam {τ1 τ2 : Ty} (x : String) (body : TExpr τ2) : TExpr (.arrow τ1 τ2)
  | recE {τ1 τ2 : Ty} (f x : String) (body : TExpr τ2) : TExpr (.arrow τ1 τ2)
  | app {τ1 τ2 : Ty} (fn : TExpr (.arrow τ1 τ2)) (arg : TExpr τ1) : TExpr τ2
  | unitE : TExpr .unit
  | const {m : Mode} (c : ℝ) : TExpr (.float m)
  | trueE : TExpr .bool
  | falseE : TExpr .bool
  | pair {τ1 τ2 : Ty} (e1 : TExpr τ1) (e2 : TExpr τ2) : TExpr (.pair τ1 τ2)
  | fst {τ1 τ2 : Ty} (e : TExpr (.pair τ1 τ2)) : TExpr τ1
  | snd {τ1 τ2 : Ty} (e : TExpr (.pair τ1 τ2)) : TExpr τ2
  | inl {τ1 τ2 : Ty} (e : TExpr τ1) : TExpr (.sum τ1 τ2)
  | inr {τ1 τ2 : Ty} (e : TExpr τ2) : TExpr (.sum τ1 τ2)
  | caseE {τ1 τ2 τ : Ty}
      (scrut : TExpr (.sum τ1 τ2))
      (x : String) (left : TExpr τ)
      (y : String) (right : TExpr τ) : TExpr τ
  | nilE {τ : Ty} : TExpr (.list τ)
  | cons {τ : Ty} (head : TExpr τ) (tail : TExpr (.list τ)) : TExpr (.list τ)
  | matchList {τ σ : Ty}
      (scrut : TExpr (.list τ)) (nilBranch : TExpr σ)
      (x xs : String) (consBranch : TExpr σ) : TExpr σ
  | letE {τ1 τ2 : Ty} (x : String) (e1 : TExpr τ1) (e2 : TExpr τ2) : TExpr τ2
  | lt {m1 m2 : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ .G → m2 ≼ .G → TExpr .bool
  | neg {m1 m : Mode}
      (e : TExpr (.float m1)) :
      m1 ≼ m → TExpr (.float m)
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
  | div {m1 m2 m : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ m → m2 ≼ .G → TExpr (.float m)
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
  | subsume {τ1 τ2 : Ty} (e : TExpr τ1) :
      τ1 <: τ2 → TExpr τ2

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
  | .lam y body =>
      if x = y then
        .lam y body
      else
        .lam y (subst x v body)
  | .recE f y body =>
      if x = f || x = y then
        .recE f y body
      else
        .recE f y (subst x v body)
  | .app fn arg =>
      .app (subst x v fn) (subst x v arg)
  | .unitE =>
      .unitE
  | .const c =>
      .const c
  | .trueE =>
      .trueE
  | .falseE =>
      .falseE
  | .pair e1 e2 =>
      .pair (subst x v e1) (subst x v e2)
  | .fst e =>
      .fst (subst x v e)
  | .snd e =>
      .snd (subst x v e)
  | .inl e =>
      .inl (subst x v e)
  | .inr e =>
      .inr (subst x v e)
  | .caseE scrut y left z right =>
      .caseE
        (subst x v scrut)
        y
        (if x = y then left else subst x v left)
        z
        (if x = z then right else subst x v right)
  | .nilE =>
      .nilE
  | .cons head tail =>
      .cons (subst x v head) (subst x v tail)
  | .matchList scrut nilBranch y ys consBranch =>
      .matchList
        (subst x v scrut)
        (subst x v nilBranch)
        y
        ys
        (if x = y || x = ys then consBranch else subst x v consBranch)
  | .letE y e1 e2 =>
      if x = y then
        .letE y (subst x v e1) e2
      else
        .letE y (subst x v e1) (subst x v e2)
  | .lt e1 e2 h1 h2 =>
      .lt (subst x v e1) (subst x v e2) h1 h2
  | .neg e h =>
      .neg (subst x v e) h
  | .add e1 e2 h1 h2 =>
      .add (subst x v e1) (subst x v e2) h1 h2
  | .mulG e1 e2 h1 h2 =>
      .mulG (subst x v e1) (subst x v e2) h1 h2
  | .mulConstL c e h1 h2 =>
      .mulConstL c (subst x v e) h1 h2
  | .mulConstR e c h1 h2 =>
      .mulConstR (subst x v e) c h1 h2
  | .div e1 e2 h1 h2 =>
      .div (subst x v e1) (subst x v e2) h1 h2
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
  | .subsume e h =>
      .subsume (subst x v e) h

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
  | .pair _ _, .pair e1 e2 =>
      isValue e1 && isValue e2
  | .pair _ _, _ =>
      false
  | .sum _ _, .inl e =>
      isValue e
  | .sum _ _, .inr e =>
      isValue e
  | .sum _ _, _ =>
      false
  | .list _, .nilE =>
      true
  | .list _, .cons head tail =>
      isValue head && isValue tail
  | .list _, _ =>
      false
  | .arrow _ _, .lam _ _ =>
      true
  | .arrow _ _, .recE _ _ _ =>
      true
  | .arrow _ _, _ =>
      false

end TExpr

end Determinize
