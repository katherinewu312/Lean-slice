import Syntax

namespace Slice

/-- Types for the current Slice expression fragment. -/
inductive Ty where
  | real : Ty
  | bool : Ty
  | fin  : Nat → Ty
deriving DecidableEq, Repr

/-- Typing context: partial map from variable names to types. -/
abbrev Ctx := String → Option Ty

namespace Ctx

/-- Empty typing context. -/
def empty : Ctx := fun _ => none

/-- Extend a context with a single binding `x : τ`. -/
def extend (Γ : Ctx) (x : String) (τ : Ty) : Ctx :=
  fun y => if y = x then some τ else Γ y

end Ctx

/-- Declarative typing judgment. -/
inductive HasType : Ctx → Expr → Ty → Prop where
  | var {Γ : Ctx} {x : String} {τ : Ty} :
      Γ x = some τ →
      HasType Γ (.var x) τ

  | const {Γ : Ctx} {r : ℝ} :
      HasType Γ (.const r) .real

  | trueE {Γ : Ctx} :
      HasType Γ .trueE .bool

  | falseE {Γ : Ctx} :
      HasType Γ .falseE .bool

  | finconst {Γ : Ctx} {n : Nat} (k : Fin n) :
      HasType Γ (.finconst n k) (.fin n)

  | discrete {Γ : Ctx} {ps : DiscreteProbs} :
      HasType Γ (.discrete ps) .real

  | letE {Γ : Ctx} {x : String} {e1 e2 : Expr} {τ1 τ2 : Ty} :
      HasType Γ e1 τ1 →
      HasType (Ctx.extend Γ x τ1) e2 τ2 →
      HasType Γ (.letE x e1 e2) τ2

  | lt {Γ : Ctx} {e1 e2 : Expr} :
      HasType Γ e1 .real →
      HasType Γ e2 .real →
      HasType Γ (.lt e1 e2) .bool

  | ifE {Γ : Ctx} {c t f : Expr} {τ : Ty} :
      HasType Γ c .bool →
      HasType Γ t τ →
      HasType Γ f τ →
      HasType Γ (.ifE c t f) τ

  | uniform {Γ : Ctx} {e1 e2 : Expr} :
      HasType Γ e1 .real →
      HasType Γ e2 .real →
      HasType Γ (.uniform e1 e2) .real

/-- Closed expressions are well-typed if they typecheck in the empty context. -/
def WellTyped (e : Expr) : Prop :=
  ∃ τ, HasType Ctx.empty e τ

end Slice
