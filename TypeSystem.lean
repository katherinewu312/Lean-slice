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
      HasType Γ (.discrete ps) (.fin ps.1.length)

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

/-- Well-typed expressions of type τ in the empty context. -/
def ExprsOfType (τ : Ty) : Type :=
  {e : Expr // HasType Ctx.empty e τ}

/-- Inversion lemmas for HasType -/
lemma hasType_letE_inv {Γ : Ctx} {x : String} {e1 e2 : Expr} {τ : Ty}
    (h : HasType Γ (.letE x e1 e2) τ) :
    ∃ τ1, HasType Γ e1 τ1 ∧ HasType (Ctx.extend Γ x τ1) e2 τ := by
  cases h with
  | letE h1 h2 => exact ⟨_, h1, h2⟩

lemma hasType_ifE_inv {Γ : Ctx} {c t f : Expr} {τ : Ty}
    (h : HasType Γ (.ifE c t f) τ) :
    HasType Γ c .bool ∧ HasType Γ t τ ∧ HasType Γ f τ := by
  cases h with
  | ifE hc ht hf => exact ⟨hc, ht, hf⟩

lemma hasType_lt_inv {Γ : Ctx} {e1 e2 : Expr} {τ : Ty}
    (h : HasType Γ (.lt e1 e2) τ) :
    τ = .bool ∧ HasType Γ e1 .real ∧ HasType Γ e2 .real := by
  cases h with
  | lt h1 h2 => exact ⟨rfl, h1, h2⟩

lemma hasType_uniform_inv {Γ : Ctx} {e1 e2 : Expr} {τ : Ty}
    (h : HasType Γ (.uniform e1 e2) τ) :
    τ = .real ∧ HasType Γ e1 .real ∧ HasType Γ e2 .real := by
  cases h with
  | uniform h1 h2 => exact ⟨rfl, h1, h2⟩

/-- Substitution preserves typing -/
lemma subst_preserves_type {Γ : Ctx} {x : String} {v e : Expr} {τ τ2 : Ty}
    (hv : HasType Γ v τ)
    (he : HasType (Ctx.extend Γ x τ) e τ2) :
    HasType Γ (subst x v e) τ2 := by
  sorry

end Slice
