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

lemma extend_shadow (Γ : Ctx) (x : String) (τ τ' : Ty) :
    Ctx.extend (Ctx.extend Γ x τ) x τ' = Ctx.extend Γ x τ' := by
  funext y
  by_cases h : y = x <;> simp [Ctx.extend, h]

lemma extend_comm (Γ : Ctx) (x y : String) (τx τy : Ty) (hxy : x ≠ y) :
    Ctx.extend (Ctx.extend Γ x τx) y τy =
      Ctx.extend (Ctx.extend Γ y τy) x τx := by
  funext z
  by_cases hz : z = y
  · subst hz
    have hxz : z ≠ x := by simpa using (Ne.symm hxy)
    simp [Ctx.extend, hxz]
  · by_cases hxz : z = x
    · subst hxz
      simp [Ctx.extend, hxy]
    · simp [Ctx.extend, hz, hxz]

end Ctx

/-- Context inclusion for renaming/weakening style arguments. -/
def CtxSub (Γ Γ' : Ctx) : Prop :=
  ∀ x τ, Γ x = some τ → Γ' x = some τ

lemma CtxSub.extend {Γ Γ' : Ctx} (h : CtxSub Γ Γ') (x : String) (τ : Ty) :
    CtxSub (Ctx.extend Γ x τ) (Ctx.extend Γ' x τ) := by
  intro y τy hy
  by_cases hxy : y = x
  · subst hxy
    have : τ = τy := by simpa [Ctx.extend] using hy
    simpa [Ctx.extend, this]
  · have hyΓ : Γ y = some τy := by simpa [Ctx.extend, hxy] using hy
    have hyΓ' : Γ' y = some τy := h y τy hyΓ
    simpa [Ctx.extend, hxy, hyΓ']

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

  | discrete {Γ : Ctx} {d : DiscreteParam} :
      HasType Γ (.discrete d) (.fin (discreteProbsOf d).1.length)

  | diverge {Γ : Ctx} {τ : Ty} :
      HasType Γ .diverge τ

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
def TExpr (τ : Ty) : Type :=
  {e : Expr // HasType Ctx.empty e τ}

lemma hasType_weaken {Γ Γ' : Ctx} {e : Expr} {τ : Ty}
    (hsub : CtxSub Γ Γ')
    (he : HasType Γ e τ) :
    HasType Γ' e τ := by
  induction he generalizing Γ' with
  | var hx =>
      exact HasType.var (hsub _ _ hx)
  | const =>
      exact HasType.const
  | trueE =>
      exact HasType.trueE
  | falseE =>
      exact HasType.falseE
  | finconst k =>
      exact HasType.finconst k
  | discrete =>
      exact HasType.discrete
  | diverge =>
      exact HasType.diverge
  | letE h1 h2 ih1 ih2 =>
      exact HasType.letE
        (ih1 hsub)
        (ih2 (CtxSub.extend hsub _ _))
  | lt h1 h2 ih1 ih2 =>
      exact HasType.lt (ih1 hsub) (ih2 hsub)
  | ifE hc ht hf ihc iht ihf =>
      exact HasType.ifE (ihc hsub) (iht hsub) (ihf hsub)
  | uniform h1 h2 ih1 ih2 =>
      exact HasType.uniform (ih1 hsub) (ih2 hsub)

lemma hasType_of_empty {e : Expr} {τ : Ty}
    (he : HasType Ctx.empty e τ) (Γ : Ctx) :
    HasType Γ e τ := by
  refine hasType_weaken (Γ := Ctx.empty) (Γ' := Γ) ?_ he
  intro y τy hy
  simpa [Ctx.empty] using hy

/-- Substitution preserves typing.
We restrict to substitution by closed terms in order to avoid the need to rename bound variables. -/
lemma subst_preserves_type {Γ : Ctx} {x : String} {v e : Expr} {τ τ2 : Ty}
    (hv : HasType Ctx.empty v τ)
    (he : HasType (Ctx.extend Γ x τ) e τ2) :
    HasType Γ (subst x v e) τ2 := by
  have haux :
      ∀ {Δ Γ : Ctx} {x : String} {e : Expr} {τ2 : Ty},
        HasType Δ e τ2 →
        Δ = Ctx.extend Γ x τ →
        HasType Γ (subst x v e) τ2 := by
    intro Δ Γ x e τ2 he hΔ
    induction he generalizing Γ x with
    | var hx =>
        subst hΔ
        rename_i y τy
        by_cases hxy : x = y
        · subst hxy
          have hτ : τ = τy := by simpa [Ctx.extend] using hx
          simpa [Slice.subst] using (hτ ▸ hasType_of_empty hv Γ)
        · have hyx : y ≠ x := by intro hy; exact hxy hy.symm
          have hy : Γ y = some τy := by simpa [Ctx.extend, hyx] using hx
          simpa [Slice.subst, hxy] using (HasType.var hy)
    | const =>
        subst hΔ
        simpa [Slice.subst] using (HasType.const (Γ := Γ))
    | trueE =>
        subst hΔ
        simpa [Slice.subst] using (HasType.trueE (Γ := Γ))
    | falseE =>
        subst hΔ
        simpa [Slice.subst] using (HasType.falseE (Γ := Γ))
    | finconst k =>
        subst hΔ
        simpa [Slice.subst] using (HasType.finconst (Γ := Γ) k)
    | discrete =>
        subst hΔ
        rename_i d
        simpa [Slice.subst] using (HasType.discrete (Γ := Γ) (d := d))
    | diverge =>
        subst hΔ
        rename_i τ'
        simpa [Slice.subst] using (HasType.diverge (Γ := Γ) (τ := τ'))
    | letE h1 h2 ih1 ih2 =>
        subst hΔ
        rename_i y e1 e2 τ1 τ2
        by_cases hxy : x = y
        · have h1' : HasType Γ (subst x v e1) τ1 :=
            ih1 (Γ := Γ) (x := x) rfl
          have h2' : HasType (Ctx.extend Γ y τ1) e2 τ2 := by
            subst hxy
            simpa [Ctx.extend_shadow] using h2
          simpa [Slice.subst, hxy] using (HasType.letE h1' h2')
        · have h1' : HasType Γ (subst x v e1) τ1 :=
            ih1 (Γ := Γ) (x := x) rfl
          have h2' : HasType (Ctx.extend Γ y τ1) (subst x v e2) τ2 :=
            ih2
              (Γ := Ctx.extend Γ y τ1)
              (x := x)
              (Ctx.extend_comm Γ x y τ τ1 hxy)
          simpa [Slice.subst, hxy] using (HasType.letE h1' h2')
    | lt h1 h2 ih1 ih2 =>
        subst hΔ
        simpa [Slice.subst] using
          (HasType.lt
            (ih1 (Γ := Γ) (x := x) rfl)
            (ih2 (Γ := Γ) (x := x) rfl))
    | ifE hc ht hf ihc iht ihf =>
        subst hΔ
        simpa [Slice.subst] using
          (HasType.ifE
            (ihc (Γ := Γ) (x := x) rfl)
            (iht (Γ := Γ) (x := x) rfl)
            (ihf (Γ := Γ) (x := x) rfl))
    | uniform h1 h2 ih1 ih2 =>
        subst hΔ
        simpa [Slice.subst] using
          (HasType.uniform
            (ih1 (Γ := Γ) (x := x) rfl)
            (ih2 (Γ := Γ) (x := x) rfl))
  exact haux he rfl

end Slice
