import Determinize.BigStep
import Determinize.Determinization
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Determinize

open MeasureTheory

namespace TExpr

/-- Read the real number out of a float value. Non-value cases are unreachable
for elements of `Val (.float m)`. -/
def floatVal {m : Mode} (v : Val (.float m)) : ℝ :=
  match (v : TExpr (.float m)) with
  | .const c =>
      c
  | _ =>
      0

/-- Expected value of the big-step semantics of a float expression. -/
noncomputable def expectedFloat {m : Mode} (e : TExpr (.float m)) : ℝ :=
  ∫ v, floatVal v ∂(sem e)

/-- Expected value of a real-valued distribution. -/
noncomputable def expectedReal (μ : Dist ℝ) : ℝ :=
  ∫ r, r ∂μ

/-- Expected value of a distribution over float values. -/
noncomputable def expectedFloatDist {m : Mode} (μ : Dist (Val (.float m))) : ℝ :=
  ∫ v, floatVal v ∂μ

/-- Semantic equivalence of distributions at a type.

At `Float E`, only the expected float observation is compared. At `Float G`,
`Bool`, and `Unit`, the whole value distribution is compared. Product types are
not present in the current `Ty` language; when they are added, their case should
compare the projected distributions structurally. -/
noncomputable def ExpectedEquiv : (τ : Ty) → Dist (Val τ) → Dist (Val τ) → Prop
  | .float .E, μ, ν =>
      expectedFloatDist μ = expectedFloatDist ν
  | .float .G, μ, ν =>
      μ = ν
  | .bool, μ, ν =>
      μ = ν
  | .unit, μ, ν =>
      μ = ν

notation "Eqv[" τ "](" μ ", " ν ")" => ExpectedEquiv τ μ ν

/-- Continuation bind followed by real expectation. -/
noncomputable def expectedBind {τ : Ty} (μ : Dist (Val τ)) (K : Val τ → Dist ℝ) : ℝ :=
  expectedReal (Dist.bind μ K)

/-- A continuation respects the observation equivalence at its input type when
equivalent input distributions produce the same real expectation after bind. -/
def RespectsExpectedEquiv {τ : Ty} (K : Val τ → Dist ℝ) : Prop :=
  ∀ μ ν : Dist (Val τ), ExpectedEquiv τ μ ν → expectedBind μ K = expectedBind ν K

/-- The n step distribution restricted to values. -/
noncomputable def valueDistAt {τ : Ty} (n : ℕ) (e : TExpr τ) : Dist (Val τ) :=
  Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n e)

/-- Continuation expectation against the value-only `n`-step approximant. -/
noncomputable def expectedBindAt {τ : Ty} (n : ℕ) (e : TExpr τ)
    (K : Val τ → Dist ℝ) : ℝ :=
  expectedBind (valueDistAt n e) K

/-- Expected value of the `n`-step semantics, restricted to values.
Mass on non-value expressions is ignored by the comap to `Val`. -/
noncomputable def expectedFloatAt {m : Mode} (n : ℕ) (e : TExpr (.float m)) : ℝ :=
  ∫ v, floatVal v ∂(valueDistAt n e)

/-- The typed distribution equivalence is reflexive. -/
theorem expectedEquiv_refl {τ : Ty} (μ : Dist (Val τ)) :
    ExpectedEquiv τ μ μ := by
  cases τ with
  | unit =>
      rfl
  | bool =>
      rfl
  | float m =>
      cases m <;> rfl

/-- The typed distribution equivalence is symmetric. -/
theorem expectedEquiv_symm {τ : Ty} {μ ν : Dist (Val τ)}
    (h : ExpectedEquiv τ μ ν) :
    ExpectedEquiv τ ν μ := by
  cases τ with
  | unit =>
      exact h.symm
  | bool =>
      exact h.symm
  | float m =>
      cases m <;> exact h.symm

/-- The typed distribution equivalence is transitive. -/
theorem expectedEquiv_trans {τ : Ty} {μ ν ξ : Dist (Val τ)}
    (hμν : ExpectedEquiv τ μ ν) (hνξ : ExpectedEquiv τ ν ξ) :
    ExpectedEquiv τ μ ξ := by
  cases τ with
  | unit =>
      exact hμν.trans hνξ
  | bool =>
      exact hμν.trans hνξ
  | float m =>
      cases m <;> exact hμν.trans hνξ

/-- Continuations that respect expected equivalence give equal expectations on
any pair of equivalent value distributions. -/
theorem det_sound_continuation {τ : Ty} (μ₁ μ₂ : Dist (Val τ))
    (K : Val τ → Dist ℝ) (hK : RespectsExpectedEquiv K)
    (hμ : ExpectedEquiv τ μ₁ μ₂) :
    expectedBind μ₁ K = expectedBind μ₂ K := by
  exact hK μ₁ μ₂ hμ

/-- Main determinization soundness theorem: determinization preserves the
expected value of float expressions. -/
theorem det_sound {m : Mode} (e : TExpr (.float m)) :
    expectedFloat e = expectedFloat (det e) := by
  let K : Val (.float m) → Dist ℝ := fun v => Dist.ret (floatVal v)
  have hK : RespectsExpectedEquiv K := by
    sorry
  have hleft : expectedFloat e = expectedBind (sem e) K := by
    sorry
  have hright : expectedFloat (det e) = expectedBind (sem (det e)) K := by
    sorry
  have hsem : ExpectedEquiv (.float m) (sem e) (sem (det e)) := by
    sorry
  calc
    expectedFloat e = expectedBind (sem e) K :=
      hleft
    _ = expectedBind (sem (det e)) K :=
      det_sound_continuation (sem e) (sem (det e)) K hK hsem
    _ = expectedFloat (det e) :=
      hright.symm

end TExpr

end Determinize
