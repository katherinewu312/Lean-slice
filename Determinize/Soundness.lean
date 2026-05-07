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

/-- The expression measurable spaces are discrete in the current model, so the
float observation is measurable. -/
theorem measurable_floatVal {m : Mode} :
    Measurable (@floatVal m) := by
  intro s _hs
  exact ⟨_, by trivial, Set.preimage_image_eq _ Subtype.val_injective⟩

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

/-- Binding the float observation continuation is the same as directly taking
the float expectation. -/
theorem expectedBind_floatVal_ret {m : Mode} (μ : Dist (Val (.float m))) :
    expectedBind μ (fun v => Dist.ret (floatVal v)) = expectedFloatDist μ := by
  unfold expectedBind expectedReal expectedFloatDist Dist.ret
  rw [show (μ.bind fun v => Measure.dirac (floatVal v)) = μ.map floatVal by
    exact Measure.bind_dirac_eq_map μ measurable_floatVal]
  exact integral_map measurable_floatVal.aemeasurable (by fun_prop)

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

/-- Strong continuation form of determinization soundness.

This is the theorem that should be proved by induction. Intuitively, every context/continuation that respects
the observation equivalence cannot distinguish `e` from `det e`.
-/
theorem det_sound_cps {τ : Ty} (e : TExpr τ) :
    ∀ K : Val τ → Dist ℝ,
      RespectsExpectedEquiv K →
      expectedBind (sem e) K = expectedBind (sem (det e)) K := by
  induction e with
  | var x =>
      intro K hK
      simp [det]

  | unitE =>
      intro K hK
      simp [det]

  | const c =>
      intro K hK
      simp [det]

  | trueE =>
      intro K hK
      simp [det]

  | falseE =>
      intro K hK
      simp [det]

  | letE x e1 e2 ih1 ih2 =>
      intro K hK
      /-
      Desired proof shape:

      1. Expand the semantics of `let`.
      2. Use `ih1` on `e1`.
      3. The continuation passed to `e1` is the semantics of the body.
      4. Prove that this continuation respects `ExpectedEquiv` using `ih2`.

      This case will probably require a substitution/environment version of
      the induction hypothesis if your `let` semantics substitutes values into
      `e2`.
      -/
      sorry

  | lt e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      cases h1
      cases h2
      /-
      After the mode proofs are eliminated, both operands are `Float G`, so
      `ih1` and `ih2` are strong enough to identify their full value
      distributions.  To finish this branch, we still need the compositional
      big-step law for `lt`: evaluating `lt e1 e2` should be equivalent to
      binding the semantics of `e1`, then the semantics of `e2`, then applying
      the boolean continuation.  That law is not currently available from the
      imported big-step API.
      -/
      sorry

  | add e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      Use linearity of expectation.

      The proof should reduce to:
        E[e1 + e2] = E[e1] + E[e2]
      and then use `ih1` and `ih2`.
      -/
      sorry

  | mulG e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      This should only be sound if the inputs are in a mode where full
      distributional equivalence is available, e.g. Float G.

      If this consumes Float E inputs, this theorem is probably false.
      -/
      sorry

  | mulConstL c e h1 h2 ih =>
      intro K hK
      /-
      Use:
        E[c * e] = c * E[e]
      then use `ih`.
      -/
      sorry

  | mulConstR e c h1 h2 ih =>
      intro K hK
      /-
      Use:
        E[e * c] = E[e] * c
      then use `ih`.
      -/
      sorry

  | div e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      Be careful: this is not expectation-preserving in general.

      In general:
        E[e1 / e2] ≠ E[e1] / E[e2].

      This case should only go through if your typing rule forces enough
      distributional information, for example if both operands are Float G, or
      if division is restricted to constants.
      -/
      sorry

  | ifE c t f ihc iht ihf =>
      intro K hK
      /-
      Proof shape:

      1. Use `ihc` to show the condition is preserved.
      2. Since booleans use full distributional equality in `ExpectedEquiv`,
         the probability of each branch is preserved.
      3. Use `iht` and `ihf` for the branches.
      -/
      sorry

  | uniform e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      For Float E result, use:
        E[uniform(a,b)] = (E[a] + E[b]) / 2

      More precisely, if the endpoints are themselves expressions:
        E[let a = e1 in let b = e2 in uniform(a,b)]
        =
        (E[e1] + E[e2]) / 2

      Then use `ih1` and `ih2`.
      -/
      sorry

  | gaussian e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      If `gaussian(mean, variance)` has expectation `mean`, use:
        E[gaussian(e1,e2)] = E[e1]

      Then use `ih1`.

      The variance argument usually does not affect the expected value, but
      it still must be well-typed/valid.
      -/
      sorry

  | poisson e h ih =>
      intro K hK
      /-
      If `poisson(rate)` has expectation `rate`, use:
        E[poisson(e)] = E[e]
      then use `ih`.
      -/
      sorry

  | exponential e h ih =>
      intro K hK
      /-
      Be careful about parameterization.

      If `exponential(a)` means rate `a`, then:
        E[exponential(a)] = 1 / a

      That is not expectation-preserving under replacing `a` by E[a].

      If `exponential(a)` means mean `a`, then:
        E[exponential(a)] = a

      This case is sound only under the second convention or with stronger
      restrictions.
      -/
      sorry

  | beta e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      Be careful:
        E[beta(a,b)] = a / (a + b)

      This is nonlinear in `a` and `b`, so replacing parameters by expectations
      is not sound in general unless your typing rules force `a` and `b` to be
      distributionally preserved or deterministic.
      -/
      sorry

  | gamma e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      Depends on parameterization.

      Shape/rate:
        E[gamma(a,b)] = a / b

      Shape/scale:
        E[gamma(a,b)] = a * b

      The shape/rate version is nonlinear because of division.
      -/
      sorry

  | subsume e h ih =>
      intro K hK
      /-
      Usually use `ih`, plus a lemma saying subsumption does not change
      semantics except for the observation relation.
      -/
      sorry

/-- Main determinization soundness theorem: determinization preserves the
expected value of float expressions. -/
theorem det_sound {m : Mode} (e : TExpr (.float m)) :
    expectedFloat e = expectedFloat (det e) := by
  let K : Val (.float m) → Dist ℝ :=
    fun v => Dist.ret (floatVal v)
  have hK : RespectsExpectedEquiv K := by
    intro μ ν hμν
    cases m with
    | E =>
        change expectedFloatDist μ = expectedFloatDist ν at hμν
        rw [expectedBind_floatVal_ret, expectedBind_floatVal_ret]
        exact hμν
    | G =>
        unfold ExpectedEquiv at hμν
        subst ν
        rfl
  have hleft : expectedFloat e = expectedBind (sem e) K := by
    exact (expectedBind_floatVal_ret (sem e)).symm
  have hright : expectedFloat (det e) = expectedBind (sem (det e)) K := by
    exact (expectedBind_floatVal_ret (sem (det e))).symm
  calc
    expectedFloat e
        = expectedBind (sem e) K := hleft
    _   = expectedBind (sem (det e)) K := det_sound_cps e K hK
    _   = expectedFloat (det e) := hright.symm

end TExpr

end Determinize
