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

/-- Finite-step continuation form of determinization soundness.

The theorem is stated only in terms of `nstep` approximants. It does not choose
or compute a syntactic stabilization depth: it only asserts that the two
finite-step tails eventually agree at the same continuation expectation. -/
theorem det_sound_continuation {τ : Ty} (e : TExpr τ)
    (K : Val τ → Dist ℝ) (hK : RespectsExpectedEquiv K) :
    ∃ L N M,
      (∀ n ≥ N, expectedBindAt n e K = L) ∧
      (∀ k ≥ M, expectedBindAt k (det e) K = L) := by
  induction e with
  | var x =>
      sorry
  | unitE =>
      sorry
  | const c =>
      sorry
  | trueE =>
      sorry
  | falseE =>
      sorry
  | letE x e1 e2 ih1 ih2 =>
      -- Needs compositional finite-step lemmas for `let`, plus a lemma saying
      -- the substituted body induces a continuation that respects equivalence.
      sorry
  | lt e1 e2 h1 h2 ih1 ih2 =>
      -- Needs compositional big-step lemmas for left-to-right evaluation of
      -- comparisons. Since both operands are `Float G`, the IHs provide
      -- distribution equality for the operand semantics.
      sorry
  | add e1 e2 h1 h2 ih1 ih2 =>
      -- Needs the compositional rule for addition. The `Float E` result case
      -- uses linearity of expectation; the `Float G` result case uses equality
      -- of operand distributions.
      sorry
  | mulG e1 e2 h1 h2 ih1 ih2 =>
      -- Both operands must be `Float G`; use the IHs at distribution equality
      -- plus compositionality of multiplication.
      sorry
  | mulConstL c e h1 h2 ih =>
      -- The `Float E` case uses scaling of expected values; the `Float G` case
      -- uses equality of the operand distribution.
      sorry
  | mulConstR e c h1 h2 ih =>
      -- Same proof shape as `mulConstL`.
      sorry
  | div e1 e2 h1 h2 ih1 ih2 =>
      -- The denominator is `Float G`, so the non-linear dependence is kept in
      -- distribution equality; the numerator may be handled by expectation.
      sorry
  | ifE c t f ihc iht ihf =>
      -- Needs the compositional rule for conditionals. The condition is `Bool`,
      -- so the IH gives distribution equality over branches.
      sorry
  | uniform e1 e2 h1 h2 ih1 ih2 =>
      -- For result mode `G`, determinization preserves `uniform` and the IHs
      -- give operand distribution equality. For result mode `E`, this is the
      -- primitive moment law `E[Uniform a b] = (a + b) / 2`, combined with the
      -- operand IHs.
      sorry
  | gaussian e1 e2 h1 h2 ih1 ih2 =>
      -- For result mode `E`, this uses `E[Gaussian μ σ] = μ`; for result mode
      -- `G`, it uses preservation of the primitive sampler plus operand IHs.
      sorry
  | poisson e h ih =>
      -- For result mode `E`, this uses `E[Poisson λ] = λ`; for result mode
      -- `G`, it uses preservation of the primitive sampler plus the operand IH.
      sorry
  | exponential e h ih =>
      -- For result mode `E`, this uses `E[Exponential λ] = 1 / λ`; the input is
      -- `Float G`, so the IH gives equality of its full distribution.
      sorry
  | beta e1 e2 h1 h2 ih1 ih2 =>
      -- For result mode `E`, this uses `E[Beta a b] = a / (a + b)`; both
      -- parameters are `Float G`.
      sorry
  | gamma e1 e2 h1 h2 ih1 ih2 =>
      -- For result mode `E`, this uses `E[Gamma k θ] = k / θ` in the convention
      -- encoded by `det`; the second parameter is `Float G`.
      sorry
  | subsume e h ih =>
      -- Needs a compositional lemma for subsumption and a proof that subsuming a
      -- value transports the corresponding observation equivalence.
      sorry

/-- The eventual finite-step continuation theorem can be lifted to `sem` once
the finite approximants are connected to the `iSup` semantics. -/
theorem det_sound_continuation_sem {τ : Ty} (e : TExpr τ)
    (K : Val τ → Dist ℝ) (hK : RespectsExpectedEquiv K) :
    expectedBind (sem e) K = expectedBind (sem (det e)) K := by
  sorry

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
  calc
    expectedFloat e = expectedBind (sem e) K :=
      hleft
    _ = expectedBind (sem (det e)) K :=
      det_sound_continuation_sem e K hK
    _ = expectedFloat (det e) :=
      hright.symm

end TExpr

end Determinize
