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

/-- Deterministic evaluation used by the stuttering semantics. It collapses
pure deterministic work introduced by determinization, while leaving stochastic
samplers to the ordinary small-step semantics. -/
noncomputable def deterministicEval? : {τ : Ty} → TExpr τ → Option (TExpr τ)
  | _, .var _ =>
      none
  | _, .unitE =>
      some .unitE
  | _, .const c =>
      some (.const c)
  | _, .trueE =>
      some .trueE
  | _, .falseE =>
      some .falseE
  | _, .letE _ _ _ =>
      none
  | _, .lt e1 e2 _ _ =>
      match deterministicEval? e1, deterministicEval? e2 with
      | some v1, some v2 =>
          match floatValue? v1, floatValue? v2 with
          | some r1, some r2 =>
              if r1 < r2 then some .trueE else some .falseE
          | _, _ =>
              none
      | _, _ =>
          none
  | .float m, .add e1 e2 _ _ =>
      match deterministicEval? e1, deterministicEval? e2 with
      | some v1, some v2 =>
          match floatValue? v1, floatValue? v2 with
          | some r1, some r2 =>
              some (.const (m := m) (r1 + r2))
          | _, _ =>
              none
      | _, _ =>
          none
  | .float m, .mulG e1 e2 _ _ =>
      match deterministicEval? e1, deterministicEval? e2 with
      | some v1, some v2 =>
          match floatValue? v1, floatValue? v2 with
          | some r1, some r2 =>
              some (.const (m := m) (r1 * r2))
          | _, _ =>
              none
      | _, _ =>
          none
  | .float m, .mulConstL c e _ _ =>
      match deterministicEval? e with
      | some v =>
          match floatValue? v with
          | some r =>
              some (.const (m := m) (c * r))
          | none =>
              none
      | none =>
          none
  | .float m, .mulConstR e c _ _ =>
      match deterministicEval? e with
      | some v =>
          match floatValue? v with
          | some r =>
              some (.const (m := m) (r * c))
          | none =>
              none
      | none =>
          none
  | .float m, .div e1 e2 _ _ =>
      match deterministicEval? e1, deterministicEval? e2 with
      | some v1, some v2 =>
          match floatValue? v1, floatValue? v2 with
          | some r1, some r2 =>
              some (.const (m := m) (r1 / r2))
          | _, _ =>
              none
      | _, _ =>
          none
  | _, .ifE c t f =>
      match deterministicEval? c with
      | some v =>
          match boolValue? v with
          | some true =>
              deterministicEval? t
          | some false =>
              deterministicEval? f
          | none =>
              none
      | none =>
          none
  | _, .uniform _ _ _ _ =>
      none
  | _, .gaussian _ _ _ _ =>
      none
  | _, .poisson _ _ =>
      none
  | _, .exponential _ _ =>
      none
  | _, .beta _ _ _ _ =>
      none
  | _, .gamma _ _ _ _ =>
      none
  | _, .subsume e h =>
      match deterministicEval? e with
      | some v =>
          subsumedValue? v h
      | none =>
          none

/-- One stuttering step for determinized expressions. If deterministic work can
be collapsed to a value, do it in one logical step; otherwise use the ordinary
small-step semantics. -/
noncomputable def stutterStep {τ : Ty} (e : TExpr τ) : Dist (TExpr τ) :=
  match deterministicEval? e with
  | some v =>
      Dist.ret v
  | none =>
      step e

/-- The determinized-side `n`-step semantics using stuttering steps. -/
noncomputable def stutterNstep {τ : Ty} : Nat → TExpr τ → Dist (TExpr τ)
  | 0, e =>
      Dist.ret e
  | n + 1, e =>
      Dist.bind (stutterNstep n e) (fun e' => stutterStep e')

/-- The stuttered `n`-step distribution restricted to values. -/
noncomputable def stutterValueDistAt {τ : Ty} (n : ℕ) (e : TExpr τ) :
    Dist (Val τ) :=
  Measure.comap (Subtype.val : Val τ → TExpr τ) (stutterNstep n e)

/-- Continuation expectation against the stuttered value-only `n`-step
approximant. -/
noncomputable def expectedStutterBindAt {τ : Ty} (n : ℕ) (e : TExpr τ)
    (K : Val τ → Dist ℝ) : ℝ :=
  expectedBind (stutterValueDistAt n e) K

private abbrev ContinuationSoundAt {τ : Ty} (e : TExpr τ) : Prop :=
  ∀ n : ℕ,
  ∀ K : Val τ → Dist ℝ,
    RespectsExpectedEquiv K →
      expectedStutterBindAt n e K = expectedStutterBindAt n (det e) K

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

/-- If `det e = e`, the lockstep stuttering statement is immediate. -/
lemma det_sound_continuation_self {τ : Ty} (e : TExpr τ)
    (hdet : det e = e) :
    ContinuationSoundAt e := by
  intro n K _hK
  rw [hdet]

private theorem det_sound_continuation_let_case {τ1 τ2 : Ty}
    (x : String) (e1 : TExpr τ1) (e2 : TExpr τ2)
    (ih1 : ContinuationSoundAt e1) (ih2 : ContinuationSoundAt e2) :
    ContinuationSoundAt (.letE x e1 e2) := by
  sorry

private theorem det_sound_continuation_lt_case {m1 m2 : Mode}
    (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2))
    (h1 : m1 ≼ .G) (h2 : m2 ≼ .G)
    (ih1 : ContinuationSoundAt e1) (ih2 : ContinuationSoundAt e2) :
    ContinuationSoundAt (.lt e1 e2 h1 h2) := by
  sorry

private theorem det_sound_continuation_add_case {m1 m2 m : Mode}
    (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2))
    (h1 : m1 ≼ m) (h2 : m2 ≼ m)
    (ih1 : ContinuationSoundAt e1) (ih2 : ContinuationSoundAt e2) :
    ContinuationSoundAt (.add (m := m) e1 e2 h1 h2) := by
  sorry

private theorem det_sound_continuation_mulG_case {m1 m2 m : Mode}
    (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2))
    (h1 : m1 ≼ .G) (h2 : m2 ≼ .G)
    (ih1 : ContinuationSoundAt e1) (ih2 : ContinuationSoundAt e2) :
    ContinuationSoundAt (.mulG (m := m) e1 e2 h1 h2) := by
  sorry

private theorem det_sound_continuation_mulConstL_case {m1 m2 m : Mode}
    (c : ℝ) (e : TExpr (.float m2))
    (h1 : m1 ≼ m) (h2 : m2 ≼ m)
    (ih : ContinuationSoundAt e) :
    ContinuationSoundAt (.mulConstL (m1 := m1) (m := m) c e h1 h2) := by
  sorry

private theorem det_sound_continuation_mulConstR_case {m1 m2 m : Mode}
    (e : TExpr (.float m1)) (c : ℝ)
    (h1 : m1 ≼ m) (h2 : m2 ≼ m)
    (ih : ContinuationSoundAt e) :
    ContinuationSoundAt (.mulConstR (m2 := m2) (m := m) e c h1 h2) := by
  sorry

private theorem det_sound_continuation_div_case {m1 m2 m : Mode}
    (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2))
    (h1 : m1 ≼ m) (h2 : m2 ≼ .G)
    (ih1 : ContinuationSoundAt e1) (ih2 : ContinuationSoundAt e2) :
    ContinuationSoundAt (.div (m := m) e1 e2 h1 h2) := by
  sorry

private theorem det_sound_continuation_if_case {τ : Ty}
    (c : TExpr .bool) (t f : TExpr τ)
    (ihc : ContinuationSoundAt c) (iht : ContinuationSoundAt t)
    (ihf : ContinuationSoundAt f) :
    ContinuationSoundAt (.ifE c t f) := by
  sorry

private theorem det_sound_continuation_uniform_case {m1 m2 m : Mode}
    (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2))
    (h1 : m1 ≼ m) (h2 : m2 ≼ m)
    (ih1 : ContinuationSoundAt e1) (ih2 : ContinuationSoundAt e2) :
    ContinuationSoundAt (.uniform (m := m) e1 e2 h1 h2) := by
  sorry

private theorem det_sound_continuation_gaussian_case {m1 m2 m : Mode}
    (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2))
    (h1 : m1 ≼ m) (h2 : m2 ≼ .G)
    (ih1 : ContinuationSoundAt e1) (ih2 : ContinuationSoundAt e2) :
    ContinuationSoundAt (.gaussian (m := m) e1 e2 h1 h2) := by
  sorry

private theorem det_sound_continuation_poisson_case {m1 m : Mode}
    (e : TExpr (.float m1)) (h : m1 ≼ m)
    (ih : ContinuationSoundAt e) :
    ContinuationSoundAt (.poisson (m := m) e h) := by
  sorry

private theorem det_sound_continuation_exponential_case {m1 m : Mode}
    (e : TExpr (.float m1)) (h : m1 ≼ .G)
    (ih : ContinuationSoundAt e) :
    ContinuationSoundAt (.exponential (m := m) e h) := by
  sorry

private theorem det_sound_continuation_beta_case {m1 m2 m : Mode}
    (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2))
    (h1 : m1 ≼ .G) (h2 : m2 ≼ .G)
    (ih1 : ContinuationSoundAt e1) (ih2 : ContinuationSoundAt e2) :
    ContinuationSoundAt (.beta (m := m) e1 e2 h1 h2) := by
  sorry

private theorem det_sound_continuation_gamma_case {m1 m2 m : Mode}
    (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2))
    (h1 : m1 ≼ m) (h2 : m2 ≼ .G)
    (ih1 : ContinuationSoundAt e1) (ih2 : ContinuationSoundAt e2) :
    ContinuationSoundAt (.gamma (m := m) e1 e2 h1 h2) := by
  sorry

private theorem det_sound_continuation_subsume_case {τ1 τ2 : Ty}
    (e : TExpr τ1) (h : τ1 <: τ2)
    (ih : ContinuationSoundAt e) :
    ContinuationSoundAt (.subsume e h) := by
  sorry

/-- Lockstep finite-step continuation form of determinization soundness.

Both expressions use `stutterNstep`, so deterministic work introduced by either
side is counted as one logical step. -/
theorem det_sound_continuation {τ : Ty} (e : TExpr τ)
    (n : ℕ) (K : Val τ → Dist ℝ) (hK : RespectsExpectedEquiv K) :
    expectedStutterBindAt n e K = expectedStutterBindAt n (det e) K := by
  revert hK
  revert K
  revert n
  change ContinuationSoundAt e
  induction e with
  | var x =>
      exact det_sound_continuation_self _ rfl
  | unitE =>
      exact det_sound_continuation_self .unitE rfl
  | const c =>
      exact det_sound_continuation_self (.const c) rfl
  | trueE =>
      exact det_sound_continuation_self .trueE rfl
  | falseE =>
      exact det_sound_continuation_self .falseE rfl
  | letE x e1 e2 ih1 ih2 =>
      exact det_sound_continuation_let_case x e1 e2 ih1 ih2
  | lt e1 e2 h1 h2 ih1 ih2 =>
      exact det_sound_continuation_lt_case e1 e2 h1 h2 ih1 ih2
  | add e1 e2 h1 h2 ih1 ih2 =>
      exact det_sound_continuation_add_case e1 e2 h1 h2 ih1 ih2
  | mulG e1 e2 h1 h2 ih1 ih2 =>
      exact det_sound_continuation_mulG_case e1 e2 h1 h2 ih1 ih2
  | mulConstL c e h1 h2 ih =>
      exact det_sound_continuation_mulConstL_case c e h1 h2 ih
  | mulConstR e c h1 h2 ih =>
      exact det_sound_continuation_mulConstR_case e c h1 h2 ih
  | div e1 e2 h1 h2 ih1 ih2 =>
      exact det_sound_continuation_div_case e1 e2 h1 h2 ih1 ih2
  | ifE c t f ihc iht ihf =>
      exact det_sound_continuation_if_case c t f ihc iht ihf
  | uniform e1 e2 h1 h2 ih1 ih2 =>
      exact det_sound_continuation_uniform_case e1 e2 h1 h2 ih1 ih2
  | gaussian e1 e2 h1 h2 ih1 ih2 =>
      exact det_sound_continuation_gaussian_case e1 e2 h1 h2 ih1 ih2
  | poisson e h ih =>
      exact det_sound_continuation_poisson_case e h ih
  | exponential e h ih =>
      exact det_sound_continuation_exponential_case e h ih
  | beta e1 e2 h1 h2 ih1 ih2 =>
      exact det_sound_continuation_beta_case e1 e2 h1 h2 ih1 ih2
  | gamma e1 e2 h1 h2 ih1 ih2 =>
      exact det_sound_continuation_gamma_case e1 e2 h1 h2 ih1 ih2
  | subsume e h ih =>
      exact det_sound_continuation_subsume_case e h ih

/-- The lockstep finite-step continuation theorem can be lifted to `sem` once
the stuttered finite approximants are connected to the `iSup` semantics. -/
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
