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

/-- The n step distribution restricted to values. -/
noncomputable def valueDistAt {τ : Ty} (n : ℕ) (e : TExpr τ) : Dist (Val τ) :=
  Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n e)

/-- Expected value of the `n`-step semantics, restricted to values.
Mass on non-value expressions is ignored by the comap to `Val`. -/
noncomputable def expectedFloatAt {m : Mode} (n : ℕ) (e : TExpr (.float m)) : ℝ :=
  ∫ v, floatVal v ∂(valueDistAt n e)

/-- Values do not take computational steps. -/
lemma step_value {τ : Ty} (v : TExpr τ) (hv : isValue v = true) :
    step v = Dist.ret v := by
  cases τ <;> cases v <;>
    simp [step, isValue, unitValue?, boolValue?, floatValue?] at hv ⊢

lemma nstep_value_absorbing {τ : Ty} (v : TExpr τ)
    (hv : isValue v = true) (n : ℕ) :
    nstep n v = Dist.ret v := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [nstep, ih, Dist.bind_is_measure_bind, Dist.ret_is_dirac, Measure.dirac_bind]
      · exact step_value v hv
      · exact (by fun_prop : Measurable (step : TExpr τ → Dist (TExpr τ)))

/-- A syntactic upper bound on the number of small steps needed before all
terminating mass of a loop-free expression has reached values.

The constants are intentionally conservative. This is a proof device, not an
operational cost model. -/
def evalDepth : {τ : Ty} → TExpr τ → ℕ
  | _, .var _ =>
      0
  | _, .unitE =>
      0
  | _, .const _ =>
      0
  | _, .trueE =>
      0
  | _, .falseE =>
      0
  | _, .letE _ e1 e2 =>
      evalDepth e1 + evalDepth e2 + 1
  | _, .lt e1 e2 _ _ =>
      evalDepth e1 + evalDepth e2 + 1
  | _, .add e1 e2 _ _ =>
      evalDepth e1 + evalDepth e2 + 1
  | _, .mulG e1 e2 _ _ =>
      evalDepth e1 + evalDepth e2 + 1
  | _, .mulConstL _ e _ _ =>
      evalDepth e + 1
  | _, .mulConstR e _ _ _ =>
      evalDepth e + 1
  | _, .div e1 e2 _ _ =>
      evalDepth e1 + evalDepth e2 + 1
  | _, .ifE c t f =>
      evalDepth c + max (evalDepth t) (evalDepth f) + 1
  | _, .uniform e1 e2 _ _ =>
      evalDepth e1 + evalDepth e2 + 1
  | _, .gaussian e1 e2 _ _ =>
      evalDepth e1 + evalDepth e2 + 1
  | _, .poisson e _ =>
      evalDepth e + 1
  | _, .exponential e _ =>
      evalDepth e + 1
  | _, .beta e1 e2 _ _ =>
      evalDepth e1 + evalDepth e2 + 1
  | _, .gamma e1 e2 _ _ =>
      evalDepth e1 + evalDepth e2 + 1
  | _, .subsume e _ =>
      evalDepth e + 1

/-- After `evalDepth e`, the finite-step value-only expectation has stabilized
to the big-step expected value.

This is the loop-free bridge from small-step approximants to the accumulated
big-step semantics. It is the theorem that would become a convergence theorem
once unbounded loops are added. -/
theorem expectedFloatAt_eq_expectedFloat_of_evalDepth
    {m : Mode} (e : TExpr (.float m)) :
    ∀ n ≥ evalDepth e, expectedFloatAt n e = expectedFloat e := by
  sorry

theorem expectedFloatAt_eventually_const {m : Mode} (e : TExpr (.float m)) :
    ∃ L N, ∀ n ≥ N, expectedFloatAt n e = L := by
  exact ⟨expectedFloat e, evalDepth e, expectedFloatAt_eq_expectedFloat_of_evalDepth e⟩

/-- Small-step formulation of determinization soundness for the current
loop-free language: the value-only finite-step expected values of `e` and
`det e` may have different intermediate plateaus, but their tails are
eventually constant at the same expected value. -/
theorem det_sound_eventual_expectedFloatAt {m : Mode} (e : TExpr (.float m)) :
    ∃ L N M,
      (∀ n ≥ N, expectedFloatAt n e = L) ∧
      (∀ k ≥ M, expectedFloatAt k (det e) = L) := by
  sorry

/-- Main determinization soundness theorem: determinization preserves the
expected value of float expressions. -/
theorem det_sound {m : Mode} (e : TExpr (.float m)) :
    expectedFloat e = expectedFloat (det e) := by
  rcases det_sound_eventual_expectedFloatAt e with ⟨L, N, M, hleft, hright⟩
  let n := max N (evalDepth e)
  let k := max M (evalDepth (det e))
  have hnN : N ≤ n := Nat.le_max_left N (evalDepth e)
  have hnDepth : evalDepth e ≤ n := Nat.le_max_right N (evalDepth e)
  have hkM : M ≤ k := Nat.le_max_left M (evalDepth (det e))
  have hkDepth : evalDepth (det e) ≤ k := Nat.le_max_right M (evalDepth (det e))
  have heAt : expectedFloatAt n e = expectedFloat e :=
    expectedFloatAt_eq_expectedFloat_of_evalDepth e n hnDepth
  have hdetAt : expectedFloatAt k (det e) = expectedFloat (det e) :=
    expectedFloatAt_eq_expectedFloat_of_evalDepth (det e) k hkDepth
  calc
    expectedFloat e = expectedFloatAt n e := heAt.symm
    _ = L := hleft n hnN
    _ = expectedFloatAt k (det e) := (hright k hkM).symm
    _ = expectedFloat (det e) := hdetAt

end TExpr

end Determinize
