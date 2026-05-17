import Determinize.BigStep
import Determinize.Determinization
import Determinize.SymbolicStep
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace Determinize

open MeasureTheory
open scoped ENNReal

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

/-- The n step distribution restricted to values. -/
noncomputable def valueDistAt {τ : Ty} (n : ℕ) (e : TExpr τ) : Dist (Val τ) :=
  Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n e)

/-- Expected value of the `n`-step semantics, restricted to values.
Mass on non-value expressions is ignored by the comap to `Val`. -/
noncomputable def expectedFloatAt {m : Mode} (n : ℕ) (e : TExpr (.float m)) : ℝ :=
  ∫ v, floatVal v ∂(valueDistAt n e)

/-- Reachable-step actual coupling: interpreting `n + 1` symbolic steps actually
is the same as interpreting `n` symbolic steps actually and then taking one
ordinary step. -/
theorem actual_symbolicNstep_succ {τ : Ty} (n : ℕ) (e : TExpr τ) :
    actual (symbolicNstep (n + 1) (symbolicInitial e)) =
      Dist.bind (actual (symbolicNstep n (symbolicInitial e))) step := by
  sorry

/-- The actual interpretation of symbolic `n`-step semantics recovers the
ordinary `n`-step semantics.

Proof structure:
* Base case: interpreting zero symbolic steps gives `return e`, matching
  `nstep 0 e`.
* Successor case: use `actual_symbolicNstep_succ` to rewrite the actual
  interpretation of `n + 1` symbolic steps as one ordinary step after the
  actual interpretation of `n` symbolic steps, then apply the induction
  hypothesis and unfold `nstep`.

Base:
actual(symstep_0(e)) = step_0(e)

Step:
assuming actual(symstep_n(e)) = step_n(e) by the inductive step,
actual(symstep_{n+1}(e))
= actual(symstep_n(e)) >>= step (by the above lemma)
= step_n(e) >>= step
= step_{n+1}(e)
 -/
theorem actual_symbolicNstep_eq_nstep {τ : Ty} (n : ℕ) (e : TExpr τ) :
    actual (symbolicNstep n (symbolicInitial e)) = nstep n e := by
  induction n with
  | zero =>
      rw [symbolicNstep, nstep]
      unfold actual symbolicInitial actualState actualWithSigma actualExpr Dist.ret Dist.bind
      rw [Measure.dirac_bind (by fun_prop)]
  | succ n ih =>
      rw [actual_symbolicNstep_succ, ih, nstep]

/-- The expected interpretation of symbolic `n`-step semantics recovers the
`n`-step semantics of the determinized program. -/
theorem expected_symbolicNstep_eq_det_nstep {τ : Ty} (n : ℕ) (e : TExpr τ) :
    expected (symbolicNstep n (symbolicInitial e)) = nstep n (det e) := by
  sorry
  -- NOTE: since det currently expands means into arithmetic expressions, the exact same-step equality may need auxiliary normalization or step-count alignment when we prove it.

/-- Main determinization soundness theorem: determinization preserves the
expected value of float expressions. -/
theorem det_sound {m : Mode} (e : TExpr (.float m)) :
    expectedFloat e = expectedFloat (det e) := by sorry

end TExpr

end Determinize
