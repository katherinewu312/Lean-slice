import Determinize.BigStep
import Determinize.Determinization
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

/-- Main determinization soundness theorem: determinization preserves the
expected value of float expressions. -/
theorem det_sound {m : Mode} (e : TExpr (.float m)) :
    expectedFloat e = expectedFloat (det e) := by sorry

end TExpr

end Determinize
