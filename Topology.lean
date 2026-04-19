import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Support
import Syntax
import Monad
import Skeleton
import TypeSystem

namespace Slice

open MeasureTheory ProbabilityTheory
open scoped Topology

-- For μ >>= f, f is measurable.
-- Measurable lemmas
-- Each f is a measurable function.
lemma let_wrap_measurable (x : String) (e2 : Expr) :
    Measurable (fun g : Expr => Expr.letE x g e2) := by
  sorry

lemma if_wrap_measurable (e2 e3 : Expr) :
    Measurable (fun g : Expr => Expr.ifE g e2 e3) := by
  sorry

lemma lt_left_wrap_measurable (e2 : Expr) :
    Measurable (fun g : Expr => Expr.lt g e2) := by
  sorry

lemma lt_right_wrap_measurable (v1 : ℝ) :
    Measurable (fun g : Expr => Expr.lt (.const v1) g) := by
  sorry

lemma uniform_left_wrap_measurable (e2 : Expr) :
    Measurable (fun g : Expr => Expr.uniform g e2) := by
  sorry

lemma uniform_right_wrap_measurable (v1 : ℝ) :
    Measurable (fun g : Expr => Expr.uniform (.const v1) g) := by
  sorry

lemma const_wrap_measurable :
    Measurable (fun r : ℝ => Expr.const r) := by
  sorry

lemma finconst_wrap_measurable (n : Nat) :
    Measurable (fun i : Fin n => Expr.finconst n i) := by
  sorry

end Slice
