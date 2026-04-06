import SmallStep

namespace Slice

open MeasureTheory ProbabilityTheory

#check Measurable

example : Measurable (fun r : ℝ => Expr.const r) := by
  fun_prop

example : Measurable (fun r : ℝ => Dist.ret (Expr.const r)) := by
  exact ret_comp_measurable (f := fun r : ℝ => Expr.const r) (by
    fun_prop)

example (x : String) (e1 e2 : Expr)
    (ih1 : IsProbabilityMeasure (step e1))
    (h : ¬ isValue e1) :
    IsProbabilityMeasure (step (.letE x e1 e2)) := by
  have hk : ∀ g : Expr, IsProbabilityMeasure (Dist.ret (Expr.letE x g e2)) := by
    intro g
    exact ret_is_prob_measure (Expr.letE x g e2)
  letI : IsProbabilityMeasure (step e1) := ih1
  change IsProbabilityMeasure (Dist.bind (step e1) (fun g : Expr => Dist.ret (Expr.letE x g e2)))
  exact bind_is_prob_measure
    (μ := step e1)
    (k := fun g : Expr => Dist.ret (Expr.letE x g e2))
    (hk := hk)
    (hkm := let_wrap_measurable x e2)

end Slice
