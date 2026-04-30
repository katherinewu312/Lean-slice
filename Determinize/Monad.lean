import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Support

namespace Determinize

open MeasureTheory ProbabilityTheory

/-- Distributions are measures. -/
abbrev Dist (α : Type) [MeasurableSpace α] := Measure α

namespace Dist

noncomputable def ret {α : Type} [MeasurableSpace α] (a : α) : Dist α :=
  Measure.dirac a

noncomputable def bind {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Dist α) (k : α → Dist β) : Dist β :=
  Measure.bind μ k

@[simp] theorem ret_is_dirac {α : Type} [MeasurableSpace α] (a : α) :
    Dist.ret a = Measure.dirac a := rfl

@[simp] theorem bind_is_measure_bind
    {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Dist α) (k : α → Dist β) :
    Dist.bind μ k = Measure.bind μ k := rfl

/-- Primitive continuous samplers (kept abstract at this stage). -/
axiom uniform : ℝ → ℝ → Dist ℝ
axiom gaussian : ℝ → ℝ → Dist ℝ
axiom poisson : ℝ → Dist ℝ
axiom exponential : ℝ → Dist ℝ
axiom beta : ℝ → ℝ → Dist ℝ
axiom gamma : ℝ → ℝ → Dist ℝ

end Dist

end Determinize
