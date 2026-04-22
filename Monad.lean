import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Support

namespace Slice

open MeasureTheory ProbabilityTheory

/-- Probabilities -/
abbrev Prob := ENNReal

/-- Distributions are Mathlib measures. -/
abbrev Dist (α : Type) [MeasurableSpace α] := Measure α

namespace Dist

noncomputable def ret {α : Type} [MeasurableSpace α] (a : α) : Dist α :=
  Measure.dirac a

noncomputable def bind {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Dist α) (k : α → Dist β) : Dist β :=
  Measure.bind μ k

/-- Dist.ret is exactly Measure.dirac -/
@[simp] theorem ret_is_dirac {α : Type} [MeasurableSpace α] (a : α) :
    Dist.ret a = Measure.dirac a := rfl

/-- Dist.bind is exactly Measure.bind -/
@[simp] theorem bind_is_measure_bind
    {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Dist α) (k : α → Dist β) :
    Dist.bind μ k = Measure.bind μ k := rfl

end Dist
end Slice
