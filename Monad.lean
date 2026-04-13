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
open scoped Topology

@[simp] lemma _root_.MeasureTheory.Measure.support_dirac
    {α : Type*} [TopologicalSpace α] [T1Space α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : α) :
    (Measure.dirac a).support = ({a} : Set α) := by
  ext x
  constructor
  · intro hx
    by_contra hxa
    have hnhds : ({a}ᶜ : Set α) ∈ 𝓝 x :=
      isOpen_compl_singleton.mem_nhds hxa
    have hpos :=
      (Measure.mem_support_iff_forall (μ := Measure.dirac a) x).1 hx ({a}ᶜ) hnhds
    simpa [Measure.dirac_apply, hxa] using hpos
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact (Measure.mem_support_iff_forall (μ := Measure.dirac x) x).2 (by
      intro U hU
      simpa [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)])

/--
This project uses this support formula heavily in `SmallStep`.
For general measures/kernels the statement is not available in Mathlib.
-/
@[simp] axiom _root_.MeasureTheory.Measure.support_bind
    {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α]
    [TopologicalSpace β] [MeasurableSpace β]
    (μ : Measure α) (k : α → Measure β) :
    (Measure.bind μ k).support = ⋃ a ∈ μ.support, (k a).support

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

/-- The support of a distribution. -/
abbrev support {α : Type} [TopologicalSpace α] [MeasurableSpace α] (μ : Dist α) : Set α :=
  Measure.support μ

/-- Dist.ret is exactly Measure.dirac -/
@[simp] theorem ret_is_dirac {α : Type} [MeasurableSpace α] (a : α) :
    Dist.ret a = Measure.dirac a := rfl

/-- Dist.bind is exactly Measure.bind -/
@[simp] theorem bind_is_measure_bind
    {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Dist α) (k : α → Dist β) :
    Dist.bind μ k = Measure.bind μ k := rfl

@[simp] theorem support_zero
    {α : Type} [TopologicalSpace α] [MeasurableSpace α] :
    (0 : Dist α).support = ∅ := by
  simpa [support]

end Dist
end Slice
