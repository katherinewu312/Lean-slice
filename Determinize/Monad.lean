import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Beta

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

/-- Uniform distribution on `[a, b]` when `a < b`.
Outside valid parameters, diverge.
-/
noncomputable def uniform (a b : ℝ) : Dist ℝ :=
  if a < b then
    ProbabilityTheory.cond volume (Set.Icc a b)
  else
    0

/-- Gaussian distribution with mean `μ` and variance `v`.
Mathlib parameterizes real Gaussians by a nonnegative variance. Negative
variance inputs are projected to `0`, yielding the Dirac Gaussian at `μ`.
-/
noncomputable def gaussian (μ v : ℝ) : Dist ℝ :=
  ProbabilityTheory.gaussianReal μ v.toNNReal

/-- Poisson distribution with rate `r`, mapped from `ℕ` to `ℝ`.
-/
noncomputable def poisson (r : ℝ) : Dist ℝ :=
  if 0 ≤ r then
    (ProbabilityTheory.poissonMeasure r.toNNReal).map (fun n : ℕ => (n : ℝ))
  else
    0

/-- Exponential distribution with rate `r`.
-/
noncomputable def exponential (r : ℝ) : Dist ℝ :=
  if 0 < r then
    ProbabilityTheory.expMeasure r
  else
    0

/-- Beta distribution with shape parameters `a` and `b`.
-/
noncomputable def beta (a b : ℝ) : Dist ℝ :=
  if 0 < a ∧ 0 < b then
    ProbabilityTheory.betaMeasure a b
  else
    0

/-- Gamma distribution with shape `a` and rate `r`.
-/
noncomputable def gamma (a r : ℝ) : Dist ℝ :=
  if 0 < a ∧ 0 < r then
    ProbabilityTheory.gammaMeasure a r
  else
    0

end Dist

end Determinize
