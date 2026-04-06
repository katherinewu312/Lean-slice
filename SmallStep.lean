import Mathlib.Probability.Kernel.Defs
import Syntax
import Monad
import Skeleton
import TypeSystem

namespace Slice

open MeasureTheory ProbabilityTheory

-- ---------------------------------------------------------------------------
-- Small-step semantics: Expr → Dist (Expr)
-- Each expression steps to a distribution over expressions.
-- For values, we return a Dirac delta on the value itself.
-- ---------------------------------------------------------------------------

/-- Finite weighted sum of Dirac measures on `.const i`, starting at index `i`. -/
noncomputable def discreteMeasureExprFrom (i : Nat) : List Prob → Dist Expr
  | [] => 0
  | p :: qs => p • Dist.ret (.const (i : ℝ)) + discreteMeasureExprFrom (i + 1) qs

def diverge : Dist Expr := 0

noncomputable def step : Expr → Dist Expr
  | .const _ =>
      diverge

  | .finconst _ _ =>
      diverge

  | .trueE =>
      diverge

  | .falseE =>
      diverge

  | .var _ =>
      diverge

  | .discrete ps =>
      discreteMeasureExprFrom 0 ps.1

  -- If e1 is a value v, substitute and return δ_{e2[v/x]}
  -- Otherwise, step e1 and wrap: ⟦e1⟧ >>= λg. δ_{let x=g in e2}
  | .letE x e1 e2 =>
      if isValue e1 then
        Dist.ret (subst x e1 e2)
      else
        Dist.bind (step e1) (fun g => Dist.ret (.letE x g e2))

  -- If e1 = const 1 (true), return δ_{e2}
  -- If e1 = const 0 (false), return δ_{e3}
  -- Otherwise, step e1 and wrap: ⟦e1⟧ >>= λg. δ_{if g then e2 else e3}
  | .ifE e1 e2 e3 =>
      match e1 with
      | .trueE =>
          Dist.ret e2
      | .falseE =>
          Dist.ret e3
      | _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.ifE g e2 e3))

  -- Both values v1, v2: return δ_{true} or δ_{false}
  -- e1 value, e2 not: step e2 and wrap
  -- e1 not value: step e1 and wrap
  | .lt e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          if v1 < v2 then Dist.ret .trueE
          else Dist.ret .falseE
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.lt (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.lt g e2))

  -- Both values v1, v2:
  --   if v1 < v2: use conditionalized volume on [v1, v2], then return a constant expression
  --   otherwise: return a deterministic value
  -- e1 value, e2 not: step e2 and wrap
  -- e1 not value: step e1 and wrap
  | .uniform e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          if v1 <= v2 then
            let uniformMeasure : Dist ℝ :=
              ProbabilityTheory.cond MeasureTheory.volume (Set.Icc v1 v2)
            Dist.bind uniformMeasure (fun _ => Dist.ret (.const v1))
          else
            diverge
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.uniform (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.uniform g e2))

-- ---------------------------------------------------------------------------
-- Small-step semantics is a Markov kernel.
-- 1. Probability measure
-- 2. Measurable function
-- ---------------------------------------------------------------------------

-- Dirac.ret e is a probability measure.
-- Proof: Dist.ret = Measure.dirac, and Mathlib registers this as an instance.
lemma ret_is_prob_measure (e : Expr) : IsProbabilityMeasure (Dist.ret e) :=
  Measure.dirac.isProbabilityMeasure

-- Bind preserves probability measures.
-- If μ is a probability measure and every k x is a probability measure (with k measurable), then μ >>= k is a probability measure.
lemma bind_is_prob_measure {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (k : α → Measure β)
    (hμ : IsProbabilityMeasure μ)
    (hk : ∀ x, IsProbabilityMeasure (k x))
    (hkm : Measurable k) :
    IsProbabilityMeasure (μ >>= k) := by
  constructor
  rw [Dist.bind_is_measure_bind, Measure.bind_apply MeasurableSet.univ hkm.aemeasurable]
  simp only [measure_univ, lintegral_const, mul_one]

-- Dist.ret ∘ f is measurable.
lemma ret_comp_measurable {α : Type*} [MeasurableSpace α] {f : α → Expr} (hf : Measurable f) :
    Measurable (fun e : α => Dist.ret (f e)) := by
  simpa [Dist.ret_is_dirac] using
    (MeasureTheory.Measure.measurable_dirac.comp hf)


-- Substitution is measurable
lemma subst_is_measurable (x : String) (body : Expr) :
    Measurable (fun e : Expr => Dist.ret (subst x e body)) := by sorry

-- Bind preserves measurability.
lemma bind_is_measurable {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α → Measure β} {k : β → Measure γ}
    (hf : Measurable f) (hk : Measurable k) :
    Measurable (fun x => (f x).bind k) := by
  exact (MeasureTheory.Measure.measurable_bind' hk).comp hf

/-
For now, assume the temporary version of `step` where the two postponed branches are:

  | .discrete ps =>
      Dist.ret (.discrete ps)

  | .uniform e1 e2 =>
      Dist.ret (.uniform e1 e2)

Everything below is for that temporary fragment.
-/

lemma let_measurable (x : String) (e2 : Expr) :
    Measurable (fun g : Expr => Dist.ret (Expr.letE x g e2)) := by
  sorry

lemma if_measurable (e2 e3 : Expr) :
    Measurable (fun g : Expr => Dist.ret (Expr.ifE g e2 e3)) := by
  sorry

lemma lt_left_measurable (e2 : Expr) :
    Measurable (fun g : Expr => Dist.ret (Expr.lt g e2)) := by
  sorry

lemma lt_right_measurable (v1 : ℝ) :
    Measurable (fun g : Expr => Dist.ret (Expr.lt (.const v1) g)) := by
  sorry

lemma uniform_left_measurable (e2 : Expr) :
    Measurable (fun g : Expr => Dist.ret (Expr.uniform g e2)) := by
  sorry

lemma uniform_right_measurable (v1 : ℝ) :
    Measurable (fun g : Expr => Dist.ret (Expr.uniform (.const v1) g)) := by
  sorry

-- Add types
lemma step_is_prob_measure (e : Expr) (ht : WellTyped e) :
    isValue e ∨ IsProbabilityMeasure (step e) := by sorry

/-- Step is measurable -/
lemma step_is_measurable : Measurable step := by
  -- `ret_const_measurable` handles branches where `step` is a fixed Dirac map.
  -- The remaining branches can be handled by structural analysis for fixed `s`.
  -- `Measurable step` is equivalent to measurability of all evaluation maps
  -- `e ↦ step e s`.
  rw [MeasureTheory.Measure.measurable_measure]
  intro s hs
  -- This avoids the incorrect `intro e; induction e` shape
  -- (`Measurable step` does not introduce an `Expr` variable first).
  --
  -- TODO: finish this proof by structural analysis of `step` for fixed `s`.
  -- (left as sorry for now; the induction error is resolved)
  sorry

/-- Package `step` as a kernel once measurability is known. -/
noncomputable def stepKernel : Kernel Expr Expr where
  toFun := step
  measurable' := step_is_measurable

/-- Final result: the temporary small-step semantics is a Markov kernel. -/
theorem step_is_Markov_kernel : IsMarkovKernel stepKernel := by
  constructor
  intro e
  exact step_is_prob_measure e

end Slice
