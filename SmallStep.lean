import Mathlib.Probability.Kernel.Defs
import Syntax
import Monad
import Skeleton
import TypeSystem

namespace Slice

open MeasureTheory ProbabilityTheory

/-- A measure is subprobability if its total mass is at most `1`.
Since μ is already a Measure, countable additivity and nonnegativity are already built in. -/
def IsSubProbabilityMeasure {α : Type*} [MeasurableSpace α] (μ : Measure α) : Prop :=
  μ Set.univ ≤ 1

-- ---------------------------------------------------------------------------
-- Small-step semantics: Expr → Dist (Expr)
-- Each expression steps to a distribution over expressions.
-- For values, we return a Dirac delta on the value itself.
-- ---------------------------------------------------------------------------

noncomputable def step : Expr → Dist Expr
  | .const r =>
      Dist.ret (.const r)

  | .finconst n k =>
      Dist.ret (.finconst n k)

  | .trueE =>
      Dist.ret .trueE

  | .falseE =>
      Dist.ret .falseE

  | .var x =>
      Dist.ret (.var x)

  | .discrete ps =>
      let rec discreteMeasureFrom (i : Nat) (qs : List Prob) : Dist ℝ :=
        match qs with
        | [] => 0
        | p :: qs' => p • Dist.ret (i : ℝ) + discreteMeasureFrom (i + 1) qs'
      let discreteMeasure : Dist ℝ := discreteMeasureFrom 0 ps.1
      Dist.bind discreteMeasure (fun r => Dist.ret (.const r))

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
          if isValue e1 then
            -- a non-const value: stuck
            Dist.ret (.ifE e1 e2 e3)
          else
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
          if isValue e2 then
            -- e2 is a non-const value: stuck
            Dist.ret (.lt e1 e2)
          else
            Dist.bind (step e2) (fun g => Dist.ret (.lt (.const v1) g))
      | _, _ =>
          if isValue e1 then
            Dist.ret (.lt e1 e2)
          else
            Dist.bind (step e1) (fun g => Dist.ret (.lt g e2))

  -- Both values v1, v2:
  --   if v1 ≤ v2: Uniform(v1, v2) >>= λv. δ_{v}   (i.e., the uniform distribution)
  --   if v1 > v2: diverge (we use 0 measure / empty)
  -- e1 value, e2 not: step e2 and wrap
  -- e1 not value: step e1 and wrap
  | .uniform e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          -- ADD THIS BACK for sub-probability distribution!!!!!!
          -- if v1 ≤ v2 then
          --   -- Uniform distribution on [v1, v2], mapping samples to .const
          --   let lo := v1
          --   let hi := v2
          --   let uniformMeasure : Dist ℝ :=
          --     ProbabilityTheory.cond MeasureTheory.volume (Set.Icc lo hi)
          --   Dist.bind uniformMeasure (fun r => Dist.ret (.const r))
          -- else
          --   -- diverge: 0 measure
          --   0
          let lo := v1
          let hi := v2
          let uniformMeasure : Dist ℝ :=
            ProbabilityTheory.cond MeasureTheory.volume (Set.Icc lo hi)
          Dist.bind uniformMeasure (fun r => Dist.ret (.const r))
      | .const v1, _ =>
          if isValue e2 then
            Dist.ret (.uniform e1 e2)
          else
            Dist.bind (step e2) (fun g => Dist.ret (.uniform (.const v1) g))
      | _, _ =>
          if isValue e1 then
            Dist.ret (.uniform e1 e2)
          else
            Dist.bind (step e1) (fun g => Dist.ret (.uniform g e2))

-- ---------------------------------------------------------------------------
-- Small-step semantics is a Markov kernel.
-- 1. Subprobability measure
-- 2. Measurable function
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- 1. Subprobability measure
-- ---------------------------------------------------------------------------

-- Dirac.ret e is a subprobability measure.
lemma ret_is_subprob_measure (e : Expr) : IsSubProbabilityMeasure (Dist.ret e) := by
  unfold IsSubProbabilityMeasure
  simp [Dist.ret_is_dirac]

-- Bind preserves subprobability measures.
lemma bind_is_subprob_measure {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (k : α → Measure β)
    (hμ : IsSubProbabilityMeasure μ)
    (hk : ∀ x, IsSubProbabilityMeasure (k x))
    (hkm : Measurable k) :
    IsSubProbabilityMeasure (μ >>= k) := by
  unfold IsSubProbabilityMeasure at hμ hk ⊢
  rw [Dist.bind_is_measure_bind, Measure.bind_apply MeasurableSet.univ hkm.aemeasurable]
  exact (lintegral_mono (fun a => hk a)).trans (by simp [hμ])

-- For μ >>= f, f is measurable.
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

lemma step_is_subprob_measure (e : Expr) :
    IsSubProbabilityMeasure (step e) := by sorry

-- ---------------------------------------------------------------------------
-- 2. Measurability
-- ---------------------------------------------------------------------------
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

/-- Step is measurable -/
lemma step_is_measurable : Measurable step := by
  sorry

noncomputable def stepKernel : Kernel Expr Expr where
  toFun    := step
  measurable' := step_is_measurable

/-- For typed inputs, `stepKernel` is subprobability. -/
theorem stepKernel_subprob_on_welltyped (e : Expr) (_ : WellTyped e) :
    IsSubProbabilityMeasure (stepKernel e) := by
  simpa [stepKernel] using step_is_subprob_measure e

end Slice
