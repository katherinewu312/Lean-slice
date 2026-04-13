import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Support
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

def diverge : Dist Expr := 0

-- ---------------------------------------------------------------------------
-- Small-step semantics: Expr → Dist (Expr)
-- Each expression steps to a distribution over expressions.
-- For values, we return a Dirac delta on the value itself.
-- ---------------------------------------------------------------------------

namespace Untyped

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
      let n := ps.1.length
      let discreteMeasure : Dist (Fin n) :=
        Finset.univ.sum (fun i : Fin n => (ps.1.get i) • Dist.ret i)
      Dist.bind discreteMeasure (fun i => Dist.ret (.finconst n i))

  | .letE x e1 e2 =>
      if isValue e1 then
        Dist.ret (subst x e1 e2)
      else
        Dist.bind (step e1) (fun g => Dist.ret (.letE x g e2))

  | .ifE e1 e2 e3 =>
      match e1 with
      | .trueE =>
          Dist.ret e2
      | .falseE =>
          Dist.ret e3
      | _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.ifE g e2 e3))

  | .lt e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          if v1 < v2 then Dist.ret .trueE
          else Dist.ret .falseE
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.lt (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.lt g e2))

  | .uniform e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          if v1 ≤ v2 then
            -- Uniform distribution on [v1, v2], mapping samples to .const
            let lo := v1
            let hi := v2
            let uniformMeasure : Dist ℝ :=
              ProbabilityTheory.cond MeasureTheory.volume (Set.Icc lo hi)
            Dist.bind uniformMeasure (fun r => Dist.ret (.const r))
          else
            diverge
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.uniform (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.uniform g e2))

end Untyped

lemma step_preserves_type_strong {τ : Ty} {e : Expr}
    (he : HasType Ctx.empty e τ) (e' : Expr)
    (hstep : e' ∈ (Untyped.step e).support) :
    HasType Ctx.empty e' τ := by
  cases he with
  | const | trueE | falseE | var | finconst =>
      simpa [Untyped.step, diverge, Measure.support_zero] using hstep
  | discrete =>
      simp [Untyped.step, Dist.ret_is_dirac, Measure.support_dirac,
        Measure.support_bind] at hstep
      rcases hstep with ⟨i, _, rfl⟩
      exact HasType.finconst i
  | letE h1 h2 =>
      simp only [Untyped.step] at hstep
      split_ifs at hstep with hv
      · simp [Dist.ret_is_dirac, Measure.support_dirac] at hstep
        simpa [hstep] using (subst_preserves_type h1 h2)
      · simp [Measure.support_bind, Dist.ret_is_dirac, Measure.support_dirac] at hstep
        rcases hstep with ⟨g, hg, rfl⟩
        exact HasType.letE (step_preserves_type_strong h1 g hg) h2
  | lt h1 h2 =>
      simp only [Untyped.step] at hstep
      split at hstep
      · split at hstep
        · simp [Dist.ret_is_dirac, Measure.support_dirac] at hstep
          simpa [hstep] using (HasType.trueE (Γ := Ctx.empty))
        · simp [Dist.ret_is_dirac, Measure.support_dirac] at hstep
          simpa [hstep] using (HasType.falseE (Γ := Ctx.empty))
      · simp [Measure.support_bind, Dist.ret_is_dirac, Measure.support_dirac] at hstep
        rcases hstep with ⟨g, hg, rfl⟩
        exact HasType.lt h1 (step_preserves_type_strong h2 g hg)
      · simp [Measure.support_bind, Dist.ret_is_dirac, Measure.support_dirac] at hstep
        rcases hstep with ⟨g, hg, rfl⟩
        exact HasType.lt (step_preserves_type_strong h1 g hg) h2
  | ifE hc ht hf =>
      simp only [Untyped.step] at hstep
      split at hstep
      · simp [Dist.ret_is_dirac, Measure.support_dirac] at hstep
        simpa [hstep] using ht
      · simp [Dist.ret_is_dirac, Measure.support_dirac] at hstep
        simpa [hstep] using hf
      · simp [Measure.support_bind, Dist.ret_is_dirac, Measure.support_dirac] at hstep
        rcases hstep with ⟨g, hg, rfl⟩
        exact HasType.ifE (step_preserves_type_strong hc g hg) ht hf
  | uniform h1 h2 =>
      simp only [Untyped.step] at hstep
      split at hstep
      · split at hstep
        · simp [Measure.support_bind, Dist.ret_is_dirac, Measure.support_dirac] at hstep
          rcases hstep with ⟨_, _, rfl⟩
          exact HasType.const
        · simp [diverge, Measure.support_zero] at hstep
      · simp [Measure.support_bind, Dist.ret_is_dirac, Measure.support_dirac] at hstep
        rcases hstep with ⟨g, hg, rfl⟩
        exact HasType.uniform h1 (step_preserves_type_strong h2 g hg)
      · simp [Measure.support_bind, Dist.ret_is_dirac, Measure.support_dirac] at hstep
        rcases hstep with ⟨g, hg, rfl⟩
        exact HasType.uniform (step_preserves_type_strong h1 g hg) h2

noncomputable def step {τ : Ty} (e : ExprsOfType τ) : Dist (ExprsOfType τ) := by
  classical
  exact (Untyped.step e.1).map (fun e' =>
    if h : e' ∈ (Untyped.step e.1).support then
      (⟨e', step_preserves_type_strong e.2 e' h⟩ : ExprsOfType τ)
    else
      e)


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
    IsSubProbabilityMeasure (Dist.bind μ k) := by
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
    IsSubProbabilityMeasure (Untyped.step e) := by sorry

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

/-- Untyped step is measurable -/
lemma step_is_measurable : Measurable Untyped.step := by
  sorry

noncomputable def stepKernel : Kernel Expr Expr where
  toFun    := Untyped.step
  measurable' := step_is_measurable

/-- For typed inputs, `stepKernel` is subprobability. -/
theorem stepKernel_subprob_on_welltyped (e : Expr) (_ : WellTyped e) :
    IsSubProbabilityMeasure (stepKernel e) := by
  simpa [stepKernel] using step_is_subprob_measure e

end Slice
