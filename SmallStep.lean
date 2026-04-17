import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Support
import Syntax
import Monad
import Skeleton
import Topology
import TypeSystem

namespace Slice

open MeasureTheory ProbabilityTheory
open scoped Topology

/-- A measure is subprobability if its total mass is at most `1`.
Since μ is already a Measure, countable additivity and nonnegativity are already built in. -/
def IsSubProbabilityMeasure {α : Type*} [MeasurableSpace α] (μ : Measure α) : Prop :=
  μ Set.univ ≤ 1

-- ---------------------------------------------------------------------------
-- Small-step semantics
-- Each expression steps to a distribution over expressions.
-- Values step to `Expr.diverge`, while `Expr.diverge` itself has zero outgoing mass.
-- ---------------------------------------------------------------------------

namespace Untyped

-- Small-step semantics over Expr → Dist (Expr)
noncomputable def step : Expr → Dist Expr
  | .diverge => 0

  | .const _ =>
      Dist.ret .diverge

  | .finconst _ _ =>
      Dist.ret .diverge

  | .trueE =>
      Dist.ret .diverge

  | .falseE =>
      Dist.ret .diverge

  | .var _ =>
      Dist.ret .diverge

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
            Dist.ret .diverge
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.uniform (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.uniform g e2))

end Untyped

-- Small-step semantics over well-typed expressions.
noncomputable def step {τ : Ty} (e : ExprsOfType τ) : Dist (ExprsOfType τ) := by
  classical
  exact
    (Untyped.step e.1).map (fun e' =>
      if h : HasType Ctx.empty e' τ then
        (⟨e', h⟩ : ExprsOfType τ)
      else
        -- dummy branch, because .map must take a total function (Expr). This is where type preservation comes in.
        e)

/-- Push an `ae` statement through `bind` when the right side is `dirac (f a)`. -/
lemma ae_of_ae_bind_dirac_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : α → β} (hf : Measurable f) {p : β → Prop}
    (hp : MeasurableSet {b | p b})
    (h : ∀ᵐ a ∂ μ, p (f a)) :
    ∀ᵐ b ∂ μ.bind (fun a => Measure.dirac (f a)), p b := by
  rw [MeasureTheory.Measure.bind_dirac_eq_map (m := μ) (f := f) (hf := hf)]
  exact (MeasureTheory.ae_map_iff hf.aemeasurable hp).2 h

lemma step_preserves_type_ae {τ : Ty} {e : Expr}
    (he : HasType Ctx.empty e τ)
    (hMeas : ∀ τ' : Ty, MeasurableSet ({e' : Expr | HasType Ctx.empty e' τ'} : Set Expr)) :
    Untyped.step e {e' | ¬ HasType Ctx.empty e' τ} = 0 := by
  change ∀ᵐ e' ∂ Untyped.step e, HasType Ctx.empty e' τ
  -- prove this directly by case split on `he`
  cases he with
  | diverge =>
      simp [Untyped.step]
  | const =>
      simpa [Untyped.step, Dist.ret_is_dirac] using
        (HasType.diverge (Γ := Ctx.empty) (τ := Ty.real))
  | trueE =>
      simpa [Untyped.step, Dist.ret_is_dirac] using
        (HasType.diverge (Γ := Ctx.empty) (τ := Ty.bool))
  | falseE =>
      simpa [Untyped.step, Dist.ret_is_dirac] using
        (HasType.diverge (Γ := Ctx.empty) (τ := Ty.bool))
  | finconst =>
      simp [Untyped.step, Dist.ret_is_dirac]
      exact HasType.diverge
  | var hx =>
      exfalso
      simp [Ctx.empty] at hx
  | discrete =>
      rename_i ps
      simp only [Untyped.step]
      let n := ps.1.length
      let discreteMeasure : Dist (Fin n) :=
        Finset.univ.sum (fun i : Fin n => (ps.1.get i) • Dist.ret i)
      change
        ∀ᵐ e' ∂ Measure.bind discreteMeasure (fun i => Measure.dirac (Expr.finconst n i)),
          HasType Ctx.empty e' (Ty.fin n)
      have hsource :
          ∀ᵐ i ∂ discreteMeasure, HasType Ctx.empty (Expr.finconst n i) (Ty.fin n) :=
        Filter.Eventually.of_forall (fun i => HasType.finconst i)
      exact ae_of_ae_bind_dirac_map
        (μ := discreteMeasure)
        (f := fun i : Fin n => Expr.finconst n i)
        (hf := finconst_wrap_measurable n)
        (hp := hMeas (Ty.fin n))
        hsource
  | letE h1 h2 =>
      rename_i x e1 e2 τ1
      simp only [Untyped.step]
      split_ifs with hv
      · have hsubst : HasType Ctx.empty (subst x e1 e2) τ :=
          subst_preserves_type h1 h2
        simp [Dist.ret_is_dirac, hsubst]
      · have ih : ∀ᵐ g ∂ Untyped.step e1, HasType Ctx.empty g τ1 := by
          exact step_preserves_type_ae (τ := τ1) h1 hMeas
        exact ae_of_ae_bind_dirac_map
          (μ := Untyped.step e1)
          (f := fun g : Expr => Expr.letE x g e2)
          (hf := let_wrap_measurable x e2)
          (hp := hMeas τ)
          (ih.mono (fun g hg => HasType.letE hg h2))
  | lt h1 h2 =>
      rename_i e1 e2
      simp only [Untyped.step]
      split
      · split
        · simpa [Dist.ret_is_dirac] using (HasType.trueE (Γ := Ctx.empty))
        · simpa [Dist.ret_is_dirac] using (HasType.falseE (Γ := Ctx.empty))
      · have ih2 : ∀ᵐ g ∂ Untyped.step e2, HasType Ctx.empty g .real := by
          exact step_preserves_type_ae (τ := .real) h2 hMeas
        exact ae_of_ae_bind_dirac_map
          (μ := Untyped.step e2)
          (f := fun g : Expr => Expr.lt (.const _) g)
          (hf := lt_right_wrap_measurable _)
          (hp := hMeas .bool)
          (ih2.mono (fun g hg => HasType.lt h1 hg))
      · have ih1 : ∀ᵐ g ∂ Untyped.step e1, HasType Ctx.empty g .real := by
          exact step_preserves_type_ae (τ := .real) h1 hMeas
        exact ae_of_ae_bind_dirac_map
          (μ := Untyped.step e1)
          (f := fun g : Expr => Expr.lt g e2)
          (hf := lt_left_wrap_measurable e2)
          (hp := hMeas .bool)
          (ih1.mono (fun g hg => HasType.lt hg h2))
  | ifE hc ht hf =>
      rename_i c t f
      simp only [Untyped.step]
      split
      · simpa [Dist.ret_is_dirac] using ht
      · simpa [Dist.ret_is_dirac] using hf
      · have ihc : ∀ᵐ g ∂ Untyped.step c, HasType Ctx.empty g .bool := by
          exact step_preserves_type_ae (τ := .bool) hc hMeas
        exact ae_of_ae_bind_dirac_map
          (μ := Untyped.step c)
          (f := fun g : Expr => Expr.ifE g t f)
          (hf := if_wrap_measurable t f)
          (hp := hMeas τ)
          (ihc.mono (fun g hg => HasType.ifE hg ht hf))
  | uniform h1 h2 =>
      rename_i e1 e2
      simp only [Untyped.step]
      split
      · split
        · exact ae_of_ae_bind_dirac_map
            (μ := ProbabilityTheory.cond MeasureTheory.volume (Set.Icc _ _))
            (f := fun r : ℝ => Expr.const r)
            (hf := const_wrap_measurable)
            (hp := hMeas .real)
            (Filter.Eventually.of_forall (fun r => HasType.const))
        · simpa [Dist.ret_is_dirac] using
            (HasType.diverge (Γ := Ctx.empty) (τ := Ty.real))
      · have ih2 : ∀ᵐ g ∂ Untyped.step e2, HasType Ctx.empty g .real := by
          exact step_preserves_type_ae (τ := .real) h2 hMeas
        exact ae_of_ae_bind_dirac_map
          (μ := Untyped.step e2)
          (f := fun g : Expr => Expr.uniform (.const _) g)
          (hf := uniform_right_wrap_measurable _)
          (hp := hMeas .real)
          (ih2.mono (fun g hg => HasType.uniform h1 hg))
      · have ih1 : ∀ᵐ g ∂ Untyped.step e1, HasType Ctx.empty g .real := by
          exact step_preserves_type_ae (τ := .real) h1 hMeas
        exact ae_of_ae_bind_dirac_map
          (μ := Untyped.step e1)
          (f := fun g : Expr => Expr.uniform g e2)
          (hf := uniform_left_wrap_measurable e2)
          (hp := hMeas .real)
          (ih1.mono (fun g hg => HasType.uniform hg h2))


/-- IRRELEVANT: Preservation: If e has type τ, and e' lies in the support of one small-step of e, then e' also has type τ. -/
lemma step_preserves_type_strong {τ : Ty} {e : Expr}
    (he : HasType Ctx.empty e τ) (e' : Expr)
    (hstep : e' ∈ (Untyped.step e).support) :
    HasType Ctx.empty e' τ := by
  cases he with
  | diverge =>
      simp [Untyped.step, Measure.support_zero] at hstep
  | const | trueE | falseE | finconst =>
      simp [Untyped.step, Dist.ret_is_dirac, Measure.support_dirac] at hstep
      simpa [hstep] using (HasType.diverge (Γ := Ctx.empty))
  | var hx =>
      exfalso
      simp [Ctx.empty] at hx
  | discrete =>
      simp [Untyped.step, Dist.ret_is_dirac] at hstep
      rcases hstep with ⟨i, _, rfl⟩
      exact HasType.finconst i
  | letE h1 h2 =>
      simp only [Untyped.step] at hstep
      split_ifs at hstep with hv
      · simp [Dist.ret_is_dirac, Measure.support_dirac] at hstep
        simpa [hstep] using (subst_preserves_type h1 h2)
      · simp [Dist.ret_is_dirac] at hstep
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
      · simp [Dist.ret_is_dirac] at hstep
        rcases hstep with ⟨g, hg, rfl⟩
        exact HasType.lt h1 (step_preserves_type_strong h2 g hg)
      · simp [Dist.ret_is_dirac] at hstep
        rcases hstep with ⟨g, hg, rfl⟩
        exact HasType.lt (step_preserves_type_strong h1 g hg) h2
  | ifE hc ht hf =>
      simp only [Untyped.step] at hstep
      split at hstep
      · simp [Dist.ret_is_dirac, Measure.support_dirac] at hstep
        simpa [hstep] using ht
      · simp [Dist.ret_is_dirac, Measure.support_dirac] at hstep
        simpa [hstep] using hf
      · simp [Dist.ret_is_dirac] at hstep
        rcases hstep with ⟨g, hg, rfl⟩
        exact HasType.ifE (step_preserves_type_strong hc g hg) ht hf
  | uniform h1 h2 =>
      simp only [Untyped.step] at hstep
      split at hstep
      · split at hstep
        · simp [Dist.ret_is_dirac] at hstep
          rcases hstep with ⟨_, _, rfl⟩
          exact HasType.const
        · simp [Dist.ret_is_dirac, Measure.support_dirac] at hstep
          simpa [hstep] using (HasType.diverge (Γ := Ctx.empty))
      · simp [Dist.ret_is_dirac] at hstep
        rcases hstep with ⟨g, hg, rfl⟩
        exact HasType.uniform h1 (step_preserves_type_strong h2 g hg)
      · simp [Dist.ret_is_dirac] at hstep
        rcases hstep with ⟨g, hg, rfl⟩
        exact HasType.uniform (step_preserves_type_strong h1 g hg) h2

-- ---------------------------------------------------------------------------
-- Small-step semantics is a Markov kernel.
-- 1. Subprobability measure
-- 2. Measurable function
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- 1. Subprobability measure
-- ---------------------------------------------------------------------------

-- Dirac.ret e is a subprobability measure.
lemma ret_is_subprob_measure {α : Type} [MeasurableSpace α] (a : α) :
    IsSubProbabilityMeasure (Dist.ret a) := by
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

lemma step_is_subprob_measure {τ : Ty} (e : ExprsOfType τ) :
    IsSubProbabilityMeasure (step e) := by
  sorry

-- ---------------------------------------------------------------------------
-- 2. Measurability
-- ---------------------------------------------------------------------------
-- Dist.ret ∘ f is measurable.
lemma ret_comp_measurable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) :
    Measurable (fun e : α => (Dist.ret (f e) : Dist β)) := by
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

/-- Typed step is measurable. -/
lemma step_is_measurable (τ : Ty) : Measurable (step (τ := τ)) := by
  sorry

noncomputable def stepKernel (τ : Ty) : Kernel (ExprsOfType τ) (ExprsOfType τ) where
  toFun    := step
  measurable' := step_is_measurable τ

/-- For typed inputs, `stepKernel` is subprobability. -/
theorem stepKernel_subprob_on_welltyped {τ : Ty} (e : ExprsOfType τ) :
    IsSubProbabilityMeasure (stepKernel τ e) := by
  simpa [stepKernel] using step_is_subprob_measure e

end Slice
