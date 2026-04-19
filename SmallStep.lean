import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.Prod
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
    [TopologicalSpace Expr]
    (he : HasType Ctx.empty e τ) (e' : Expr)
    (hstep : e' ∈ (Untyped.step e).support) :
    HasType Ctx.empty e' τ := by
  sorry

-- ---------------------------------------------------------------------------
-- Small-step semantics is a Markov kernel.
-- 1. Subprobability measure
-- 2. Measurable function
-- ---------------------------------------------------------------------------

/-- A sub-Markov kernel presented as a plain function `α → Measure β`. -/
-- We need sub- Markov kernels because we have diverge.
def IsSubMarkovKernel {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (K : α → Measure β) : Prop :=
  Measurable K ∧ ∀ a, IsSubProbabilityMeasure (K a)


/-- `ret ∘ f` is a sub-Markov kernel. -/
lemma ret_is_subMarkovKernel
    {α β : Type}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β}
    (hf : Measurable f) :
    IsSubMarkovKernel (fun a : α => (Dist.ret (f a) : Dist β)) := by
  refine ⟨
    (by
      simpa [Dist.ret_is_dirac] using
        (MeasureTheory.Measure.measurable_dirac.comp hf)),
    (by
      intro a
      simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
  ⟩

/-- A constant measure-valued map is a sub-Markov kernel if the measure is subprobability. -/
lemma const_is_subMarkovKernel
    {α β : Type}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure β}
    (hμ : IsSubProbabilityMeasure μ) :
    IsSubMarkovKernel (fun _ : α => μ) := by
  exact ⟨measurable_const, fun _ => hμ⟩

/-- General bind closure for sub-Markov kernels. -/
lemma bind_preserves_subMarkovKernel
    {α β γ : Type}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : α → Measure β}
    [∀ a, SFinite (μ a)]
    {κ : α → β → Measure γ}
    (hμ : IsSubMarkovKernel μ)
    (hκ_meas : Measurable (Function.uncurry κ))
    (hκ_sub : ∀ a b, IsSubProbabilityMeasure (κ a b)) :
    IsSubMarkovKernel
      (fun a : α => (Dist.bind (μ a) (κ a) : Dist γ)) := by
  rcases hμ with ⟨hμ_meas, hμ_sub⟩
  let μK : Kernel α β := ⟨μ, hμ_meas⟩
  let κK : Kernel (α × β) γ := ⟨Function.uncurry κ, hκ_meas⟩
  have hμK_fin : IsFiniteKernel μK := by
    refine ⟨⟨1, by simp, by
      intro a
      exact hμ_sub a⟩⟩
  letI : IsFiniteKernel μK := hμK_fin
  letI : IsSFiniteKernel μK := inferInstance
  have hbind_meas :
      Measurable (fun a : α => (Dist.bind (μ a) (κ a) : Dist γ)) := by
    let K : Kernel α γ := κK ∘ₖ Kernel.prod Kernel.id μK
    have hEq :
        (fun a : α => (Dist.bind (μ a) (κ a) : Dist γ)) =
          (fun a : α => (K a : Measure γ)) := by
      funext a
      ext s hs
      calc
        (Dist.bind (μ a) (κ a)) s
            = ∫⁻ b, κ a b s ∂(μ a) := by
              rw [Dist.bind_is_measure_bind, Measure.bind_apply hs]
              exact (Measurable.of_uncurry_left (f := κ) hκ_meas (x := a)).aemeasurable
        _ = ((κK ∘ₖ Kernel.prod Kernel.id μK) a) s := by
              symm
              rw [Kernel.comp_apply' (η := κK)
                (κ := Kernel.prod Kernel.id μK) (a := a) (hs := hs)]
              rw [Kernel.lintegral_id_prod (κ := μK) (a := a)
                (f := fun p : α × β => κK p s) (hf := Kernel.measurable_coe κK hs)]
              simp [μK, κK, Function.uncurry]
        _ = K a s := rfl
    rw [hEq]
    exact Kernel.measurable K
  refine ⟨hbind_meas, by
    intro a
    unfold IsSubProbabilityMeasure
    change (Dist.bind (μ a) (κ a) Set.univ ≤ 1)
    rw [Dist.bind_is_measure_bind, Measure.bind_apply MeasurableSet.univ]
    · calc
        ∫⁻ b, κ a b Set.univ ∂(μ a)
            ≤ ∫⁻ b, 1 ∂(μ a) := lintegral_mono (fun b => hκ_sub a b)
        _ = (μ a) Set.univ := by simp
        _ ≤ 1 := hμ_sub a
    · exact (Measurable.of_uncurry_left (f := κ) hκ_meas (x := a)).aemeasurable
  ⟩

/-- Specialization of bind closure when the RHS is `ret (f a b)`. -/
lemma bind_ret_preserves_subMarkovKernel
    {α β γ : Type}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : α → Measure β}
    [∀ a, SFinite (μ a)]
    (hμ : IsSubMarkovKernel μ)
    {f : α → β → γ}
    (hf : Measurable (Function.uncurry f)) :
    IsSubMarkovKernel
      (fun a : α => (Dist.bind (μ a) (fun b => Dist.ret (f a b)) : Dist γ)) := by
  refine bind_preserves_subMarkovKernel
    (μ := μ)
    (κ := fun a b => Dist.ret (f a b))
    hμ
    (by
      simpa [Function.uncurry, Dist.ret_is_dirac] using
        (MeasureTheory.Measure.measurable_dirac.comp hf))
    (by
      intro a b
      simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])




-- Continuation of bind is a Markov kernel.
lemma discrete_rhs_kernel (n : Nat) :
    IsSubMarkovKernel
      (fun i : Fin n => (Dist.ret (Expr.finconst n i) : Dist Expr)) := by
  sorry

lemma let_rhs_kernel (x : String) (e2 : Expr) :
    IsSubMarkovKernel
      (fun g : Expr => (Dist.ret (Expr.letE x g e2) : Dist Expr)) := by
  sorry

lemma if_rhs_kernel (t f : Expr) :
    IsSubMarkovKernel
      (fun g : Expr => (Dist.ret (Expr.ifE g t f) : Dist Expr)) := by
  sorry

lemma lt_left_rhs_kernel (e2 : Expr) :
    IsSubMarkovKernel
      (fun g : Expr => (Dist.ret (Expr.lt g e2) : Dist Expr)) := by
  sorry

lemma lt_right_rhs_kernel (v1 : ℝ) :
    IsSubMarkovKernel
      (fun g : Expr => (Dist.ret (Expr.lt (.const v1) g) : Dist Expr)) := by
  sorry

lemma uniform_left_rhs_kernel (e2 : Expr) :
    IsSubMarkovKernel
      (fun g : Expr => (Dist.ret (Expr.uniform g e2) : Dist Expr)) := by
  sorry

lemma uniform_right_rhs_kernel (v1 : ℝ) :
    IsSubMarkovKernel
      (fun g : Expr => (Dist.ret (Expr.uniform (.const v1) g) : Dist Expr)) := by
  sorry

lemma const_sample_rhs_kernel :
    IsSubMarkovKernel
      (fun r : ℝ => (Dist.ret (Expr.const r) : Dist Expr)) := by
  sorry


-- If K : Expr → Measure Expr is already a sub-Markov kernel for stepping a subexpression, then plugging that stepped subexpression back into a larger expression form still gives a sub-Markov kernel.
lemma let_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (x : String) (e2 : Expr) :
    IsSubMarkovKernel
      (fun e1 : Expr =>
        if isValue e1 then
          (Dist.ret (subst x e1 e2) : Dist Expr)
        else
          Dist.bind (K e1) (fun g => Dist.ret (Expr.letE x g e2))) := by
  sorry

lemma if_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (t f : Expr) :
    IsSubMarkovKernel
      (fun c : Expr =>
        match c with
        | .trueE  => Dist.ret t
        | .falseE => Dist.ret f
        | _       => Dist.bind (K c) (fun g => Dist.ret (Expr.ifE g t f))) := by
  sorry

lemma lt_left_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (e2 : Expr) :
    IsSubMarkovKernel
      (fun e1 : Expr =>
        Dist.bind (K e1) (fun g => Dist.ret (Expr.lt g e2))) := by
  sorry

lemma lt_right_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (v1 : ℝ) :
    IsSubMarkovKernel
      (fun e2 : Expr =>
        Dist.bind (K e2) (fun g => Dist.ret (Expr.lt (.const v1) g))) := by
  sorry

lemma uniform_left_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (e2 : Expr) :
    IsSubMarkovKernel
      (fun e1 : Expr =>
        Dist.bind (K e1) (fun g => Dist.ret (Expr.uniform g e2))) := by
  sorry

lemma uniform_right_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (v1 : ℝ) :
    IsSubMarkovKernel
      (fun e2 : Expr =>
        Dist.bind (K e2) (fun g => Dist.ret (Expr.uniform (.const v1) g))) := by
  sorry



lemma step_untyped_is_subMarkovKernel :
    IsSubMarkovKernel (fun e : Expr => Untyped.step e) := by
  sorry

end Slice
