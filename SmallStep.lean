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

-- General bind closure for sub-Markov kernels.
lemma bind_preserves_subMarkovKernel
    {α β γ : Type}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : α → Measure β}
    [∀ a, SFinite (μ a)]
    {κ : α → β → Measure γ}
    (hμ : IsSubMarkovKernel μ)
    (hκ : IsSubMarkovKernel (Function.uncurry κ)) :
    IsSubMarkovKernel
      (fun a : α => (Dist.bind (μ a) (κ a) : Dist γ)) := by
  rcases hμ with ⟨hμ_meas, hμ_sub⟩
  rcases hκ with ⟨hκ_meas, hκ_sub'⟩
  have hκ_sub : ∀ a b, IsSubProbabilityMeasure (κ a b) := fun a b => hκ_sub' (a, b)
  let μK : Kernel α β := ⟨μ, hμ_meas⟩
  let κK : Kernel (α × β) γ := ⟨Function.uncurry κ, hκ_meas⟩
  have hμK_fin : IsFiniteKernel μK := by
    refine ⟨⟨1, by simp, by intro a; exact hμ_sub a⟩⟩
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
      refine ⟨
        (by
          simpa [Function.uncurry, Dist.ret_is_dirac] using
            (MeasureTheory.Measure.measurable_dirac.comp hf)),
        (by
          intro p
          rcases p with ⟨a, b⟩
          simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
      ⟩)


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
  classical
  rcases hK with ⟨hK_meas, hK_sub⟩
  letI : ∀ a : Expr, IsFiniteMeasure (K a) := fun a =>
    ⟨lt_of_le_of_lt (hK_sub a) (by simp)⟩
  letI : ∀ a : Expr, SFinite (K a) := fun a => inferInstance
  have hif_uncurry :
      Measurable (Function.uncurry (fun (_ : Expr) (g : Expr) => Expr.ifE g t f)) := by
    simpa [Function.uncurry] using (if_wrap_measurable t f).comp measurable_snd
  have hbind :
      IsSubMarkovKernel
        (fun c : Expr =>
          (Dist.bind (K c) (fun g => Dist.ret (Expr.ifE g t f)) : Dist Expr)) :=
    bind_ret_preserves_subMarkovKernel
      (μ := K) ⟨hK_meas, hK_sub⟩ (f := fun (_ : Expr) (g : Expr) => Expr.ifE g t f) hif_uncurry
  rcases hbind with ⟨hbind_meas, hbind_sub⟩
  have hEq :
      (fun c : Expr =>
        match c with
        | .trueE  => Dist.ret t
        | .falseE => Dist.ret f
        | _       => Dist.bind (K c) (fun g => Dist.ret (Expr.ifE g t f)))
      =
      (fun c : Expr =>
        if c = Expr.trueE then (Dist.ret t : Dist Expr)
        else if c = Expr.falseE then (Dist.ret f : Dist Expr)
        else (Dist.bind (K c) (fun g => Dist.ret (Expr.ifE g t f)) : Dist Expr)) := by
    funext c
    cases c <;> simp
  refine ⟨?_, ?_⟩
  · rw [hEq]
    have htrueSet : MeasurableSet {c : Expr | c = Expr.trueE} := by
      simpa [Set.setOf_eq_eq_singleton] using
        (measurableSet_singleton (a := Expr.trueE))
    have hfalseSet : MeasurableSet {c : Expr | c = Expr.falseE} := by
      simpa [Set.setOf_eq_eq_singleton] using
        (measurableSet_singleton (a := Expr.falseE))
    refine Measurable.ite htrueSet measurable_const ?_
    exact Measurable.ite hfalseSet measurable_const hbind_meas
  · intro c
    rw [hEq]
    by_cases htrue : c = Expr.trueE
    · simp [htrue, IsSubProbabilityMeasure, Dist.ret_is_dirac]
    · by_cases hfalse : c = Expr.falseE
      · simp [hfalse, IsSubProbabilityMeasure, Dist.ret_is_dirac]
      · simpa [htrue, hfalse] using hbind_sub c

lemma lt_left_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (e2 : Expr) :
    IsSubMarkovKernel
      (fun e1 : Expr =>
        Dist.bind (K e1) (fun g => Dist.ret (Expr.lt g e2))) := by
  rcases hK with ⟨hK_meas, hK_sub⟩
  letI : ∀ a : Expr, IsFiniteMeasure (K a) := fun a =>
    ⟨lt_of_le_of_lt (hK_sub a) (by simp)⟩
  letI : ∀ a : Expr, SFinite (K a) := fun a => inferInstance
  exact bind_ret_preserves_subMarkovKernel
    (μ := K)
    ⟨hK_meas, hK_sub⟩
    (f := fun (_ : Expr) (g : Expr) => Expr.lt g e2)
    (by
      simpa [Function.uncurry] using (lt_left_wrap_measurable e2).comp measurable_snd)

lemma lt_right_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (v1 : ℝ) :
    IsSubMarkovKernel
      (fun e2 : Expr =>
        Dist.bind (K e2) (fun g => Dist.ret (Expr.lt (.const v1) g))) := by
  rcases hK with ⟨hK_meas, hK_sub⟩
  letI : ∀ a : Expr, IsFiniteMeasure (K a) := fun a =>
    ⟨lt_of_le_of_lt (hK_sub a) (by simp)⟩
  letI : ∀ a : Expr, SFinite (K a) := fun a => inferInstance
  exact bind_ret_preserves_subMarkovKernel
    (μ := K)
    ⟨hK_meas, hK_sub⟩
    (f := fun (_ : Expr) (g : Expr) => Expr.lt (.const v1) g)
    (by
      simpa [Function.uncurry] using (lt_right_wrap_measurable v1).comp measurable_snd)

lemma uniform_left_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (e2 : Expr) :
    IsSubMarkovKernel
      (fun e1 : Expr =>
        Dist.bind (K e1) (fun g => Dist.ret (Expr.uniform g e2))) := by
  rcases hK with ⟨hK_meas, hK_sub⟩
  letI : ∀ a : Expr, IsFiniteMeasure (K a) := fun a =>
    ⟨lt_of_le_of_lt (hK_sub a) (by simp)⟩
  letI : ∀ a : Expr, SFinite (K a) := fun a => inferInstance
  exact bind_ret_preserves_subMarkovKernel
    (μ := K)
    ⟨hK_meas, hK_sub⟩
    (f := fun (_ : Expr) (g : Expr) => Expr.uniform g e2)
    (by
      simpa [Function.uncurry] using (uniform_left_wrap_measurable e2).comp measurable_snd)

lemma uniform_right_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (v1 : ℝ) :
    IsSubMarkovKernel
      (fun e2 : Expr =>
        Dist.bind (K e2) (fun g => Dist.ret (Expr.uniform (.const v1) g))) := by
  rcases hK with ⟨hK_meas, hK_sub⟩
  letI : ∀ a : Expr, IsFiniteMeasure (K a) := fun a =>
    ⟨lt_of_le_of_lt (hK_sub a) (by simp)⟩
  letI : ∀ a : Expr, SFinite (K a) := fun a => inferInstance
  exact bind_ret_preserves_subMarkovKernel
    (μ := K)
    ⟨hK_meas, hK_sub⟩
    (f := fun (_ : Expr) (g : Expr) => Expr.uniform (.const v1) g)
    (by
      simpa [Function.uncurry] using (uniform_right_wrap_measurable v1).comp measurable_snd)


lemma fillSkeleton_not_const_of_ne_hole
    {s : Untyped.Skeleton}
    (hs : s ≠ Untyped.Skeleton.hole) :
    ∀ v : Fin (Untyped.numHoles s) → ℝ, ¬ ∃ r : ℝ, Untyped.fillSkeleton s v = Expr.const r := by
  intro v
  cases s <;> simp [Untyped.fillSkeleton] at hs ⊢

lemma fillSkeleton_not_true_of_ne_trueE
    {s : Untyped.Skeleton}
    (hs : s ≠ Untyped.Skeleton.trueE) :
    ∀ v : Fin (Untyped.numHoles s) → ℝ, Untyped.fillSkeleton s v ≠ Expr.trueE := by
  intro v
  cases s <;> simp [Untyped.fillSkeleton] at hs ⊢

lemma fillSkeleton_not_false_of_ne_falseE
    {s : Untyped.Skeleton}
    (hs : s ≠ Untyped.Skeleton.falseE) :
    ∀ v : Fin (Untyped.numHoles s) → ℝ, Untyped.fillSkeleton s v ≠ Expr.falseE := by
  intro v
  cases s <;> simp [Untyped.fillSkeleton] at hs ⊢

/-- Measurability of dependent `bind` into `ret`. -/
axiom bind_ret_dep_measurable
    {α β γ : Type}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : α → Measure β}
    (hμ : Measurable μ)
    {f : α → β → γ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun a : α => (Dist.bind (μ a) (fun b => Dist.ret (f a b)) : Dist γ))

/-- Uncurry measurability for `(a,g) ↦ lt g (e₂ a)`. -/
axiom lt_left_dep_uncurry_measurable
    {α : Type}
    [MeasurableSpace α]
    {e2 : α → Expr} :
    Measurable (Function.uncurry (fun a : α => fun g : Expr => Expr.lt g (e2 a)))

/-- Uncurry measurability for `(a,g) ↦ lt (const (r a)) g`. -/
axiom lt_right_dep_uncurry_measurable
    {α : Type}
    [MeasurableSpace α]
    {r : α → ℝ} :
    Measurable (Function.uncurry (fun a : α => fun g : Expr => Expr.lt (.const (r a)) g))

/-- Uncurry measurability for `(a,g) ↦ ifE g (t a) (f a)`. -/
axiom if_dep_uncurry_measurable
    {α : Type}
    [MeasurableSpace α]
    {t f : α → Expr} :
    Measurable (Function.uncurry (fun a : α => fun g : Expr => Expr.ifE g (t a) (f a)))

/-- Measurability of `a ↦ ret (fillSkeleton σ (p a))`. -/
axiom fill_ret_slice_measurable
    {α : Type}
    [MeasurableSpace α]
    (σ : Untyped.Skeleton)
    (p : α → Fin (Untyped.numHoles σ) → ℝ)
    (hp : Measurable p) :
    Measurable (fun a : α => (Dist.ret (Untyped.fillSkeleton σ (p a)) : Dist Expr))

/-- Uncurry measurability for `(a,g) ↦ uniform g (e₂ a)`. -/
axiom uniform_left_dep_uncurry_measurable
    {α : Type}
    [MeasurableSpace α]
    {e2 : α → Expr} :
    Measurable (Function.uncurry (fun a : α => fun g : Expr => Expr.uniform g (e2 a)))

/-- Uncurry measurability for `(a,g) ↦ uniform (const (r a)) g`. -/
axiom uniform_right_dep_uncurry_measurable
    {α : Type}
    [MeasurableSpace α]
    {r : α → ℝ} :
    Measurable (Function.uncurry (fun a : α => fun g : Expr => Expr.uniform (.const (r a)) g))

/-- Measurability of the const/const uniform branch. -/
axiom uniform_const_const_branch_measurable
    {α : Type}
    [MeasurableSpace α]
    {lo hi : α → ℝ} :
    Measurable (fun a : α =>
      if lo a ≤ hi a then
        (Dist.bind (ProbabilityTheory.cond MeasureTheory.volume (Set.Icc (lo a) (hi a)))
          (fun r => Dist.ret (Expr.const r)) : Dist Expr)
      else
        (Dist.ret Expr.diverge : Dist Expr))

/-- Uncurry measurability for `(a,g) ↦ letE x g (e₂ a)`. -/
axiom let_dep_uncurry_measurable
    {α : Type}
    [MeasurableSpace α]
    (x : String)
    {e2 : α → Expr} :
    Measurable (Function.uncurry (fun a : α => fun g : Expr => Expr.letE x g (e2 a)))

/-- Measurability of `a ↦ ret (subst x (v a) (e₂ a))`. -/
axiom subst_dep_ret_measurable
    {α : Type}
    [MeasurableSpace α]
    (x : String)
    {v e2 : α → Expr} :
    Measurable (fun a : α => (Dist.ret (subst x (v a) (e2 a)) : Dist Expr))


lemma step_lt_slice_measurable
    (s1 s2 : Untyped.Skeleton)
    (ih1 : Measurable (fun v : Fin (Untyped.numHoles s1) → ℝ => Untyped.step (Untyped.fillSkeleton s1 v)))
    (ih2 : Measurable (fun v : Fin (Untyped.numHoles s2) → ℝ => Untyped.step (Untyped.fillSkeleton s2 v))) :
    Measurable (fun v : Fin (Untyped.numHoles s1 + Untyped.numHoles s2) → ℝ =>
      match Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2) i)),
            Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) i)) with
      | Expr.const v1, Expr.const v2 =>
          if v1 < v2 then (Dist.ret Expr.trueE : Dist Expr)
          else (Dist.ret Expr.falseE : Dist Expr)
      | Expr.const v1, _ =>
          Dist.bind
            (Untyped.step (Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) i))))
            (fun g => Dist.ret (Expr.lt (.const v1) g))
      | _, _ =>
          Dist.bind
            (Untyped.step (Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2) i))))
            (fun g => Dist.ret (Expr.lt g (Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) i)))))) := by
  classical
  let α := Fin (Untyped.numHoles s1 + Untyped.numHoles s2) → ℝ
  let v1 : α → (Fin (Untyped.numHoles s1) → ℝ) :=
    fun v i => v (Fin.castAdd (Untyped.numHoles s2) i)
  let v2 : α → (Fin (Untyped.numHoles s2) → ℝ) :=
    fun v i => v (Fin.natAdd (Untyped.numHoles s1) i)
  have hv1 : Measurable v1 := by
    refine measurable_pi_iff.2 ?_
    intro i
    simpa [v1] using (measurable_pi_apply (Fin.castAdd (Untyped.numHoles s2) i))
  have hv2 : Measurable v2 := by
    refine measurable_pi_iff.2 ?_
    intro i
    simpa [v2] using (measurable_pi_apply (Fin.natAdd (Untyped.numHoles s1) i))
  by_cases hs1 : s1 = Untyped.Skeleton.hole
  · subst hs1
    let i0 : Fin (Untyped.numHoles Untyped.Skeleton.hole) := ⟨0, by simp [Untyped.numHoles]⟩
    by_cases hs2 : s2 = Untyped.Skeleton.hole
    · subst hs2
      refine Measurable.ite ?_ measurable_const measurable_const
      simpa [Untyped.numHoles] using
        (measurableSet_lt
          (measurable_pi_apply (Fin.castAdd 1 (0 : Fin 1)))
          (measurable_pi_apply (Fin.natAdd 1 (0 : Fin 1))))
    · have hEq :
        (fun v : α =>
          match Untyped.fillSkeleton Untyped.Skeleton.hole (v1 v),
                Untyped.fillSkeleton s2 (v2 v) with
          | Expr.const v1, Expr.const v2 =>
              if v1 < v2 then (Dist.ret Expr.trueE : Dist Expr)
              else (Dist.ret Expr.falseE : Dist Expr)
          | Expr.const v1, _ =>
              Dist.bind
                (Untyped.step (Untyped.fillSkeleton s2 (v2 v)))
                (fun g => Dist.ret (Expr.lt (.const v1) g))
          | _, _ =>
              Dist.bind
                (Untyped.step (Untyped.fillSkeleton Untyped.Skeleton.hole (v1 v)))
                (fun g => Dist.ret (Expr.lt g (Untyped.fillSkeleton s2 (v2 v)))))
        =
        (fun v : α =>
          Dist.bind
            (Untyped.step (Untyped.fillSkeleton s2 (v2 v)))
            (fun g =>
              Dist.ret
                (Expr.lt
                  (.const ((v1 v) i0))
                  g))) := by
        funext v
        have hnot2 : ¬ ∃ r : ℝ, Untyped.fillSkeleton s2 (v2 v) = Expr.const r :=
          fillSkeleton_not_const_of_ne_hole hs2 (v2 v)
        cases h2 : Untyped.fillSkeleton s2 (v2 v) with
        | const r =>
            exact (False.elim (hnot2 ⟨r, h2⟩))
        | var _ | trueE | falseE | finconst _ _ | discrete _ | diverge
          | letE _ _ _ | lt _ _ | ifE _ _ _ | uniform _ _ =>
            simpa [Untyped.fillSkeleton, i0]
      rw [hEq]
      let μ : α → Measure Expr := fun v => Untyped.step (Untyped.fillSkeleton s2 (v2 v))
      have hμ : Measurable μ := by
        simpa [μ] using ih2.comp hv2
      have hbind :
          Measurable
            (fun v : α =>
              Dist.bind (μ v) (fun g => Dist.ret (Expr.lt (.const ((v1 v) i0)) g))) :=
        bind_ret_dep_measurable
          (μ := μ) hμ
          (f := fun v g => Expr.lt (.const ((v1 v) i0)) g)
          (hf := lt_right_dep_uncurry_measurable (r := fun v : α => (v1 v) i0))
      simpa [μ] using hbind
  · have hEq :
      (fun v : α =>
        match Untyped.fillSkeleton s1 (v1 v),
              Untyped.fillSkeleton s2 (v2 v) with
        | Expr.const v1, Expr.const v2 =>
            if v1 < v2 then (Dist.ret Expr.trueE : Dist Expr)
            else (Dist.ret Expr.falseE : Dist Expr)
        | Expr.const v1, _ =>
            Dist.bind
              (Untyped.step (Untyped.fillSkeleton s2 (v2 v)))
              (fun g => Dist.ret (Expr.lt (.const v1) g))
        | _, _ =>
            Dist.bind
              (Untyped.step (Untyped.fillSkeleton s1 (v1 v)))
              (fun g => Dist.ret (Expr.lt g (Untyped.fillSkeleton s2 (v2 v)))))
      =
      (fun v : α =>
        Dist.bind
          (Untyped.step (Untyped.fillSkeleton s1 (v1 v)))
          (fun g => Dist.ret (Expr.lt g (Untyped.fillSkeleton s2 (v2 v))))) := by
      funext v
      have hnot1 : ¬ ∃ r : ℝ, Untyped.fillSkeleton s1 (v1 v) = Expr.const r :=
        fillSkeleton_not_const_of_ne_hole hs1 (v1 v)
      cases h1 : Untyped.fillSkeleton s1 (v1 v) <;> simp [h1] at hnot1 ⊢
    rw [hEq]
    let μ : α → Measure Expr := fun v => Untyped.step (Untyped.fillSkeleton s1 (v1 v))
    have hμ : Measurable μ := by
      simpa [μ] using ih1.comp hv1
    have hbind :
        Measurable
          (fun v : α =>
            Dist.bind
              (μ v)
              (fun g => Dist.ret (Expr.lt g (Untyped.fillSkeleton s2 (v2 v))))) :=
      bind_ret_dep_measurable
        (μ := μ) hμ
        (f := fun v g => Expr.lt g (Untyped.fillSkeleton s2 (v2 v)))
        (hf := lt_left_dep_uncurry_measurable (e2 := fun v : α => Untyped.fillSkeleton s2 (v2 v)))
    simpa [μ] using hbind

lemma step_if_slice_measurable
    (s1 s2 s3 : Untyped.Skeleton)
    (ih1 : Measurable (fun v : Fin (Untyped.numHoles s1) → ℝ => Untyped.step (Untyped.fillSkeleton s1 v)))
    (ih2 : Measurable (fun v : Fin (Untyped.numHoles s2) → ℝ => Untyped.step (Untyped.fillSkeleton s2 v)))
    (ih3 : Measurable (fun v : Fin (Untyped.numHoles s3) → ℝ => Untyped.step (Untyped.fillSkeleton s3 v))) :
    Measurable (fun v : Fin (Untyped.numHoles s1 + (Untyped.numHoles s2 + Untyped.numHoles s3)) → ℝ =>
      match Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2 + Untyped.numHoles s3) i)) with
      | Expr.trueE =>
          Dist.ret (Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) (Fin.castAdd (Untyped.numHoles s3) i))))
      | Expr.falseE =>
          Dist.ret (Untyped.fillSkeleton s3 (fun i => v (Fin.natAdd (Untyped.numHoles s1) (Fin.natAdd (Untyped.numHoles s2) i))))
      | _ =>
          Dist.bind
            (Untyped.step (Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2 + Untyped.numHoles s3) i))))
            (fun g =>
              Dist.ret
                (Expr.ifE g
                  (Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) (Fin.castAdd (Untyped.numHoles s3) i))))
                  (Untyped.fillSkeleton s3 (fun i => v (Fin.natAdd (Untyped.numHoles s1) (Fin.natAdd (Untyped.numHoles s2) i))))))) := by
  classical
  let α := Fin (Untyped.numHoles s1 + (Untyped.numHoles s2 + Untyped.numHoles s3)) → ℝ
  let v1 : α → (Fin (Untyped.numHoles s1) → ℝ) :=
    fun v i => v (Fin.castAdd (Untyped.numHoles s2 + Untyped.numHoles s3) i)
  let v2 : α → (Fin (Untyped.numHoles s2) → ℝ) :=
    fun v i => v (Fin.natAdd (Untyped.numHoles s1) (Fin.castAdd (Untyped.numHoles s3) i))
  let v3 : α → (Fin (Untyped.numHoles s3) → ℝ) :=
    fun v i => v (Fin.natAdd (Untyped.numHoles s1) (Fin.natAdd (Untyped.numHoles s2) i))
  have hv1 : Measurable v1 := by
    refine measurable_pi_iff.2 ?_
    intro i
    simpa [v1] using
      (measurable_pi_apply (Fin.castAdd (Untyped.numHoles s2 + Untyped.numHoles s3) i))
  have hv2 : Measurable v2 := by
    refine measurable_pi_iff.2 ?_
    intro i
    simpa [v2] using
      (measurable_pi_apply (Fin.natAdd (Untyped.numHoles s1) (Fin.castAdd (Untyped.numHoles s3) i)))
  have hv3 : Measurable v3 := by
    refine measurable_pi_iff.2 ?_
    intro i
    simpa [v3] using
      (measurable_pi_apply (Fin.natAdd (Untyped.numHoles s1) (Fin.natAdd (Untyped.numHoles s2) i)))
  by_cases hs1t : s1 = Untyped.Skeleton.trueE
  · subst hs1t
    have hret :
        Measurable (fun v : α => (Dist.ret (Untyped.fillSkeleton s2 (v2 v)) : Dist Expr)) :=
      fill_ret_slice_measurable s2 v2 hv2
    simpa [Untyped.fillSkeleton] using hret
  · by_cases hs1f : s1 = Untyped.Skeleton.falseE
    · subst hs1f
      have hret :
          Measurable (fun v : α => (Dist.ret (Untyped.fillSkeleton s3 (v3 v)) : Dist Expr)) :=
        fill_ret_slice_measurable s3 v3 hv3
      simpa [Untyped.fillSkeleton] using hret
    · have hEq :
        (fun v : α =>
          match Untyped.fillSkeleton s1 (v1 v) with
          | Expr.trueE =>
              Dist.ret (Untyped.fillSkeleton s2 (v2 v))
          | Expr.falseE =>
              Dist.ret (Untyped.fillSkeleton s3 (v3 v))
          | _ =>
              Dist.bind
                (Untyped.step (Untyped.fillSkeleton s1 (v1 v)))
                (fun g => Dist.ret (Expr.ifE g (Untyped.fillSkeleton s2 (v2 v)) (Untyped.fillSkeleton s3 (v3 v)))))
        =
        (fun v : α =>
          Dist.bind
            (Untyped.step (Untyped.fillSkeleton s1 (v1 v)))
            (fun g => Dist.ret (Expr.ifE g (Untyped.fillSkeleton s2 (v2 v)) (Untyped.fillSkeleton s3 (v3 v))))) := by
        funext v
        have hnt : Untyped.fillSkeleton s1 (v1 v) ≠ Expr.trueE :=
          fillSkeleton_not_true_of_ne_trueE hs1t (v1 v)
        have hnf : Untyped.fillSkeleton s1 (v1 v) ≠ Expr.falseE :=
          fillSkeleton_not_false_of_ne_falseE hs1f (v1 v)
        cases h1 : Untyped.fillSkeleton s1 (v1 v) with
        | trueE =>
            exact (False.elim (hnt h1))
        | falseE =>
            exact (False.elim (hnf h1))
        | var _ | const _ | finconst _ _ | discrete _ | diverge
          | letE _ _ _ | lt _ _ | ifE _ _ _ | uniform _ _ =>
            simp [h1]
      rw [hEq]
      let μ : α → Measure Expr := fun v => Untyped.step (Untyped.fillSkeleton s1 (v1 v))
      have hμ : Measurable μ := by
        simpa [μ] using ih1.comp hv1
      have hbind :
          Measurable
            (fun v : α =>
              Dist.bind
                (μ v)
                (fun g => Dist.ret (Expr.ifE g (Untyped.fillSkeleton s2 (v2 v)) (Untyped.fillSkeleton s3 (v3 v))))) :=
        bind_ret_dep_measurable
          (μ := μ) hμ
          (f := fun v g => Expr.ifE g (Untyped.fillSkeleton s2 (v2 v)) (Untyped.fillSkeleton s3 (v3 v)))
          (hf := if_dep_uncurry_measurable
            (t := fun v : α => Untyped.fillSkeleton s2 (v2 v))
            (f := fun v : α => Untyped.fillSkeleton s3 (v3 v)))
      simpa [μ] using hbind

lemma step_let_slice_measurable
    (x : String) (s1 s2 : Untyped.Skeleton)
    (ih1 : Measurable (fun v : Fin (Untyped.numHoles s1) → ℝ => Untyped.step (Untyped.fillSkeleton s1 v))) :
    Measurable (fun v : Fin (Untyped.numHoles s1 + Untyped.numHoles s2) → ℝ =>
      if isValue (Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2) i)) ) then
        Dist.ret
          (subst x
            (Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2) i)))
            (Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) i))))
      else
        Dist.bind
          (Untyped.step (Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2) i))))
          (fun g =>
            Dist.ret
              (Expr.letE x g
                (Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) i)))))) := by
  classical
  let α := Fin (Untyped.numHoles s1 + Untyped.numHoles s2) → ℝ
  let v1 : α → (Fin (Untyped.numHoles s1) → ℝ) :=
    fun v i => v (Fin.castAdd (Untyped.numHoles s2) i)
  let v2 : α → (Fin (Untyped.numHoles s2) → ℝ) :=
    fun v i => v (Fin.natAdd (Untyped.numHoles s1) i)
  have hv1 : Measurable v1 := by
    refine measurable_pi_iff.2 ?_
    intro i
    simpa [v1] using (measurable_pi_apply (Fin.castAdd (Untyped.numHoles s2) i))
  have hv2 : Measurable v2 := by
    refine measurable_pi_iff.2 ?_
    intro i
    simpa [v2] using (measurable_pi_apply (Fin.natAdd (Untyped.numHoles s1) i))
  have hbind_let_of_meas
      (μ : α → Measure Expr)
      (hμ : Measurable μ) :
      Measurable
        (fun v : α =>
          Dist.bind
            (μ v)
            (fun g => Dist.ret (Expr.letE x g (Untyped.fillSkeleton s2 (v2 v))))) :=
    bind_ret_dep_measurable
      (μ := μ) hμ
      (f := fun v g => Expr.letE x g (Untyped.fillSkeleton s2 (v2 v)))
      (hf := let_dep_uncurry_measurable x (e2 := fun v : α => Untyped.fillSkeleton s2 (v2 v)))
  have hsubst_ret
      (val : α → Expr) :
      Measurable
        (fun v : α =>
          Dist.ret (subst x (val v) (Untyped.fillSkeleton s2 (v2 v)))) :=
    subst_dep_ret_measurable x (v := val) (e2 := fun v : α => Untyped.fillSkeleton s2 (v2 v))
  cases s1 with
  | hole =>
      let i0 : Fin (Untyped.numHoles Untyped.Skeleton.hole) := ⟨0, by simp [Untyped.numHoles]⟩
      simpa [Untyped.fillSkeleton, v1, v2, i0] using
        (hsubst_ret (fun v : α => Expr.const ((v1 v) i0)))
  | var y =>
      let μ : α → Measure Expr := fun _ => Untyped.step (Expr.var y)
      have hμ : Measurable μ := measurable_const
      simpa [Untyped.fillSkeleton, v1, v2, μ] using hbind_let_of_meas μ hμ
  | trueE =>
      simpa [Untyped.fillSkeleton, v1, v2] using
        (hsubst_ret (fun _ : α => Expr.trueE))
  | falseE =>
      simpa [Untyped.fillSkeleton, v1, v2] using
        (hsubst_ret (fun _ : α => Expr.falseE))
  | finconst n k =>
      simpa [Untyped.fillSkeleton, v1, v2] using
        (hsubst_ret (fun _ : α => Expr.finconst n k))
  | discrete ps =>
      let μ : α → Measure Expr := fun _ => Untyped.step (Expr.discrete ps)
      have hμ : Measurable μ := measurable_const
      simpa [Untyped.fillSkeleton, v1, v2, μ] using hbind_let_of_meas μ hμ
  | diverge =>
      let μ : α → Measure Expr := fun _ => Untyped.step Expr.diverge
      have hμ : Measurable μ := measurable_const
      simpa [Untyped.fillSkeleton, v1, v2, μ] using hbind_let_of_meas μ hμ
  | lt s11 s12 =>
      let μ : α → Measure Expr := fun v => Untyped.step (Untyped.fillSkeleton (.lt s11 s12) (v1 v))
      have hμ : Measurable μ := by
        simpa [μ, Untyped.fillSkeleton] using ih1.comp hv1
      simpa [Untyped.fillSkeleton, v1, v2, μ] using hbind_let_of_meas μ hμ
  | ifE s11 s12 s13 =>
      let μ : α → Measure Expr := fun v => Untyped.step (Untyped.fillSkeleton (.ifE s11 s12 s13) (v1 v))
      have hμ : Measurable μ := by
        simpa [μ, Untyped.fillSkeleton] using ih1.comp hv1
      simpa [Untyped.fillSkeleton, v1, v2, μ] using hbind_let_of_meas μ hμ
  | letE y s11 s12 =>
      let μ : α → Measure Expr := fun v => Untyped.step (Untyped.fillSkeleton (.letE y s11 s12) (v1 v))
      have hμ : Measurable μ := by
        simpa [μ, Untyped.fillSkeleton] using ih1.comp hv1
      simpa [Untyped.fillSkeleton, v1, v2, μ] using hbind_let_of_meas μ hμ
  | uniform s11 s12 =>
      let μ : α → Measure Expr := fun v => Untyped.step (Untyped.fillSkeleton (.uniform s11 s12) (v1 v))
      have hμ : Measurable μ := by
        simpa [μ, Untyped.fillSkeleton] using ih1.comp hv1
      simpa [Untyped.fillSkeleton, v1, v2, μ] using hbind_let_of_meas μ hμ

lemma step_uniform_slice_measurable
    (s1 s2 : Untyped.Skeleton)
    (ih1 : Measurable (fun v : Fin (Untyped.numHoles s1) → ℝ => Untyped.step (Untyped.fillSkeleton s1 v)))
    (ih2 : Measurable (fun v : Fin (Untyped.numHoles s2) → ℝ => Untyped.step (Untyped.fillSkeleton s2 v))) :
    Measurable (fun v : Fin (Untyped.numHoles s1 + Untyped.numHoles s2) → ℝ =>
      match Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2) i)),
            Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) i)) with
      | Expr.const v1, Expr.const v2 =>
          if v1 ≤ v2 then
            Dist.bind (ProbabilityTheory.cond MeasureTheory.volume (Set.Icc v1 v2))
              (fun r => Dist.ret (Expr.const r))
          else
            Dist.ret Expr.diverge
      | Expr.const v1, _ =>
          Dist.bind
            (Untyped.step (Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) i))))
            (fun g => Dist.ret (Expr.uniform (.const v1) g))
      | _, _ =>
          Dist.bind
            (Untyped.step (Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2) i))))
            (fun g => Dist.ret (Expr.uniform g (Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) i)))))) := by
  classical
  let α := Fin (Untyped.numHoles s1 + Untyped.numHoles s2) → ℝ
  let v1 : α → (Fin (Untyped.numHoles s1) → ℝ) :=
    fun v i => v (Fin.castAdd (Untyped.numHoles s2) i)
  let v2 : α → (Fin (Untyped.numHoles s2) → ℝ) :=
    fun v i => v (Fin.natAdd (Untyped.numHoles s1) i)
  have hv1 : Measurable v1 := by
    refine measurable_pi_iff.2 ?_
    intro i
    simpa [v1] using (measurable_pi_apply (Fin.castAdd (Untyped.numHoles s2) i))
  have hv2 : Measurable v2 := by
    refine measurable_pi_iff.2 ?_
    intro i
    simpa [v2] using (measurable_pi_apply (Fin.natAdd (Untyped.numHoles s1) i))
  by_cases hs1 : s1 = Untyped.Skeleton.hole
  · subst hs1
    let i0 : Fin (Untyped.numHoles Untyped.Skeleton.hole) := ⟨0, by simp [Untyped.numHoles]⟩
    by_cases hs2 : s2 = Untyped.Skeleton.hole
    · subst hs2
      let j0 : Fin (Untyped.numHoles Untyped.Skeleton.hole) := ⟨0, by simp [Untyped.numHoles]⟩
      simpa [v1, v2, i0, j0, Untyped.fillSkeleton] using
        (uniform_const_const_branch_measurable
          (lo := fun v : α => (v1 v) i0)
          (hi := fun v : α => (v2 v) j0))
    · have hEq :
        (fun v : α =>
          match Untyped.fillSkeleton Untyped.Skeleton.hole (v1 v),
                Untyped.fillSkeleton s2 (v2 v) with
          | Expr.const v1, Expr.const v2 =>
              if v1 ≤ v2 then
                Dist.bind (ProbabilityTheory.cond MeasureTheory.volume (Set.Icc v1 v2))
                  (fun r => Dist.ret (Expr.const r))
              else
                Dist.ret Expr.diverge
          | Expr.const v1, _ =>
              Dist.bind
                (Untyped.step (Untyped.fillSkeleton s2 (v2 v)))
                (fun g => Dist.ret (Expr.uniform (.const v1) g))
          | _, _ =>
              Dist.bind
                (Untyped.step (Untyped.fillSkeleton Untyped.Skeleton.hole (v1 v)))
                (fun g => Dist.ret (Expr.uniform g (Untyped.fillSkeleton s2 (v2 v)))))
        =
        (fun v : α =>
          Dist.bind
            (Untyped.step (Untyped.fillSkeleton s2 (v2 v)))
            (fun g =>
              Dist.ret (Expr.uniform (.const ((v1 v) i0)) g))) := by
        funext v
        have hnot2 : ¬ ∃ r : ℝ, Untyped.fillSkeleton s2 (v2 v) = Expr.const r :=
          fillSkeleton_not_const_of_ne_hole hs2 (v2 v)
        cases h2 : Untyped.fillSkeleton s2 (v2 v) with
        | const r =>
            exact (False.elim (hnot2 ⟨r, h2⟩))
        | var _ | trueE | falseE | finconst _ _ | discrete _ | diverge
          | letE _ _ _ | lt _ _ | ifE _ _ _ | uniform _ _ =>
            simpa [Untyped.fillSkeleton, i0]
      rw [hEq]
      let μ : α → Measure Expr := fun v => Untyped.step (Untyped.fillSkeleton s2 (v2 v))
      have hμ : Measurable μ := by
        simpa [μ] using ih2.comp hv2
      have hbind :
          Measurable
            (fun v : α =>
              Dist.bind
                (μ v)
                (fun g => Dist.ret (Expr.uniform (.const ((v1 v) i0)) g))) :=
        bind_ret_dep_measurable
          (μ := μ) hμ
          (f := fun v g => Expr.uniform (.const ((v1 v) i0)) g)
          (hf := uniform_right_dep_uncurry_measurable (r := fun v : α => (v1 v) i0))
      simpa [μ] using hbind
  · have hEq :
      (fun v : α =>
        match Untyped.fillSkeleton s1 (v1 v),
              Untyped.fillSkeleton s2 (v2 v) with
        | Expr.const v1, Expr.const v2 =>
            if v1 ≤ v2 then
              Dist.bind (ProbabilityTheory.cond MeasureTheory.volume (Set.Icc v1 v2))
                (fun r => Dist.ret (Expr.const r))
            else
              Dist.ret Expr.diverge
        | Expr.const v1, _ =>
            Dist.bind
              (Untyped.step (Untyped.fillSkeleton s2 (v2 v)))
              (fun g => Dist.ret (Expr.uniform (.const v1) g))
        | _, _ =>
            Dist.bind
              (Untyped.step (Untyped.fillSkeleton s1 (v1 v)))
              (fun g => Dist.ret (Expr.uniform g (Untyped.fillSkeleton s2 (v2 v)))))
      =
      (fun v : α =>
        Dist.bind
          (Untyped.step (Untyped.fillSkeleton s1 (v1 v)))
          (fun g => Dist.ret (Expr.uniform g (Untyped.fillSkeleton s2 (v2 v))))) := by
      funext v
      have hnot1 : ¬ ∃ r : ℝ, Untyped.fillSkeleton s1 (v1 v) = Expr.const r :=
        fillSkeleton_not_const_of_ne_hole hs1 (v1 v)
      cases h1 : Untyped.fillSkeleton s1 (v1 v) <;> simp [h1] at hnot1 ⊢
    rw [hEq]
    let μ : α → Measure Expr := fun v => Untyped.step (Untyped.fillSkeleton s1 (v1 v))
    have hμ : Measurable μ := by
      simpa [μ] using ih1.comp hv1
    have hbind :
        Measurable
          (fun v : α =>
            Dist.bind
              (μ v)
              (fun g => Dist.ret (Expr.uniform g (Untyped.fillSkeleton s2 (v2 v))))) :=
      bind_ret_dep_measurable
        (μ := μ) hμ
        (f := fun v g => Expr.uniform g (Untyped.fillSkeleton s2 (v2 v)))
        (hf := uniform_left_dep_uncurry_measurable
          (e2 := fun v : α => Untyped.fillSkeleton s2 (v2 v)))
    simpa [μ] using hbind


lemma step_untyped_measurable :
    Measurable (fun e : Expr => Untyped.step e) := by
  refine measurable_of_slices ?_
  intro σ
  induction σ with
  | hole =>
      simp [Untyped.step, Untyped.fillSkeleton, Dist.ret_is_dirac]
  | var x =>
      simp [Untyped.step, Untyped.fillSkeleton, Dist.ret_is_dirac]
  | trueE =>
      simp [Untyped.step, Untyped.fillSkeleton, Dist.ret_is_dirac]
  | falseE =>
      simp [Untyped.step, Untyped.fillSkeleton, Dist.ret_is_dirac]
  | finconst n k =>
      simp [Untyped.step, Untyped.fillSkeleton, Dist.ret_is_dirac]
  | discrete ps =>
      simp [Untyped.step, Untyped.fillSkeleton]
  | diverge =>
      simp [Untyped.step, Untyped.fillSkeleton]
  | lt s1 s2 ih1 ih2 =>
      simpa [Untyped.step, Untyped.fillSkeleton] using
        step_lt_slice_measurable s1 s2 ih1 ih2
  | ifE s1 s2 s3 ih1 ih2 ih3 =>
      simpa [Untyped.step, Untyped.fillSkeleton] using
        step_if_slice_measurable s1 s2 s3 ih1 ih2 ih3
  | letE x s1 s2 ih1 _ =>
      simpa [Untyped.step, Untyped.fillSkeleton] using
        step_let_slice_measurable x s1 s2 ih1
  | uniform s1 s2 ih1 ih2 =>
      simpa [Untyped.step, Untyped.fillSkeleton] using
        step_uniform_slice_measurable s1 s2 ih1 ih2

lemma step_untyped_is_subMarkovKernel :
    IsSubMarkovKernel (fun e : Expr => Untyped.step e) := by
  have bind_is_subprob_measure
      {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
      {μ : Measure α} {k : α → Measure β}
      (hμ : IsSubProbabilityMeasure μ)
      (hk : ∀ x, IsSubProbabilityMeasure (k x))
      (hkm : Measurable k) :
      IsSubProbabilityMeasure (Dist.bind μ k) := by
    unfold IsSubProbabilityMeasure at hμ hk ⊢
    rw [Dist.bind_is_measure_bind, Measure.bind_apply MeasurableSet.univ hkm.aemeasurable]
    calc
      ∫⁻ x, k x Set.univ ∂μ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono (fun x => hk x)
      _ = μ Set.univ := by simp
      _ ≤ 1 := hμ
  refine ⟨step_untyped_measurable, ?_⟩
  intro e
  induction e with
  | diverge =>
      simp [Untyped.step, IsSubProbabilityMeasure]
  | const _ | finconst _ _ | trueE | falseE | var _ =>
      simp [Untyped.step, IsSubProbabilityMeasure, Dist.ret_is_dirac]
  | discrete ps =>
      simp only [Untyped.step]
      let n := ps.1.length
      let discreteMeasure : Dist (Fin n) :=
        Finset.univ.sum (fun i : Fin n => (ps.1.get i) • Dist.ret i)
      exact bind_is_subprob_measure
        (hμ := by
          unfold IsSubProbabilityMeasure
          simpa [discreteMeasure, n, Dist.ret_is_dirac, ps.2] using
            (le_rfl : (1 : ENNReal) ≤ 1))
        (hk := by
          intro i
          simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
        (hkm := by
          simpa [Dist.ret_is_dirac] using
            (MeasureTheory.Measure.measurable_dirac.comp (finconst_wrap_measurable n)))
  | letE x e1 e2 ih1 _ =>
      simp only [Untyped.step]
      split_ifs with hv
      · simp [IsSubProbabilityMeasure, Dist.ret_is_dirac]
      · exact bind_is_subprob_measure
          (hμ := ih1)
          (hk := by
            intro g
            simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
          (hkm := by
            simpa [Dist.ret_is_dirac] using
              (MeasureTheory.Measure.measurable_dirac.comp (let_wrap_measurable x e2)))
  | ifE e1 e2 e3 ih1 _ _ =>
      simp only [Untyped.step]
      split
      · simp [IsSubProbabilityMeasure, Dist.ret_is_dirac]
      · simp [IsSubProbabilityMeasure, Dist.ret_is_dirac]
      · exact bind_is_subprob_measure
          (hμ := ih1)
          (hk := by
            intro g
            simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
          (hkm := by
            simpa [Dist.ret_is_dirac] using
              (MeasureTheory.Measure.measurable_dirac.comp (if_wrap_measurable e2 e3)))
  | lt e1 e2 ih1 ih2 =>
      simp only [Untyped.step]
      split
      · split
        · simp [IsSubProbabilityMeasure, Dist.ret_is_dirac]
        · simp [IsSubProbabilityMeasure, Dist.ret_is_dirac]
      · exact bind_is_subprob_measure
          (hμ := ih2)
          (hk := by
            intro g
            simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
          (hkm := by
            simpa [Dist.ret_is_dirac] using
              (MeasureTheory.Measure.measurable_dirac.comp (lt_right_wrap_measurable _)))
      · exact bind_is_subprob_measure
          (hμ := ih1)
          (hk := by
            intro g
            simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
          (hkm := by
            simpa [Dist.ret_is_dirac] using
              (MeasureTheory.Measure.measurable_dirac.comp (lt_left_wrap_measurable e2)))
  | uniform e1 e2 ih1 ih2 =>
      simp only [Untyped.step]
      split
      · split
        · exact bind_is_subprob_measure
            (hμ := by
              unfold IsSubProbabilityMeasure
              simpa using
                prob_le_one (μ := ProbabilityTheory.cond MeasureTheory.volume (Set.Icc _ _))
                  (s := Set.univ))
            (hk := by
              intro r
              simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
            (hkm := by
              simpa [Dist.ret_is_dirac] using
                (MeasureTheory.Measure.measurable_dirac.comp const_wrap_measurable))
        · simp [IsSubProbabilityMeasure, Dist.ret_is_dirac]
      · exact bind_is_subprob_measure
          (hμ := ih2)
          (hk := by
            intro g
            simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
          (hkm := by
            simpa [Dist.ret_is_dirac] using
              (MeasureTheory.Measure.measurable_dirac.comp (uniform_right_wrap_measurable _)))
      · exact bind_is_subprob_measure
          (hμ := ih1)
          (hk := by
            intro g
            simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
          (hkm := by
            simpa [Dist.ret_is_dirac] using
              (MeasureTheory.Measure.measurable_dirac.comp (uniform_left_wrap_measurable e2)))

end Slice
