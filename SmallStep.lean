import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Measure.Support
import Syntax
import Monad
import Skeleton
import Measurable
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

-- ---------------------------------------------------------------------------
-- 1. Subprobability measure
-- ---------------------------------------------------------------------------

-- Dirac.ret e is a subprobability measure.
lemma ret_is_subprob_measure {α : Type} [MeasurableSpace α] (a : α) :
    IsSubProbabilityMeasure (Dist.ret a) := by
  unfold IsSubProbabilityMeasure
  simp [Dist.ret_is_dirac]

-- Bind preserves subprobability measures.
-- If μ is a subprobability measure and k is a subprobability measure, then μ >>= k is a subprobability measure.
lemma bind_is_subprob_measure {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (k : α → Measure β)
    (hμ : IsSubProbabilityMeasure μ)
    (hk : ∀ x, IsSubProbabilityMeasure (k x))
    (hkm : Measurable k) :
    IsSubProbabilityMeasure (Dist.bind μ k) := by
  unfold IsSubProbabilityMeasure at hμ hk ⊢
  rw [Dist.bind_is_measure_bind, Measure.bind_apply MeasurableSet.univ hkm.aemeasurable]
  exact (lintegral_mono (fun a => hk a)).trans (by simp [hμ])

-- Small-step semantics is a subprobability measure.
lemma step_untyped_is_subprob_measure (e : Expr) :
    IsSubProbabilityMeasure (Untyped.step e) := by
  induction e with
  | diverge =>
      unfold IsSubProbabilityMeasure
      simp [Untyped.step]
  | const _ | finconst _ _ | trueE | falseE | var _ =>
      simp only [Untyped.step]
      exact ret_is_subprob_measure _
  | discrete ps =>
      simp only [Untyped.step]
      apply bind_is_subprob_measure
      · unfold IsSubProbabilityMeasure
        simpa [Dist.ret_is_dirac, ps.2] using (le_rfl : (1 : ENNReal) ≤ 1)
      · intro i; exact ret_is_subprob_measure _
      · simpa [Dist.ret_is_dirac] using
          MeasureTheory.Measure.measurable_dirac.comp (finconst_wrap_measurable _)
  | letE x e1 e2 ih1 _ =>
      simp only [Untyped.step]
      split_ifs
      · exact ret_is_subprob_measure _
      · exact bind_is_subprob_measure _ _ ih1
          (fun _ => ret_is_subprob_measure _)
          (by simpa [Dist.ret_is_dirac] using
            MeasureTheory.Measure.measurable_dirac.comp (let_wrap_measurable x e2))
  | lt e1 e2 ih1 ih2 =>
      simp only [Untyped.step]
      split
      · split
        · exact ret_is_subprob_measure _
        · exact ret_is_subprob_measure _
      · exact bind_is_subprob_measure _ _ ih2
          (fun _ => ret_is_subprob_measure _)
          (by simpa [Dist.ret_is_dirac] using
            MeasureTheory.Measure.measurable_dirac.comp (lt_right_wrap_measurable _))
      · exact bind_is_subprob_measure _ _ ih1
          (fun _ => ret_is_subprob_measure _)
          (by simpa [Dist.ret_is_dirac] using
            MeasureTheory.Measure.measurable_dirac.comp (lt_left_wrap_measurable e2))
  | ifE e1 e2 e3 ih1 _ _ =>
      simp only [Untyped.step]
      split
      · exact ret_is_subprob_measure _
      · exact ret_is_subprob_measure _
      · exact bind_is_subprob_measure _ _ ih1
          (fun _ => ret_is_subprob_measure _)
          (by simpa [Dist.ret_is_dirac] using
            MeasureTheory.Measure.measurable_dirac.comp (if_wrap_measurable e2 e3))
  | uniform e1 e2 ih1 ih2 =>
      simp only [Untyped.step]
      split
      · split
        · apply bind_is_subprob_measure
          · unfold IsSubProbabilityMeasure
            simpa using prob_le_one (μ := ProbabilityTheory.cond volume (Set.Icc _ _)) (s := Set.univ)
          · intro _; exact ret_is_subprob_measure _
          · simpa [Dist.ret_is_dirac] using
              MeasureTheory.Measure.measurable_dirac.comp const_wrap_measurable
        · exact ret_is_subprob_measure _
      · exact bind_is_subprob_measure _ _ ih2
          (fun _ => ret_is_subprob_measure _)
          (by simpa [Dist.ret_is_dirac] using
            MeasureTheory.Measure.measurable_dirac.comp (uniform_right_wrap_measurable _))
      · exact bind_is_subprob_measure _ _ ih1
          (fun _ => ret_is_subprob_measure _)
          (by simpa [Dist.ret_is_dirac] using
            MeasureTheory.Measure.measurable_dirac.comp (uniform_left_wrap_measurable e2))

lemma step_is_subprob_measure {τ : Ty} (e : ExprsOfType τ) :
    IsSubProbabilityMeasure (step e) := by
  classical
  have hUntyped := step_untyped_is_subprob_measure e.1
  unfold step IsSubProbabilityMeasure at hUntyped ⊢
  let f : Expr → ExprsOfType τ :=
    fun e' => if h : HasType Ctx.empty e' τ then (⟨e', h⟩ : ExprsOfType τ) else e
  by_cases hf : AEMeasurable
      f
      (Untyped.step e.1)
  · calc
      (Measure.map f (Untyped.step e.1)) Set.univ
          = (Untyped.step e.1) Set.univ := by
            rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ, Set.preimage_univ]
      _ ≤ 1 := hUntyped
  · rw [Measure.map_of_not_aemeasurable hf]
    change (0 : ENNReal) ≤ 1
    exact zero_le (1 : ENNReal)

-- ---------------------------------------------------------------------------
-- 2. Measurability
-- ---------------------------------------------------------------------------

-- At a high-level:
-- From `Measurable (fun e => Untyped.step e)`, transform the goal to `∀ σ, Measurable (fun v => Untyped.step (Untyped.fillSkeleton σ v))` by applying fillSkeleton_measurable_expr.
-- Fix σ. Prove by induction on σ.

/-- If a skeleton is not `hole`, filling it can never produce `Expr.const r`. -/
lemma fillSkeleton_not_const_of_ne_hole
    {s : Untyped.Skeleton}
    (hs : s ≠ Untyped.Skeleton.hole) :
    ∀ v : Fin (Untyped.numHoles s) → ℝ, ¬ ∃ r : ℝ, Untyped.fillSkeleton s v = Expr.const r := by
  intro v
  cases s <;> simp [Untyped.fillSkeleton] at hs ⊢

/-- If a skeleton is not `trueE`, filling it can never be exactly `Expr.trueE`. -/
lemma fillSkeleton_not_true_of_ne_trueE
    {s : Untyped.Skeleton}
    (hs : s ≠ Untyped.Skeleton.trueE) :
    ∀ v : Fin (Untyped.numHoles s) → ℝ, Untyped.fillSkeleton s v ≠ Expr.trueE := by
  intro v
  cases s <;> simp [Untyped.fillSkeleton] at hs ⊢

/-- If a skeleton is not `falseE`, filling it can never be exactly `Expr.falseE`. -/
lemma fillSkeleton_not_false_of_ne_falseE
    {s : Untyped.Skeleton}
    (hs : s ≠ Untyped.Skeleton.falseE) :
    ∀ v : Fin (Untyped.numHoles s) → ℝ, Untyped.fillSkeleton s v ≠ Expr.falseE := by
  intro v
  cases s <;> simp [Untyped.fillSkeleton] at hs ⊢


/-- If μ is measurable and each (μ a) is a subprobability, and F is measurable, then a ↦ bind (μ a) (fun g => ret (F a g)) is measurable. -/
lemma bind_is_measurable
    {α : Type} [MeasurableSpace α]
    {μ : α → Measure Expr}
    (hμ : Measurable μ)
    (hμ_sub : ∀ a : α, IsSubProbabilityMeasure (μ a))
    {F : α → Expr → Expr}
    (hF : Measurable (Function.uncurry F)) :
    Measurable
      (fun a : α => Dist.bind (μ a) (fun g => Dist.ret (F a g))) := by
  let μK : Kernel α Expr := ⟨μ, hμ⟩
  have hμK_fin : IsFiniteKernel μK := by
    refine ⟨⟨1, by simp, by intro a; exact hμ_sub a⟩⟩
  letI : IsFiniteKernel μK := hμK_fin
  have hκ_meas :
      Measurable
        (Function.uncurry
          (fun a : α => fun g : Expr => (Measure.dirac (F a g) : Measure Expr))) := by
    simpa [Function.uncurry] using (MeasureTheory.Measure.measurable_dirac.comp hF)
  let κK : Kernel (α × Expr) Expr :=
    ⟨fun p => Measure.dirac (F p.1 p.2),
     by simpa [Function.uncurry] using hκ_meas⟩
  have hEq :
      (fun a : α => Dist.bind (μ a) (fun g => Dist.ret (F a g))) =
      (fun a : α => ((κK ∘ₖ Kernel.prod Kernel.id μK) a : Measure Expr)) := by
    funext a
    ext s hs
    rw [Dist.bind_is_measure_bind,
        Measure.bind_apply hs
          (by
            simpa [Dist.ret_is_dirac] using
              (MeasureTheory.Measure.measurable_dirac.comp
                (Measurable.of_uncurry_left (f := F) hF (x := a))).aemeasurable),
        Kernel.comp_apply' _ _ _ hs,
        Kernel.lintegral_id_prod
          (hf := Kernel.measurable_coe κK hs)
          (κ := μK) (a := a) (f := fun p : α × Expr => κK p s)]
    simp [κK, μK, Dist.ret_is_dirac]
  rw [hEq]
  exact Kernel.measurable _

/-- Filling an if skeleton with a hole assignment v is measurable. -/
lemma step_if_slice_measurable
    (s1 s2 s3 : Untyped.Skeleton)
    (ih1 : Measurable (fun v : Fin (Untyped.numHoles s1) → ℝ =>
      Untyped.step (Untyped.fillSkeleton s1 v))) :
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

  -- Split a single combined hole assignment into projections v1, v2, v3 (for condition/then/else holes)
  let v1 : α → (Fin (Untyped.numHoles s1) → ℝ) :=
    fun v i => v (Fin.castAdd (Untyped.numHoles s2 + Untyped.numHoles s3) i)
  let v2 : α → (Fin (Untyped.numHoles s2) → ℝ) :=
    fun v i => v (Fin.natAdd (Untyped.numHoles s1) (Fin.castAdd (Untyped.numHoles s3) i))
  let v3 : α → (Fin (Untyped.numHoles s3) → ℝ) :=
    fun v i => v (Fin.natAdd (Untyped.numHoles s1) (Fin.natAdd (Untyped.numHoles s2) i))

  -- Prove each projection v1, v2, v3 is measurable
  have hv1 : Measurable v1 := by
    exact measurable_pi_iff.2 (fun i => by
      simpa [v1] using
        (measurable_pi_apply (Fin.castAdd (Untyped.numHoles s2 + Untyped.numHoles s3) i)))
  have hv2 : Measurable v2 := by
    exact measurable_pi_iff.2 (fun i => by
      simpa [v2] using
        (measurable_pi_apply (Fin.natAdd (Untyped.numHoles s1) (Fin.castAdd (Untyped.numHoles s3) i))))
  have hv3 : Measurable v3 := by
    exact measurable_pi_iff.2 (fun i => by
      simpa [v3] using
        (measurable_pi_apply (Fin.natAdd (Untyped.numHoles s1) (Fin.natAdd (Untyped.numHoles s2) i))))

  -- Define c, t, f as the filled condition/then/else expressions.
  let c : α → Expr := fun v => Untyped.fillSkeleton s1 (v1 v)
  let t : α → Expr := fun v => Untyped.fillSkeleton s2 (v2 v)
  let f : α → Expr := fun v => Untyped.fillSkeleton s3 (v3 v)

  -- Case split on s1.
  by_cases hs1t : s1 = Untyped.Skeleton.trueE
  -- if s1 = trueE, expression is always ret (t v). This is measurable by measurable_dirac.
  · subst hs1t
    simpa [Dist.ret_is_dirac] using
      (MeasureTheory.Measure.measurable_dirac.comp ((fillSkeleton_measurable_skel s2).comp hv2))
  · by_cases hs1f : s1 = Untyped.Skeleton.falseE
    -- if s1 = false, expression is always ret (f v). This is measurable by measurable_dirac.
    · subst hs1f
      simpa [Dist.ret_is_dirac] using
        (MeasureTheory.Measure.measurable_dirac.comp ((fillSkeleton_measurable_skel s3).comp hv3))
    -- Otherwise `c v` can never be `trueE`/`falseE`; only the bind works.
    · have hEq :
          (fun v : α =>
            match c v with
            | Expr.trueE  => Dist.ret (t v)
            | Expr.falseE => Dist.ret (f v)
            | _           => Dist.bind (Untyped.step (c v)) (fun g => Dist.ret (Expr.ifE g (t v) (f v))))
          =
          (fun v : α =>
            Dist.bind (Untyped.step (c v)) (fun g => Dist.ret (Expr.ifE g (t v) (f v)))) := by
          funext v
          have hnt : c v ≠ Expr.trueE :=
            fillSkeleton_not_true_of_ne_trueE hs1t (v1 v)
          have hnf : c v ≠ Expr.falseE :=
            fillSkeleton_not_false_of_ne_falseE hs1f (v1 v)
          cases hc : c v <;> simp [hc] at hnt hnf ⊢

      rw [hEq]
      -- Bind is measurable. Obtain measurability of (v,g) ↦ ifE g (t v) (f v) from if_dep_uncurry_measurable.
      exact
        bind_is_measurable
          (by simpa [c] using ih1.comp hv1)
          (fun v : α => step_untyped_is_subprob_measure (c v))
          (if_dep_uncurry_measurable
            (t := t) (f := f)
            (by simpa [t] using ((fillSkeleton_measurable_skel s2).comp hv2))
            (by simpa [f] using ((fillSkeleton_measurable_skel s3).comp hv3)))


/-- Filling a lt skeleton with a hole assignment v is measurable. -/
lemma step_lt_slice_measurable
    (s1 s2 : Untyped.Skeleton)
    (ih1 : Measurable (fun v : Fin (Untyped.numHoles s1) → ℝ =>
      Untyped.step (Untyped.fillSkeleton s1 v)))
    (ih2 : Measurable (fun v : Fin (Untyped.numHoles s2) → ℝ =>
      Untyped.step (Untyped.fillSkeleton s2 v))) :
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
  -- Split a single combined hole assignment into projections v1, v2 (for lhs/rhs holes)
  let v1 : α → (Fin (Untyped.numHoles s1) → ℝ) :=
    fun v i => v (Fin.castAdd (Untyped.numHoles s2) i)
  let v2 : α → (Fin (Untyped.numHoles s2) → ℝ) :=
    fun v i => v (Fin.natAdd (Untyped.numHoles s1) i)
  -- Prove each projection v1, v2 is measurable
  have hv1 : Measurable v1 := by
    exact measurable_pi_iff.2 (fun i => by
      simpa [v1] using (measurable_pi_apply (Fin.castAdd (Untyped.numHoles s2) i)))
  have hv2 : Measurable v2 := by
    exact measurable_pi_iff.2 (fun i => by
      simpa [v2] using (measurable_pi_apply (Fin.natAdd (Untyped.numHoles s1) i)))

  -- Define l, r as the filled lhs/rhs expressions of the lt expression. Get measurability of l and r from IH.
  let l : α → Expr := fun v => Untyped.fillSkeleton s1 (v1 v)
  let r : α → Expr := fun v => Untyped.fillSkeleton s2 (v2 v)
  have hμl : Measurable (fun v : α => Untyped.step (l v)) := by
    simpa [l] using ih1.comp hv1
  have hμr : Measurable (fun v : α => Untyped.step (r v)) := by
    simpa [r] using ih2.comp hv2

  -- Case split on s1.
  by_cases hs1 : s1 = Untyped.Skeleton.hole
  · subst hs1
    let i0 : Fin (Untyped.numHoles Untyped.Skeleton.hole) := ⟨0, by simp [Untyped.numHoles]⟩
    -- If both sides are holes, we are in the pure const/const branch and measurability is an `ite`.
    by_cases hs2 : s2 = Untyped.Skeleton.hole
    · subst hs2
      have hlt :
          MeasurableSet
            {v : α | v (Fin.castAdd 1 (0 : Fin 1)) < v (Fin.natAdd 1 (0 : Fin 1))} := by
        simpa [Untyped.numHoles] using
          (measurableSet_lt
            (measurable_pi_apply (Fin.castAdd 1 (0 : Fin 1)))
            (measurable_pi_apply (Fin.natAdd 1 (0 : Fin 1))))
      exact Measurable.ite hlt measurable_const measurable_const
    -- Left is const, right is never const: collapse to the right-bind branch.
    · have hEq :
          (fun v : α =>
            match l v, r v with
            | Expr.const v1, Expr.const v2 =>
                if v1 < v2 then (Dist.ret Expr.trueE : Dist Expr)
                else (Dist.ret Expr.falseE : Dist Expr)
            | Expr.const v1, _ =>
                Dist.bind (Untyped.step (r v)) (fun g => Dist.ret (Expr.lt (.const v1) g))
            | _, _ =>
                Dist.bind (Untyped.step (l v)) (fun g => Dist.ret (Expr.lt g (r v))))
          =
          (fun v : α =>
            Dist.bind (Untyped.step (r v))
              (fun g => Dist.ret (Expr.lt (.const ((v1 v) i0)) g))) := by
        funext v
        have hnot2 : ¬ ∃ rr : ℝ, Untyped.fillSkeleton s2 (v2 v) = Expr.const rr :=
          fillSkeleton_not_const_of_ne_hole hs2 (v2 v)
        cases hr : r v with
        | const rr =>
            exact False.elim (hnot2 ⟨rr, by simpa [r] using hr⟩)
        | var _ | trueE | falseE | finconst _ _ | discrete _ | diverge
          | letE _ _ _ | lt _ _ | ifE _ _ _ | uniform _ _ =>
            simp [l, r, Untyped.fillSkeleton, i0]
      rw [hEq]
      -- Final closure: measurable input kernel + measurable `(v,g) ↦ lt (const ...) g`.
      exact
        bind_is_measurable
          hμr
          (fun v : α => step_untyped_is_subprob_measure (r v))
          (lt_right_dep_uncurry_measurable
            (r := fun v : α => (v1 v) i0)
            ((measurable_pi_apply i0).comp hv1))
  -- Left is never const: collapse to the fallback left-bind branch.
  · have hEq :
        (fun v : α =>
          match l v, r v with
          | Expr.const v1, Expr.const v2 =>
              if v1 < v2 then (Dist.ret Expr.trueE : Dist Expr)
              else (Dist.ret Expr.falseE : Dist Expr)
          | Expr.const v1, _ =>
              Dist.bind (Untyped.step (r v)) (fun g => Dist.ret (Expr.lt (.const v1) g))
          | _, _ =>
              Dist.bind (Untyped.step (l v)) (fun g => Dist.ret (Expr.lt g (r v))))
        =
        (fun v : α =>
          Dist.bind (Untyped.step (l v)) (fun g => Dist.ret (Expr.lt g (r v)))) := by
      funext v
      have hnot1 : ¬ ∃ rr : ℝ, Untyped.fillSkeleton s1 (v1 v) = Expr.const rr :=
        fillSkeleton_not_const_of_ne_hole hs1 (v1 v)
      cases hl : l v with
      | const rr =>
          exact False.elim (hnot1 ⟨rr, by simpa [l] using hl⟩)
      | var _ | trueE | falseE | finconst _ _ | discrete _ | diverge
        | letE _ _ _ | lt _ _ | ifE _ _ _ | uniform _ _ =>
          simp [l, r]
    rw [hEq]
    have hr : Measurable r := by
      simpa [r] using ((fillSkeleton_measurable_skel s2).comp hv2)
    -- Final closure: measurable input kernel + measurable `(v,g) ↦ lt g (r v)`.
    exact
      bind_is_measurable
        hμl
        (fun v : α => step_untyped_is_subprob_measure (l v))
        (lt_left_dep_uncurry_measurable (e2 := r) hr)


/-- Filling a let skeleton with a hole assignment v is measurable. -/
lemma step_let_slice_measurable
    (x : String) (s1 s2 : Untyped.Skeleton)
    (ih1 : Measurable (fun v : Fin (Untyped.numHoles s1) → ℝ =>
      Untyped.step (Untyped.fillSkeleton s1 v)))
    (ih2 : Measurable (fun v : Fin (Untyped.numHoles s2) → ℝ =>
      Untyped.step (Untyped.fillSkeleton s2 v))) :
    Measurable (fun v : Fin (Untyped.numHoles s1 + Untyped.numHoles s2) → ℝ =>
      if isValue (Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2) i))) then
        Dist.ret
          (subst x
            (Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2) i)))
            (Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) i))))
      else
        Dist.bind
          (Untyped.step (Untyped.fillSkeleton s1 (fun i => v (Fin.castAdd (Untyped.numHoles s2) i))))
          (fun g => Dist.ret (Expr.letE x g (Untyped.fillSkeleton s2 (fun i => v (Fin.natAdd (Untyped.numHoles s1) i)))))) := by
  classical
  let α := Fin (Untyped.numHoles s1 + Untyped.numHoles s2) → ℝ
  -- Project one combined hole-assignment into lhs/rhs assignments.
  let v1 : α → (Fin (Untyped.numHoles s1) → ℝ) :=
    fun v i => v (Fin.castAdd (Untyped.numHoles s2) i)
  let v2 : α → (Fin (Untyped.numHoles s2) → ℝ) :=
    fun v i => v (Fin.natAdd (Untyped.numHoles s1) i)
  have hv1 : Measurable v1 := by
    exact measurable_pi_iff.2 (fun i => by
      simpa [v1] using (measurable_pi_apply (Fin.castAdd (Untyped.numHoles s2) i)))
  have hv2 : Measurable v2 := by
    exact measurable_pi_iff.2 (fun i => by
      simpa [v2] using (measurable_pi_apply (Fin.natAdd (Untyped.numHoles s1) i)))

  -- Abbreviate filled subexpressions.
  let e1 : α → Expr := fun v => Untyped.fillSkeleton s1 (v1 v)
  let e2 : α → Expr := fun v => Untyped.fillSkeleton s2 (v2 v)
  have he2 : Measurable e2 := by
    simpa [e2] using ((fillSkeleton_measurable_skel s2).comp hv2)
  have _ : Measurable (fun v : α => Untyped.step (Untyped.fillSkeleton s2 (v2 v))) := by
    simpa [v2] using ih2.comp hv2
  have hμ : Measurable (fun v : α => Untyped.step (e1 v)) := by
    simpa [e1] using ih1.comp hv1
  -- Measurability of the non-value branch: bind the step of `e1` and rebuild `letE`.
  have hbind :
      Measurable
        (fun v : α =>
          Dist.bind (Untyped.step (e1 v)) (fun g => Dist.ret (Expr.letE x g (e2 v)))) := by
    letI : ∀ v : α, IsFiniteMeasure (Untyped.step (e1 v)) := fun v =>
      ⟨lt_of_le_of_lt (step_untyped_is_subprob_measure (e1 v)) (by simp)⟩
    letI : ∀ v : α, SFinite (Untyped.step (e1 v)) := fun v => inferInstance
    exact
      bind_is_measurable
        hμ
        (fun v : α => step_untyped_is_subprob_measure (e1 v))
        (let_dep_uncurry_measurable x (e2 := e2) he2)
  -- Measurability of the value branch: `ret (subst ...)`.
  have hsubst :
      Measurable (fun v : α => (Dist.ret (subst x (e1 v) (e2 v)) : Dist Expr)) :=
    subst_dep_ret_measurable x (v := e1) (e2 := e2)

  -- Finish by case-splitting on the shape of `s1`; this determines whether `isValue (e1 v)` is always true or false.
  cases s1 with
  | hole =>
      let i0 : Fin (Untyped.numHoles Untyped.Skeleton.hole) := ⟨0, by simp [Untyped.numHoles]⟩
      simpa [e1, e2, Untyped.fillSkeleton, i0] using hsubst
  | var _ =>
      simpa [e1, e2, Untyped.fillSkeleton] using hbind
  | trueE =>
      simpa [e1, e2, Untyped.fillSkeleton] using hsubst
  | falseE =>
      simpa [e1, e2, Untyped.fillSkeleton] using hsubst
  | finconst _ _ =>
      simpa [e1, e2, Untyped.fillSkeleton] using hsubst
  | discrete _ =>
      simpa [e1, e2, Untyped.fillSkeleton] using hbind
  | diverge =>
      simpa [e1, e2, Untyped.fillSkeleton] using hbind
  | lt _ _ =>
      simpa [e1, e2, Untyped.fillSkeleton] using hbind
  | ifE _ _ _ =>
      simpa [e1, e2, Untyped.fillSkeleton] using hbind
  | letE _ _ _ =>
      simpa [e1, e2, Untyped.fillSkeleton] using hbind
  | uniform _ _ =>
      simpa [e1, e2, Untyped.fillSkeleton] using hbind


/-- Filling a uniform skeleton with a hole assignment v is measurable. -/
lemma step_uniform_slice_measurable
    (s1 s2 : Untyped.Skeleton)
    (ih1 : Measurable (fun v : Fin (Untyped.numHoles s1) → ℝ =>
      Untyped.step (Untyped.fillSkeleton s1 v)))
    (ih2 : Measurable (fun v : Fin (Untyped.numHoles s2) → ℝ =>
      Untyped.step (Untyped.fillSkeleton s2 v))) :
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
  -- Project one combined hole-assignment into left/right assignments.
  let v1 : α → (Fin (Untyped.numHoles s1) → ℝ) :=
    fun v i => v (Fin.castAdd (Untyped.numHoles s2) i)
  let v2 : α → (Fin (Untyped.numHoles s2) → ℝ) :=
    fun v i => v (Fin.natAdd (Untyped.numHoles s1) i)
  have hv1 : Measurable v1 := by
    exact measurable_pi_iff.2 (fun i => by
      simpa [v1] using (measurable_pi_apply (Fin.castAdd (Untyped.numHoles s2) i)))
  have hv2 : Measurable v2 := by
    exact measurable_pi_iff.2 (fun i => by
      simpa [v2] using (measurable_pi_apply (Fin.natAdd (Untyped.numHoles s1) i)))

  -- Abbreviate filled left/right subexpressions and their stepped kernels.
  let l : α → Expr := fun v => Untyped.fillSkeleton s1 (v1 v)
  let r : α → Expr := fun v => Untyped.fillSkeleton s2 (v2 v)
  have hμl : Measurable (fun v : α => Untyped.step (l v)) := by
    simpa [l] using ih1.comp hv1
  have hμr : Measurable (fun v : α => Untyped.step (r v)) := by
    simpa [r] using ih2.comp hv2

  -- Split on whether the left skeleton is a hole (so left side is definitely const).
  by_cases hs1 : s1 = Untyped.Skeleton.hole
  · subst hs1
    let i0 : Fin (Untyped.numHoles Untyped.Skeleton.hole) := ⟨0, by simp [Untyped.numHoles]⟩
    -- If both are holes, use the dedicated measurable lemma for the const/const uniform branch.
    by_cases hs2 : s2 = Untyped.Skeleton.hole
    · subst hs2
      let j0 : Fin (Untyped.numHoles Untyped.Skeleton.hole) := ⟨0, by simp [Untyped.numHoles]⟩
      simpa [l, r, v1, v2, i0, j0, Untyped.fillSkeleton] using
        (uniform_const_const_branch_measurable
          (lo := fun v : α => (v1 v) i0)
          (hi := fun v : α => (v2 v) j0))
    -- Left is const, right is never const: collapse to the right-bind branch.
    · have hEq :
          (fun v : α =>
            match l v, r v with
            | Expr.const v1, Expr.const v2 =>
                if v1 ≤ v2 then
                  Dist.bind (ProbabilityTheory.cond MeasureTheory.volume (Set.Icc v1 v2))
                    (fun r => Dist.ret (Expr.const r))
                else
                  Dist.ret Expr.diverge
            | Expr.const v1, _ =>
                Dist.bind (Untyped.step (r v)) (fun g => Dist.ret (Expr.uniform (.const v1) g))
            | _, _ =>
                Dist.bind (Untyped.step (l v)) (fun g => Dist.ret (Expr.uniform g (r v))))
          =
          (fun v : α =>
            Dist.bind (Untyped.step (r v))
              (fun g => Dist.ret (Expr.uniform (.const ((v1 v) i0)) g))) := by
        funext v
        have hnot2 : ¬ ∃ rr : ℝ, Untyped.fillSkeleton s2 (v2 v) = Expr.const rr :=
          fillSkeleton_not_const_of_ne_hole hs2 (v2 v)
        cases hr : r v with
        | const rr =>
            exact False.elim (hnot2 ⟨rr, by simpa [r] using hr⟩)
        | var _ | trueE | falseE | finconst _ _ | discrete _ | diverge
          | letE _ _ _ | lt _ _ | ifE _ _ _ | uniform _ _ =>
            simp [l, r, Untyped.fillSkeleton, i0, hr]
      rw [hEq]
      -- Final closure: measurable input kernel + measurable `(v,g) ↦ uniform (const ...) g`.
      letI : ∀ v : α, IsFiniteMeasure (Untyped.step (r v)) := fun v =>
        ⟨lt_of_le_of_lt (step_untyped_is_subprob_measure (r v)) (by simp)⟩
      letI : ∀ v : α, SFinite (Untyped.step (r v)) := fun v => inferInstance
      exact
        bind_is_measurable
          hμr
          (fun v : α => step_untyped_is_subprob_measure (r v))
          (uniform_right_dep_uncurry_measurable
            (r := fun v : α => (v1 v) i0)
            ((measurable_pi_apply i0).comp hv1))
  -- Left is never const: collapse to the fallback left-bind branch.
  · have hEq :
        (fun v : α =>
          match l v, r v with
          | Expr.const v1, Expr.const v2 =>
              if v1 ≤ v2 then
                Dist.bind (ProbabilityTheory.cond MeasureTheory.volume (Set.Icc v1 v2))
                  (fun r => Dist.ret (Expr.const r))
              else
                Dist.ret Expr.diverge
          | Expr.const v1, _ =>
              Dist.bind (Untyped.step (r v)) (fun g => Dist.ret (Expr.uniform (.const v1) g))
          | _, _ =>
              Dist.bind (Untyped.step (l v)) (fun g => Dist.ret (Expr.uniform g (r v))))
        =
        (fun v : α =>
          Dist.bind (Untyped.step (l v)) (fun g => Dist.ret (Expr.uniform g (r v)))) := by
      funext v
      have hnot1 : ¬ ∃ rr : ℝ, Untyped.fillSkeleton s1 (v1 v) = Expr.const rr :=
        fillSkeleton_not_const_of_ne_hole hs1 (v1 v)
      cases hl : l v with
      | const rr =>
          exact False.elim (hnot1 ⟨rr, by simpa [l] using hl⟩)
      | var _ | trueE | falseE | finconst _ _ | discrete _ | diverge
        | letE _ _ _ | lt _ _ | ifE _ _ _ | uniform _ _ =>
          simp [l, r, hl]
    rw [hEq]
    have hr : Measurable r := by
      simpa [r] using ((fillSkeleton_measurable_skel s2).comp hv2)
    -- Final closure: measurable input kernel + measurable `(v,g) ↦ uniform g (r v)`.
    exact
      bind_is_measurable
        hμl
        (fun v : α => step_untyped_is_subprob_measure (l v))
        (uniform_left_dep_uncurry_measurable (e2 := r) hr)

lemma step_untyped_measurable :
    Measurable (fun e : Expr => Untyped.step e) := by
  apply fillSkeleton_measurable_expr (f := fun e : Expr => Untyped.step e)
  -- this changes the goal from global Measurable (fun e => Untyped.step e) to: for each skeleton σ, prove measurability of v ↦ Untyped.step (Untyped.fillSkeleton σ v).
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
  | ifE s1 s2 s3 ih1 _ _ =>
      simpa [Untyped.step, Untyped.fillSkeleton] using
        step_if_slice_measurable s1 s2 s3 ih1
  | letE x s1 s2 ih1 ih2 =>
      simpa [Untyped.step, Untyped.fillSkeleton] using
        step_let_slice_measurable x s1 s2 ih1 ih2
  | uniform s1 s2 ih1 ih2 =>
      simpa [Untyped.step, Untyped.fillSkeleton] using
        step_uniform_slice_measurable s1 s2 ih1 ih2

lemma step_untyped_is_subMarkovKernel :
    IsSubMarkovKernel (fun e : Expr => Untyped.step e) := by
  exact ⟨step_untyped_measurable, step_untyped_is_subprob_measure⟩

lemma step_is_subMarkovKernel {τ : Ty} :
    IsSubMarkovKernel (fun e : ExprsOfType τ => step e) := by sorry

end Slice
