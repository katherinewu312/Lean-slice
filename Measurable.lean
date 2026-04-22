import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Support
import Syntax
import Monad
import Skeleton
import TypeSystem

namespace Slice

open MeasureTheory ProbabilityTheory

-- ------------------------------------------------------------------------
-- Helper lemmas regarding measurable functions.
-- These are for the small-step semantics is a Markov kernel proof
-- (namely for the measurability condition).
-- ------------------------------------------------------------------------

/-- v ↦ fillSkeleton σ v is measurable (where σ is fixed).
This is proved by showing: (hole values) → ExprsOfSkel σ → Expr -/
lemma fillSkeleton_measurable_skel (σ : Untyped.Skeleton) :
    Measurable
      (fun v : (Fin (Untyped.numHoles σ) → ℝ) =>
        (Untyped.fillSkeleton σ v : Expr)) := by
  have hsymm : Measurable (Untyped.exprsOfSkel_equiv σ).symm := by
    rw [measurable_comap_iff]
    simpa using (measurable_id : Measurable (fun x : Fin (Untyped.numHoles σ) → ℝ => x))
  have hcoe : Measurable (fun x : Untyped.ExprsOfSkel σ => x.1) := by
    intro s hs
    simpa [Set.preimage] using (hs σ)
  have h :
      Measurable
        (fun v : Fin (Untyped.numHoles σ) → ℝ => ((Untyped.exprsOfSkel_equiv σ).symm v).1) :=
    hcoe.comp hsymm
  simpa [Untyped.exprsOfSkel_equiv, Untyped.fillSkeleton] using h

/-- If each skeleton-indexed hole map `v ↦ f (fillSkeleton σ v)` is measurable, then `f` is measurable on `Expr`.
This is proved by showing: For every measurable set `s` and every skeleton `σ`, the set of expressions in that `σ`-slice that land in `s` under `f` comes from a measurable set of hole assignments. -/
lemma fillSkeleton_measurable_expr
    {β : Type} [MeasurableSpace β]
    (f : Expr → β)
    (h : ∀ σ : Untyped.Skeleton,
      Measurable
        (fun v : (Fin (Untyped.numHoles σ) → ℝ) =>
          f (Untyped.fillSkeleton σ v))) :
    Measurable f := by
  intro s hs σ
  refine ⟨
    {v : Fin (Untyped.numHoles σ) → ℝ | f (Untyped.fillSkeleton σ v) ∈ s},
    (h σ) hs,
    by
      ext p
      have hfill :
          Untyped.fillSkeleton σ (Untyped.exprsOfSkel_equiv σ p) = p.1 := by
        simpa [Untyped.exprsOfSkel_equiv] using
          congrArg Subtype.val ((Untyped.exprsOfSkel_equiv σ).left_inv p)
      simp [Set.preimage, hfill]⟩

/-- A measurable embedding is a function that is: injective, measurable, and whose measurable sets stay measurale when you push them forward along the map. -/
lemma fillSkeleton_measurableEmbedding (σ : Untyped.Skeleton) :
    MeasurableEmbedding
      (fun v : (Fin (Untyped.numHoles σ) → ℝ) =>
        (Untyped.fillSkeleton σ v : Expr)) := by
  refine ⟨Untyped.fillSkeleton_injective σ, fillSkeleton_measurable_skel σ, ?_⟩
  intro s hs τ
  by_cases hτσ : τ = σ
  · cases hτσ
    have hset :
        {p : Untyped.ExprsOfSkel σ | p.1 ∈ Untyped.fillSkeleton σ '' s} =
          {p : Untyped.ExprsOfSkel σ | Untyped.exprsOfSkel_equiv σ p ∈ s} := by
      ext p
      constructor
      · intro hp
        rcases hp with ⟨v, hvs, hvp⟩
        have hfill :
            Untyped.fillSkeleton σ (Untyped.exprsOfSkel_equiv σ p) = p.1 := by
          simpa [Untyped.exprsOfSkel_equiv] using
            congrArg Subtype.val ((Untyped.exprsOfSkel_equiv σ).left_inv p)
        have hvEq : v = Untyped.exprsOfSkel_equiv σ p := by
          apply Untyped.fillSkeleton_injective σ
          simpa [hfill] using hvp
        simpa [hvEq] using hvs
      · intro hp
        have hfill :
            Untyped.fillSkeleton σ (Untyped.exprsOfSkel_equiv σ p) = p.1 := by
          simpa [Untyped.exprsOfSkel_equiv] using
            congrArg Subtype.val ((Untyped.exprsOfSkel_equiv σ).left_inv p)
        exact ⟨Untyped.exprsOfSkel_equiv σ p, hp, by simpa [hfill]⟩
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨s, hs, ?_⟩
    have hset' :
        {p : Untyped.ExprsOfSkel σ | (∃ x ∈ s, Untyped.fillSkeleton σ x = p.1)} =
          {p : Untyped.ExprsOfSkel σ | Untyped.exprsOfSkel_equiv σ p ∈ s} := by
      simpa [Set.mem_image] using hset
    simpa [Set.preimage, hset']
  · have hempty :
        {p : Untyped.ExprsOfSkel τ | p.1 ∈ Untyped.fillSkeleton σ '' s} = ∅ := by
      ext p
      constructor
      · intro hp
        rcases hp with ⟨v, hvs, hvp⟩
        have hτσ' : τ = σ := by
          calc
            τ = Untyped.skeletonOf p.1 := by simpa using p.2.symm
            _ = Untyped.skeletonOf (Untyped.fillSkeleton σ v) := by simpa [hvp]
            _ = σ := Untyped.skeletonOf_fillSkeleton σ v
        exact (hτσ hτσ').elim
      · intro hp
        exact False.elim (by simpa using hp)
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨∅, MeasurableSet.empty, ?_⟩
    simpa [Set.mem_image] using hempty.symm

lemma fillSkeleton_prod_measurableEmbedding
    {α : Type} [MeasurableSpace α] :
    ∀ σ : Untyped.Skeleton,
      MeasurableEmbedding
        (fun p : α × (Fin (Untyped.numHoles σ) → ℝ) =>
          (p.1, Untyped.fillSkeleton σ p.2)) := by
  intro σ
  simpa [Prod.map] using
    (MeasurableEmbedding.id.prodMap
      (fillSkeleton_measurableEmbedding σ))

lemma measurable_of_slices_prod_right
    {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    [Countable Untyped.Skeleton]
    {f : α × Expr → β}
    (h : ∀ σ : Untyped.Skeleton,
      Measurable
        (fun p : α × (Fin (Untyped.numHoles σ) → ℝ) =>
          f (p.1, Untyped.fillSkeleton σ p.2))) :
    Measurable f := by
  classical
  let i : (σ : Untyped.Skeleton) →
      α × (Fin (Untyped.numHoles σ) → ℝ) → α × Expr :=
    fun σ p => (p.1, Untyped.fillSkeleton σ p.2)
  intro s hs
  have hP :
      f ⁻¹' s =
        ⋃ σ : Untyped.Skeleton,
          i σ '' {p : α × (Fin (Untyped.numHoles σ) → ℝ) | i σ p ∈ f ⁻¹' s} := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.2 ?_
      refine ⟨Untyped.skeletonOf x.2, ?_⟩
      refine ⟨(x.1, Untyped.holeValues x.2), ?_, ?_⟩
      · simpa [i, Untyped.fillSkeleton_holeValues] using hx
      · simp [i, Untyped.fillSkeleton_holeValues]
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨σ, hxσ⟩
      rcases hxσ with ⟨p, hpP, rfl⟩
      exact hpP
  rw [hP]
  refine MeasurableSet.iUnion ?_
  intro σ
  have hpre :
      MeasurableSet {p : α × (Fin (Untyped.numHoles σ) → ℝ) | i σ p ∈ f ⁻¹' s} := by
    simpa [i, Set.preimage] using (h σ) hs
  exact (fillSkeleton_prod_measurableEmbedding (α := α) σ).measurableSet_image' hpre



/-- Uncurry measurability for `(a,g) ↦ lt g (e₂ a)`. -/
lemma lt_left_dep_uncurry_measurable
    {α : Type}
    [MeasurableSpace α]
    {e2 : α → Expr}
    (he2 : Measurable e2) :
    Measurable (Function.uncurry (fun a : α => fun g : Expr => Expr.lt g (e2 a))) := by
  classical
  have hbase : Measurable (fun p : Expr × Expr => Expr.lt p.1 p.2) := by
    refine measurable_of_slices_prod_right
      (f := fun p : Expr × Expr => Expr.lt p.1 p.2) ?_
    intro σr
    have hF :
        Measurable
          (fun q : (Fin (Untyped.numHoles σr) → ℝ) × Expr =>
            Expr.lt q.2 (Untyped.fillSkeleton σr q.1)) := by
      refine measurable_of_slices_prod_right
        (f := fun q : (Fin (Untyped.numHoles σr) → ℝ) × Expr =>
          Expr.lt q.2 (Untyped.fillSkeleton σr q.1)) ?_
      intro σl
      let combine :
          ((Fin (Untyped.numHoles σr) → ℝ) × (Fin (Untyped.numHoles σl) → ℝ)) →
            (Fin (Untyped.numHoles (Untyped.Skeleton.lt σl σr)) → ℝ) :=
        fun u =>
          Fin.addCases
            (fun il : Fin (Untyped.numHoles σl) => u.2 il)
            (fun ir : Fin (Untyped.numHoles σr) => u.1 ir)
      have hcombine : Measurable combine := by
        refine measurable_pi_iff.2 ?_
        intro i
        rcases hsum : (finSumFinEquiv.symm i) with il | ir
        · have hi : i = Fin.castAdd (Untyped.numHoles σr) il := by
            have htmp := congrArg finSumFinEquiv hsum
            simpa [finSumFinEquiv_apply_left] using htmp
          simpa [combine, hi] using
            ((measurable_pi_apply il).comp measurable_snd)
        · have hi : i = Fin.natAdd (Untyped.numHoles σl) ir := by
            have htmp := congrArg finSumFinEquiv hsum
            simpa [finSumFinEquiv_apply_right] using htmp
          simpa [combine, hi] using
            ((measurable_pi_apply ir).comp measurable_fst)
      have hfill :
          Measurable
            (fun v : Fin (Untyped.numHoles (Untyped.Skeleton.lt σl σr)) → ℝ =>
              Untyped.fillSkeleton (Untyped.Skeleton.lt σl σr) v) :=
        fillSkeleton_measurable_skel (σ := Untyped.Skeleton.lt σl σr)
      have hcomp :
          Measurable
            (fun u : (Fin (Untyped.numHoles σr) → ℝ) × (Fin (Untyped.numHoles σl) → ℝ) =>
              Untyped.fillSkeleton (Untyped.Skeleton.lt σl σr) (combine u)) :=
        hfill.comp hcombine
      simpa [combine, Untyped.fillSkeleton] using hcomp
    have hswap :
        Measurable (fun p : Expr × (Fin (Untyped.numHoles σr) → ℝ) => (p.2, p.1)) :=
      measurable_snd.prodMk measurable_fst
    simpa using hF.comp hswap
  have hargs : Measurable (fun p : α × Expr => (p.2, e2 p.1)) :=
    measurable_snd.prodMk (he2.comp measurable_fst)
  simpa [Function.uncurry] using hbase.comp hargs

/-- Uncurry measurability for `(a,g) ↦ lt (const (r a)) g`. -/
lemma lt_right_dep_uncurry_measurable
    {α : Type}
    [MeasurableSpace α]
    {r : α → ℝ}
    (hr : Measurable r) :
    Measurable (Function.uncurry (fun a : α => fun g : Expr => Expr.lt (.const (r a)) g)) := by
  have hconstVec :
      Measurable (fun a : α => (fun _ : Fin (Untyped.numHoles Untyped.Skeleton.hole) => r a)) := by
    refine measurable_pi_iff.2 ?_
    intro i
    have : (fun a : α => (fun _ : Fin (Untyped.numHoles Untyped.Skeleton.hole) => r a) i) = r := by
      funext a
      simp
    simpa [this] using hr
  have hconst : Measurable (fun a : α => Expr.const (r a)) := by
    simpa [Untyped.fillSkeleton] using
      ((fillSkeleton_measurable_skel (σ := Untyped.Skeleton.hole)).comp hconstVec)
  have hlt_swapped :
      Measurable
        (Function.uncurry (fun a : Expr => fun g : Expr => Expr.lt g a)) := by
    simpa using
      (lt_left_dep_uncurry_measurable
        (α := Expr) (e2 := fun a : Expr => a) measurable_id)
  have hargs : Measurable (fun p : α × Expr => (p.2, Expr.const (r p.1))) :=
    measurable_snd.prodMk (hconst.comp measurable_fst)
  simpa [Function.uncurry] using hlt_swapped.comp hargs

lemma if_dep_uncurry_measurable
    {α : Type} [MeasurableSpace α]
    {t f : α → Expr}
    (ht : Measurable t) (hf : Measurable f) :
    Measurable (Function.uncurry (fun a => fun g => Expr.ifE g (t a) (f a))) := by
  classical
  have hbase :
      Measurable (fun p : (Expr × Expr) × Expr => Expr.ifE p.2 p.1.1 p.1.2) := by
    refine measurable_of_slices_prod_right
      (f := fun p : (Expr × Expr) × Expr => Expr.ifE p.2 p.1.1 p.1.2) ?_
    intro σg
    have hF :
        Measurable
          (fun q : (Expr × (Fin (Untyped.numHoles σg) → ℝ)) × Expr =>
            Expr.ifE (Untyped.fillSkeleton σg q.1.2) q.1.1 q.2) := by
      refine measurable_of_slices_prod_right
        (f := fun q : (Expr × (Fin (Untyped.numHoles σg) → ℝ)) × Expr =>
          Expr.ifE (Untyped.fillSkeleton σg q.1.2) q.1.1 q.2) ?_
      intro σf
      have hG :
          Measurable
            (fun r : ((Fin (Untyped.numHoles σg) → ℝ) × (Fin (Untyped.numHoles σf) → ℝ)) × Expr =>
              Expr.ifE (Untyped.fillSkeleton σg r.1.1) r.2 (Untyped.fillSkeleton σf r.1.2)) := by
        refine measurable_of_slices_prod_right
          (f := fun r :
            ((Fin (Untyped.numHoles σg) → ℝ) × (Fin (Untyped.numHoles σf) → ℝ)) × Expr =>
            Expr.ifE (Untyped.fillSkeleton σg r.1.1) r.2 (Untyped.fillSkeleton σf r.1.2)) ?_
        intro σt
        let combine :
            (((Fin (Untyped.numHoles σg) → ℝ) × (Fin (Untyped.numHoles σf) → ℝ)) ×
                (Fin (Untyped.numHoles σt) → ℝ)) →
              (Fin (Untyped.numHoles (Untyped.Skeleton.ifE σg σt σf)) → ℝ) :=
          fun u =>
            Fin.addCases
              (fun ig : Fin (Untyped.numHoles σg) => u.1.1 ig)
              (fun j : Fin (Untyped.numHoles σt + Untyped.numHoles σf) =>
                Fin.addCases
                  (fun it : Fin (Untyped.numHoles σt) => u.2 it)
                  (fun iff : Fin (Untyped.numHoles σf) => u.1.2 iff)
                  j)
        have hcombine : Measurable combine := by
          refine measurable_pi_iff.2 ?_
          intro i
          rcases hsum : (finSumFinEquiv.symm i) with ig | j
          · have hi : i = Fin.castAdd (Untyped.numHoles σt + Untyped.numHoles σf) ig := by
              have htmp := congrArg finSumFinEquiv hsum
              simpa [finSumFinEquiv_apply_left] using htmp
            simpa [combine, hi] using
              ((measurable_pi_apply ig).comp (measurable_fst.comp measurable_fst))
          · have hi : i = Fin.natAdd (Untyped.numHoles σg) j := by
              have htmp := congrArg finSumFinEquiv hsum
              simpa [finSumFinEquiv_apply_right] using htmp
            rcases hsum2 : (finSumFinEquiv.symm j) with it | iff
            · have hj : j = Fin.castAdd (Untyped.numHoles σf) it := by
                have htmp := congrArg finSumFinEquiv hsum2
                simpa [finSumFinEquiv_apply_left] using htmp
              simpa [combine, hi, hj] using
                ((measurable_pi_apply it).comp measurable_snd)
            · have hj : j = Fin.natAdd (Untyped.numHoles σt) iff := by
                have htmp := congrArg finSumFinEquiv hsum2
                simpa [finSumFinEquiv_apply_right] using htmp
              simpa [combine, hi, hj] using
                ((measurable_pi_apply iff).comp (measurable_snd.comp measurable_fst))
        have hfill :
            Measurable
              (fun v : Fin (Untyped.numHoles (Untyped.Skeleton.ifE σg σt σf)) → ℝ =>
                Untyped.fillSkeleton (Untyped.Skeleton.ifE σg σt σf) v) :=
          fillSkeleton_measurable_skel (σ := Untyped.Skeleton.ifE σg σt σf)
        have hcomp :
            Measurable
              (fun u : ((Fin (Untyped.numHoles σg) → ℝ) × (Fin (Untyped.numHoles σf) → ℝ)) ×
                  (Fin (Untyped.numHoles σt) → ℝ) =>
                Untyped.fillSkeleton (Untyped.Skeleton.ifE σg σt σf) (combine u)) :=
          hfill.comp hcombine
        simpa [combine, Untyped.fillSkeleton] using hcomp
      have hswapf :
          Measurable
            (fun p : (Expr × (Fin (Untyped.numHoles σg) → ℝ)) × (Fin (Untyped.numHoles σf) → ℝ) =>
              ((p.1.2, p.2), p.1.1)) :=
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd).prodMk
          (measurable_fst.comp measurable_fst)
      simpa using hG.comp hswapf
    have hswap0 :
        Measurable
          (fun p : (Expr × Expr) × (Fin (Untyped.numHoles σg) → ℝ) =>
            ((p.1.1, p.2), p.1.2)) :=
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst)
    simpa using hF.comp hswap0
  have hswap : Measurable (fun p : Expr × (Expr × Expr) => (p.2, p.1)) :=
    measurable_snd.prodMk measurable_fst
  have hunc :
      Measurable
        (Function.uncurry
          (fun g : Expr => fun q : Expr × Expr => Expr.ifE g q.1 q.2)) := by
    simpa [Function.uncurry] using hbase.comp hswap
  have htf : Measurable (fun a : α => (t a, f a)) := ht.prodMk hf
  have hargs : Measurable (fun p : α × Expr => (p.2, (t p.1, f p.1))) :=
    measurable_snd.prodMk (htf.comp measurable_fst)
  simpa [Function.uncurry] using hunc.comp hargs


/-- Uncurry measurability for `(a,g) ↦ uniform g (e₂ a)`. -/
lemma uniform_left_dep_uncurry_measurable
    {α : Type}
    [MeasurableSpace α]
    {e2 : α → Expr}
    (he2 : Measurable e2) :
    Measurable (Function.uncurry (fun a : α => fun g : Expr => Expr.uniform g (e2 a))) := by
  classical
  have hbase : Measurable (fun p : Expr × Expr => Expr.uniform p.1 p.2) := by
    refine measurable_of_slices_prod_right
      (f := fun p : Expr × Expr => Expr.uniform p.1 p.2) ?_
    intro σr
    have hF :
        Measurable
          (fun q : (Fin (Untyped.numHoles σr) → ℝ) × Expr =>
            Expr.uniform q.2 (Untyped.fillSkeleton σr q.1)) := by
      refine measurable_of_slices_prod_right
        (f := fun q : (Fin (Untyped.numHoles σr) → ℝ) × Expr =>
          Expr.uniform q.2 (Untyped.fillSkeleton σr q.1)) ?_
      intro σl
      let combine :
          ((Fin (Untyped.numHoles σr) → ℝ) × (Fin (Untyped.numHoles σl) → ℝ)) →
            (Fin (Untyped.numHoles (Untyped.Skeleton.uniform σl σr)) → ℝ) :=
        fun u =>
          Fin.addCases
            (fun il : Fin (Untyped.numHoles σl) => u.2 il)
            (fun ir : Fin (Untyped.numHoles σr) => u.1 ir)
      have hcombine : Measurable combine := by
        refine measurable_pi_iff.2 ?_
        intro i
        rcases hsum : (finSumFinEquiv.symm i) with il | ir
        · have hi : i = Fin.castAdd (Untyped.numHoles σr) il := by
            have htmp := congrArg finSumFinEquiv hsum
            simpa [finSumFinEquiv_apply_left] using htmp
          simpa [combine, hi] using
            ((measurable_pi_apply il).comp measurable_snd)
        · have hi : i = Fin.natAdd (Untyped.numHoles σl) ir := by
            have htmp := congrArg finSumFinEquiv hsum
            simpa [finSumFinEquiv_apply_right] using htmp
          simpa [combine, hi] using
            ((measurable_pi_apply ir).comp measurable_fst)
      have hfill :
          Measurable
            (fun v : Fin (Untyped.numHoles (Untyped.Skeleton.uniform σl σr)) → ℝ =>
              Untyped.fillSkeleton (Untyped.Skeleton.uniform σl σr) v) :=
        fillSkeleton_measurable_skel (σ := Untyped.Skeleton.uniform σl σr)
      have hcomp :
          Measurable
            (fun u : (Fin (Untyped.numHoles σr) → ℝ) × (Fin (Untyped.numHoles σl) → ℝ) =>
              Untyped.fillSkeleton (Untyped.Skeleton.uniform σl σr) (combine u)) :=
        hfill.comp hcombine
      simpa [combine, Untyped.fillSkeleton] using hcomp
    have hswap :
        Measurable (fun p : Expr × (Fin (Untyped.numHoles σr) → ℝ) => (p.2, p.1)) :=
      measurable_snd.prodMk measurable_fst
    simpa using hF.comp hswap
  have hargs : Measurable (fun p : α × Expr => (p.2, e2 p.1)) :=
    measurable_snd.prodMk (he2.comp measurable_fst)
  simpa [Function.uncurry] using hbase.comp hargs

/-- Uncurry measurability for `(a,g) ↦ uniform (const (r a)) g`. -/
lemma uniform_right_dep_uncurry_measurable
    {α : Type}
    [MeasurableSpace α]
    {r : α → ℝ}
    (hr : Measurable r) :
    Measurable (Function.uncurry (fun a : α => fun g : Expr => Expr.uniform (.const (r a)) g)) := by
  have hconstVec :
      Measurable (fun a : α => (fun _ : Fin (Untyped.numHoles Untyped.Skeleton.hole) => r a)) := by
    refine measurable_pi_iff.2 ?_
    intro i
    have : (fun a : α => (fun _ : Fin (Untyped.numHoles Untyped.Skeleton.hole) => r a) i) = r := by
      funext a
      simp
    simpa [this] using hr
  have hconst : Measurable (fun a : α => Expr.const (r a)) := by
    simpa [Untyped.fillSkeleton] using
      ((fillSkeleton_measurable_skel (σ := Untyped.Skeleton.hole)).comp hconstVec)
  have hunif_swapped :
      Measurable
        (Function.uncurry (fun a : Expr => fun g : Expr => Expr.uniform g a)) := by
    simpa using
      (uniform_left_dep_uncurry_measurable
        (α := Expr) (e2 := fun a : Expr => a) measurable_id)
  have hargs : Measurable (fun p : α × Expr => (p.2, Expr.const (r p.1))) :=
    measurable_snd.prodMk (hconst.comp measurable_fst)
  simpa [Function.uncurry] using hunif_swapped.comp hargs

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
lemma let_dep_uncurry_measurable
    {α : Type}
    [MeasurableSpace α]
    (x : String)
    {e2 : α → Expr}
    (he2 : Measurable e2) :
    Measurable (Function.uncurry (fun a : α => fun g : Expr => Expr.letE x g (e2 a))) := by
  classical
  have hbase : Measurable (fun p : Expr × Expr => Expr.letE x p.1 p.2) := by
    refine measurable_of_slices_prod_right
      (f := fun p : Expr × Expr => Expr.letE x p.1 p.2) ?_
    intro σr
    have hF :
        Measurable
          (fun q : (Fin (Untyped.numHoles σr) → ℝ) × Expr =>
            Expr.letE x q.2 (Untyped.fillSkeleton σr q.1)) := by
      refine measurable_of_slices_prod_right
        (f := fun q : (Fin (Untyped.numHoles σr) → ℝ) × Expr =>
          Expr.letE x q.2 (Untyped.fillSkeleton σr q.1)) ?_
      intro σl
      let combine :
          ((Fin (Untyped.numHoles σr) → ℝ) × (Fin (Untyped.numHoles σl) → ℝ)) →
            (Fin (Untyped.numHoles (Untyped.Skeleton.letE x σl σr)) → ℝ) :=
        fun u =>
          Fin.addCases
            (fun il : Fin (Untyped.numHoles σl) => u.2 il)
            (fun ir : Fin (Untyped.numHoles σr) => u.1 ir)
      have hcombine : Measurable combine := by
        refine measurable_pi_iff.2 ?_
        intro i
        rcases hsum : (finSumFinEquiv.symm i) with il | ir
        · have hi : i = Fin.castAdd (Untyped.numHoles σr) il := by
            have htmp := congrArg finSumFinEquiv hsum
            simpa [finSumFinEquiv_apply_left] using htmp
          simpa [combine, hi] using
            ((measurable_pi_apply il).comp measurable_snd)
        · have hi : i = Fin.natAdd (Untyped.numHoles σl) ir := by
            have htmp := congrArg finSumFinEquiv hsum
            simpa [finSumFinEquiv_apply_right] using htmp
          simpa [combine, hi] using
            ((measurable_pi_apply ir).comp measurable_fst)
      have hfill :
          Measurable
            (fun v : Fin (Untyped.numHoles (Untyped.Skeleton.letE x σl σr)) → ℝ =>
              Untyped.fillSkeleton (Untyped.Skeleton.letE x σl σr) v) :=
        fillSkeleton_measurable_skel (σ := Untyped.Skeleton.letE x σl σr)
      have hcomp :
          Measurable
            (fun u : (Fin (Untyped.numHoles σr) → ℝ) × (Fin (Untyped.numHoles σl) → ℝ) =>
              Untyped.fillSkeleton (Untyped.Skeleton.letE x σl σr) (combine u)) :=
        hfill.comp hcombine
      simpa [combine, Untyped.fillSkeleton] using hcomp
    have hswap :
        Measurable (fun p : Expr × (Fin (Untyped.numHoles σr) → ℝ) => (p.2, p.1)) :=
      measurable_snd.prodMk measurable_fst
    simpa using hF.comp hswap
  have hargs : Measurable (fun p : α × Expr => (p.2, e2 p.1)) :=
    measurable_snd.prodMk (he2.comp measurable_fst)
  simpa [Function.uncurry] using hbase.comp hargs

/-- Measurability of `a ↦ ret (subst x (v a) (e₂ a))`. -/
axiom subst_dep_ret_measurable
    {α : Type}
    [MeasurableSpace α]
    (x : String)
    {v e2 : α → Expr} :
    Measurable (fun a : α => (Dist.ret (subst x (v a) (e2 a)) : Dist Expr))


-- Measurable lemmas
-- Each f is a measurable function.
lemma let_wrap_measurable (x : String) (e2 : Expr) :
    Measurable (fun g : Expr => Expr.letE x g e2) := by
  have hunc :
      Measurable
        (Function.uncurry (fun _ : Unit => fun g : Expr => Expr.letE x g e2)) := by
    simpa using
      (let_dep_uncurry_measurable
        (α := Unit) x (e2 := fun _ : Unit => e2) measurable_const)
  simpa using
    (Measurable.of_uncurry_left
      (f := fun _ : Unit => fun g : Expr => Expr.letE x g e2)
      hunc (x := ()))

lemma lt_left_wrap_measurable (e2 : Expr) :
    Measurable (fun g : Expr => Expr.lt g e2) := by
  have hunc :
      Measurable
        (Function.uncurry (fun _ : Unit => fun g : Expr => Expr.lt g e2)) := by
    simpa using
      (lt_left_dep_uncurry_measurable
        (α := Unit) (e2 := fun _ : Unit => e2) measurable_const)
  simpa using
    (Measurable.of_uncurry_left
      (f := fun _ : Unit => fun g : Expr => Expr.lt g e2)
      hunc (x := ()))

lemma lt_right_wrap_measurable (v1 : ℝ) :
    Measurable (fun g : Expr => Expr.lt (.const v1) g) := by
  have hunc :
      Measurable
        (Function.uncurry (fun _ : Unit => fun g : Expr => Expr.lt (.const v1) g)) := by
    simpa using
      (lt_right_dep_uncurry_measurable
        (α := Unit) (r := fun _ : Unit => v1) measurable_const)
  simpa using
    (Measurable.of_uncurry_left
      (f := fun _ : Unit => fun g : Expr => Expr.lt (.const v1) g)
      hunc (x := ()))

lemma if_wrap_measurable (e2 e3 : Expr) :
    Measurable (fun g : Expr => Expr.ifE g e2 e3) := by
  have hunc :
      Measurable
        (Function.uncurry (fun _ : Unit => fun g : Expr => Expr.ifE g e2 e3)) := by
    simpa using
      (if_dep_uncurry_measurable
        (α := Unit) (t := fun _ : Unit => e2) (f := fun _ : Unit => e3)
        measurable_const measurable_const)
  simpa using
    (Measurable.of_uncurry_left
      (f := fun _ : Unit => fun g : Expr => Expr.ifE g e2 e3)
      hunc (x := ()))

lemma uniform_left_wrap_measurable (e2 : Expr) :
    Measurable (fun g : Expr => Expr.uniform g e2) := by
  have hunc :
      Measurable
        (Function.uncurry (fun _ : Unit => fun g : Expr => Expr.uniform g e2)) := by
    simpa using
      (uniform_left_dep_uncurry_measurable
        (α := Unit) (e2 := fun _ : Unit => e2) measurable_const)
  simpa using
    (Measurable.of_uncurry_left
      (f := fun _ : Unit => fun g : Expr => Expr.uniform g e2)
      hunc (x := ()))

lemma uniform_right_wrap_measurable (v1 : ℝ) :
    Measurable (fun g : Expr => Expr.uniform (.const v1) g) := by
  have hunc :
      Measurable
        (Function.uncurry (fun _ : Unit => fun g : Expr => Expr.uniform (.const v1) g)) := by
    simpa using
      (uniform_right_dep_uncurry_measurable
        (α := Unit) (r := fun _ : Unit => v1) measurable_const)
  simpa using
    (Measurable.of_uncurry_left
      (f := fun _ : Unit => fun g : Expr => Expr.uniform (.const v1) g)
      hunc (x := ()))

lemma const_wrap_measurable :
    Measurable (fun r : ℝ => Expr.const r) := by
  sorry

lemma finconst_wrap_measurable (n : Nat) :
    Measurable (fun i : Fin n => Expr.finconst n i) := by
  sorry

end Slice
