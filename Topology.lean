import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Support
import Syntax
import Monad
import Skeleton
import TypeSystem

namespace Slice

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace Untyped

/-- Transport the Euclidean topology on `Fin (numHoles σ) → ℝ` across the
    bijection `exprsOfSkel_equiv σ` to get a topology on `ExprsOfSkel σ`. -/
noncomputable instance exprsOfSkel_topologicalSpace (σ : Skeleton) :
    TopologicalSpace (ExprsOfSkel σ) :=
  TopologicalSpace.induced (exprsOfSkel_equiv σ) inferInstance

noncomputable instance exprsOfSkel_t1Space (σ : Skeleton) :
    T1Space (ExprsOfSkel σ) :=
  (exprsOfSkel_equiv σ).injective.isEmbedding_induced.t1Space

/-- The disjoint-union topology on `Expr`:
    a set `S` is open iff for every skeleton `σ`, the slice
    `{ p : ExprsOfSkel σ | p.1 ∈ S }` is open in `ExprsOfSkel σ`. -/
instance expr_topologicalSpace : TopologicalSpace Expr where
  IsOpen S :=
    ∀ σ : Skeleton,
      IsOpen { p : ExprsOfSkel σ | p.1 ∈ S }
  isOpen_univ := by
    intro σ
    simp
  isOpen_inter := by
    intro S T hS hT σ
    have hSσ : IsOpen { p : ExprsOfSkel σ | p.1 ∈ S } := hS σ
    have hTσ : IsOpen { p : ExprsOfSkel σ | p.1 ∈ T } := hT σ
    have hEq :
        { p : ExprsOfSkel σ | p.1 ∈ S ∩ T } =
          ({ p : ExprsOfSkel σ | p.1 ∈ S } ∩ { p : ExprsOfSkel σ | p.1 ∈ T }) := by
      ext p
      simp
    rw [hEq]
    exact hSσ.inter hTσ
  isOpen_sUnion := by
    intro 𝒮 h𝒮 σ
    have hEq :
        { p : ExprsOfSkel σ | p.1 ∈ ⋃₀ 𝒮 } =
          ⋃ s ∈ 𝒮, ({ p : ExprsOfSkel σ | p.1 ∈ s } : Set (ExprsOfSkel σ)) := by
      ext p
      simp [Set.mem_sUnion]
    rw [hEq]
    exact isOpen_iUnion (fun s => isOpen_iUnion (fun hs => h𝒮 s hs σ))

instance expr_t1Space : T1Space Expr := by
  refine t1Space_iff_exists_open.2 ?_
  intro x y hxy
  refine ⟨({y}ᶜ : Set Expr), ?_, by simpa using hxy, by simp⟩
  intro σ
  by_cases hs : skeletonOf y = σ
  · let py : ExprsOfSkel σ := ⟨y, hs⟩
    have hset :
        { p : ExprsOfSkel σ | p.1 ∈ ({y}ᶜ : Set Expr) } =
          (({py} : Set (ExprsOfSkel σ))ᶜ) := by
      ext p
      constructor
      · intro hp
        intro hp'
        rcases Set.mem_singleton_iff.mp hp' with hp'
        apply hp
        exact congrArg Subtype.val hp'
      · intro hp
        have hp' : p ≠ py := by
          simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hp
        have hpy : p.1 ≠ y := by
          intro hpe
          apply hp'
          apply Subtype.ext
          simpa [py, hpe]
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hpy
    rw [hset]
    exact isOpen_compl_iff.mpr isClosed_singleton
  · have hset :
        { p : ExprsOfSkel σ | p.1 ∈ ({y}ᶜ : Set Expr) } =
          (Set.univ : Set (ExprsOfSkel σ)) := by
      ext p
      constructor
      · intro _
        simp
      · intro _
        have hpy : p.1 ≠ y := by
          intro hpe
          have : skeletonOf y = σ := by
            simpa [hpe] using p.2
          exact (hs this).elim
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hpy
    rw [hset]
    simp

end Untyped

-- ---------------------------------------------------------------------------
-- Topology on well-typed expressions
-- ---------------------------------------------------------------------------

noncomputable instance exprsOfType_topologicalSpace (τ : Ty) :
    TopologicalSpace (ExprsOfType τ) :=
  TopologicalSpace.induced (fun x : ExprsOfType τ => x.1) inferInstance

noncomputable instance exprsOfSkel_topologicalSpace {τ : Ty} (σ : SkeletonsOfType τ) :
    TopologicalSpace (ExprsOfSkel σ) :=
  TopologicalSpace.induced (exprsOfSkel_equiv σ) inferInstance

-- The support of a Dirac measure is exactly the singleton containing its point: support(δₐ) = {a}.
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
If you first sample some a from μ, and then deterministically return f a, then any point in the support of the result must come from some support point a of the source.
y ∈ support(μ.bind(λa, δ f(a)​)) ↔ ∃a ∈ μ.support, y = f(a).
This is the generic lemma that the constructor-specific `[simp]` lemmas will use.
-/
lemma _root_.MeasureTheory.Measure.mem_support_bind_dirac_iff
    {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α]
    [TopologicalSpace β] [MeasurableSpace β]
    (μ : Measure α) (f : α → β)
    (hf_meas : Measurable f)
    (hf_emb : Topology.IsClosedEmbedding f)
    {y : β} :
    y ∈ (Measure.bind μ (fun a => Measure.dirac (f a))).support
      ↔ ∃ a ∈ μ.support, y = f a := by
  sorry

-- For μ >>= f, f is measurable.
-- Measurable lemmas
-- Each f is a measurable function.
lemma let_wrap_measurable (x : String) (e2 : Expr) :
    Measurable (fun g : Expr => Expr.letE x g e2) := by
  sorry

lemma if_wrap_measurable (e2 e3 : Expr) :
    Measurable (fun g : Expr => Expr.ifE g e2 e3) := by
  sorry

lemma lt_left_wrap_measurable (e2 : Expr) :
    Measurable (fun g : Expr => Expr.lt g e2) := by
  sorry

lemma lt_right_wrap_measurable (v1 : ℝ) :
    Measurable (fun g : Expr => Expr.lt (.const v1) g) := by
  sorry

lemma uniform_left_wrap_measurable (e2 : Expr) :
    Measurable (fun g : Expr => Expr.uniform g e2) := by
  sorry

lemma uniform_right_wrap_measurable (v1 : ℝ) :
    Measurable (fun g : Expr => Expr.uniform (.const v1) g) := by
  sorry

lemma const_wrap_measurable :
    Measurable (fun r : ℝ => Expr.const r) := by
  sorry

lemma finconst_wrap_measurable (n : Nat) :
    Measurable (fun i : Fin n => Expr.finconst n i) := by
  sorry

-- Closed-embedding lemmas.
-- Each f is a closed embedding. This means: it is injective, it preserves the topology of the source, and its image is a closed subset of the target.
lemma let_wrap_closedEmbedding (x : String) (e2 : Expr) :
    Topology.IsClosedEmbedding (fun g : Expr => Expr.letE x g e2) := by
  sorry

lemma if_wrap_closedEmbedding (e2 e3 : Expr) :
    Topology.IsClosedEmbedding (fun g : Expr => Expr.ifE g e2 e3) := by
  sorry

lemma lt_left_wrap_closedEmbedding (e2 : Expr) :
    Topology.IsClosedEmbedding (fun g : Expr => Expr.lt g e2) := by
  sorry

lemma lt_right_wrap_closedEmbedding (v1 : ℝ) :
    Topology.IsClosedEmbedding (fun g : Expr => Expr.lt (.const v1) g) := by
  sorry

lemma uniform_left_wrap_closedEmbedding (e2 : Expr) :
    Topology.IsClosedEmbedding (fun g : Expr => Expr.uniform g e2) := by
  sorry

lemma uniform_right_wrap_closedEmbedding (v1 : ℝ) :
    Topology.IsClosedEmbedding (fun g : Expr => Expr.uniform (.const v1) g) := by
  sorry

lemma const_isClosedEmbedding :
    Topology.IsClosedEmbedding (fun r : ℝ => Expr.const r) := by
  sorry

lemma finconst_isClosedEmbedding (n : Nat) :
    Topology.IsClosedEmbedding (fun i : Fin n => Expr.finconst n i) := by
  sorry

--
@[simp] lemma mem_support_bind_letE_iff
    (μ : Measure Expr) (x : String) (e2 e' : Expr) :
    e' ∈ (Measure.bind μ (fun g => Measure.dirac (Expr.letE x g e2))).support
      ↔ ∃ g ∈ μ.support, e' = Expr.letE x g e2 := by
  simpa using
    (MeasureTheory.Measure.mem_support_bind_dirac_iff
      (μ := μ)
      (f := fun g : Expr => Expr.letE x g e2)
      (hf_meas := let_wrap_measurable x e2)
      (hf_emb := let_wrap_closedEmbedding x e2)
      (y := e'))

@[simp] lemma mem_support_bind_ifE_iff
    (μ : Measure Expr) (e2 e3 e' : Expr) :
    e' ∈ (Measure.bind μ (fun g => Measure.dirac (Expr.ifE g e2 e3))).support
      ↔ ∃ g ∈ μ.support, e' = Expr.ifE g e2 e3 := by
  simpa using
    (MeasureTheory.Measure.mem_support_bind_dirac_iff
      (μ := μ)
      (f := fun g : Expr => Expr.ifE g e2 e3)
      (hf_meas := if_wrap_measurable e2 e3)
      (hf_emb := if_wrap_closedEmbedding e2 e3)
      (y := e'))

@[simp] lemma mem_support_bind_lt_left_iff
    (μ : Measure Expr) (e2 e' : Expr) :
    e' ∈ (Measure.bind μ (fun g => Measure.dirac (Expr.lt g e2))).support
      ↔ ∃ g ∈ μ.support, e' = Expr.lt g e2 := by
  simpa using
    (MeasureTheory.Measure.mem_support_bind_dirac_iff
      (μ := μ)
      (f := fun g : Expr => Expr.lt g e2)
      (hf_meas := lt_left_wrap_measurable e2)
      (hf_emb := lt_left_wrap_closedEmbedding e2)
      (y := e'))

@[simp] lemma mem_support_bind_lt_right_iff
    (μ : Measure Expr) (v1 : ℝ) (e' : Expr) :
    e' ∈ (Measure.bind μ (fun g => Measure.dirac (Expr.lt (.const v1) g))).support
      ↔ ∃ g ∈ μ.support, e' = Expr.lt (.const v1) g := by
  simpa using
    (MeasureTheory.Measure.mem_support_bind_dirac_iff
      (μ := μ)
      (f := fun g : Expr => Expr.lt (.const v1) g)
      (hf_meas := lt_right_wrap_measurable v1)
      (hf_emb := lt_right_wrap_closedEmbedding v1)
      (y := e'))

@[simp] lemma mem_support_bind_uniform_left_iff
    (μ : Measure Expr) (e2 e' : Expr) :
    e' ∈ (Measure.bind μ (fun g => Measure.dirac (Expr.uniform g e2))).support
      ↔ ∃ g ∈ μ.support, e' = Expr.uniform g e2 := by
  simpa using
    (MeasureTheory.Measure.mem_support_bind_dirac_iff
      (μ := μ)
      (f := fun g : Expr => Expr.uniform g e2)
      (hf_meas := uniform_left_wrap_measurable e2)
      (hf_emb := uniform_left_wrap_closedEmbedding e2)
      (y := e'))

@[simp] lemma mem_support_bind_uniform_right_iff
    (μ : Measure Expr) (v1 : ℝ) (e' : Expr) :
    e' ∈ (Measure.bind μ (fun g => Measure.dirac (Expr.uniform (.const v1) g))).support
      ↔ ∃ g ∈ μ.support, e' = Expr.uniform (.const v1) g := by
  simpa using
    (MeasureTheory.Measure.mem_support_bind_dirac_iff
      (μ := μ)
      (f := fun g : Expr => Expr.uniform (.const v1) g)
      (hf_meas := uniform_right_wrap_measurable v1)
      (hf_emb := uniform_right_wrap_closedEmbedding v1)
      (y := e'))

@[simp] lemma mem_support_bind_const_iff
    (μ : Measure ℝ) (e' : Expr) :
    e' ∈ (Measure.bind μ (fun r => Measure.dirac (Expr.const r))).support
      ↔ ∃ r ∈ μ.support, e' = Expr.const r := by
  simpa using
    (MeasureTheory.Measure.mem_support_bind_dirac_iff
      (μ := μ)
      (f := fun r : ℝ => Expr.const r)
      (hf_meas := const_wrap_measurable)
      (hf_emb := const_isClosedEmbedding)
      (y := e'))

@[simp] lemma mem_support_bind_finconst_iff
    {n : Nat} (μ : Measure (Fin n)) (e' : Expr) :
    e' ∈ (Measure.bind μ (fun i : Fin n => Measure.dirac (Expr.finconst n i))).support
      ↔ ∃ i ∈ μ.support, e' = Expr.finconst n i := by
  simpa using
    (MeasureTheory.Measure.mem_support_bind_dirac_iff
      (μ := μ)
      (f := fun i : Fin n => Expr.finconst n i)
      (hf_meas := finconst_wrap_measurable n)
      (hf_emb := finconst_isClosedEmbedding n)
      (y := e'))

end Slice
