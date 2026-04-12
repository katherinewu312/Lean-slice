import Syntax
import TypeSystem

namespace Slice

open MeasureTheory ProbabilityTheory

namespace Untyped

--- Expression skeletons
--- A skeleton is syntactically identical to Expr except that every const r is replaced by a hole. Formally, this is the paper's set Skel.
inductive Skeleton : Type where
  | hole : Skeleton
  | var : String → Skeleton
  | trueE : Skeleton
  | falseE : Skeleton
  | finconst : (n : ℕ) → Fin n → Skeleton
  | discrete : DiscreteProbs → Skeleton
  | lt : Skeleton → Skeleton → Skeleton
  | ifE : Skeleton → Skeleton → Skeleton → Skeleton
  | letE : String → Skeleton → Skeleton → Skeleton
  | uniform : Skeleton → Skeleton → Skeleton
  -- etc.

--- Number of holes in a skeleton
def numHoles : Skeleton → ℕ
  | .hole => 1
  | .var _ => 0
  | .trueE => 0
  | .falseE => 0
  | .finconst _ _ => 0
  | .discrete _ => 0
  | .lt s1 s2 => numHoles s1 + numHoles s2
  | .ifE s1 s2 s3 => numHoles s1 + (numHoles s2 + numHoles s3)
  | .letE _ s1 s2 => numHoles s1 + numHoles s2
  | .uniform s1 s2 => numHoles s1 + numHoles s2

-- Fills skeleton s with hole assignment v, reading holes left-to-right, producing an expression
def fillSkeleton : (s : Skeleton) → (Fin (numHoles s) → ℝ) → Expr
  | .hole, v =>
      .const (v ⟨0, by simp [numHoles]⟩)
  | .var x, _ =>
      .var x
  | .trueE, _ =>
      .trueE
  | .falseE, _ =>
      .falseE
  | .finconst n k, _ =>
      .finconst n k
  | .discrete ps, _ =>
      .discrete ps
  | .lt s1 s2, v =>
      let v1 : Fin (numHoles s1) → ℝ := fun i => v (Fin.castAdd (numHoles s2) i)
      let v2 : Fin (numHoles s2) → ℝ := fun i => v (Fin.natAdd (numHoles s1) i)
      .lt (fillSkeleton s1 v1) (fillSkeleton s2 v2)
  | .ifE s1 s2 s3, v =>
      let v1 : Fin (numHoles s1) → ℝ := fun i => v (Fin.castAdd (numHoles s2 + numHoles s3) i)
      let v23 : Fin (numHoles s2 + numHoles s3) → ℝ := fun i => v (Fin.natAdd (numHoles s1) i)
      let v2 : Fin (numHoles s2) → ℝ := fun i => v23 (Fin.castAdd (numHoles s3) i)
      let v3 : Fin (numHoles s3) → ℝ := fun i => v23 (Fin.natAdd (numHoles s2) i)
      .ifE (fillSkeleton s1 v1) (fillSkeleton s2 v2) (fillSkeleton s3 v3)
  | .letE x s1 s2, v =>
      let v1 : Fin (numHoles s1) → ℝ := fun i => v (Fin.castAdd (numHoles s2) i)
      let v2 : Fin (numHoles s2) → ℝ := fun i => v (Fin.natAdd (numHoles s1) i)
      .letE x (fillSkeleton s1 v1) (fillSkeleton s2 v2)
  | .uniform s1 s2, v =>
      let v1 : Fin (numHoles s1) → ℝ := fun i => v (Fin.castAdd (numHoles s2) i)
      let v2 : Fin (numHoles s2) → ℝ := fun i => v (Fin.natAdd (numHoles s1) i)
      .uniform (fillSkeleton s1 v1) (fillSkeleton s2 v2)

--- Decomposing an expression ---

-- Extract the skeleton of an expression.
def skeletonOf : Expr → Skeleton
  | .var x           => .var x
  | .const _         => .hole
  | .trueE           => .trueE
  | .falseE          => .falseE
  | .finconst n k    => .finconst n k
  | .discrete ps     => .discrete ps
  | .lt   e₁ e₂     => .lt   (skeletonOf e₁) (skeletonOf e₂)
  | .ifE  e₁ e₂ e₃  => .ifE  (skeletonOf e₁) (skeletonOf e₂) (skeletonOf e₃)
  | .letE x e₁ e₂  => .letE x (skeletonOf e₁) (skeletonOf e₂)
  | .uniform e₁ e₂  => .uniform (skeletonOf e₁) (skeletonOf e₂)

-- The vector of real constants appearing in an expression, from left-to-right.
def holeValues : (e : Expr) → Fin (numHoles (skeletonOf e)) → ℝ
  | .var _ =>
      Fin.elim0
  | .const r =>
      fun _ => r
  | .trueE =>
      Fin.elim0
  | .falseE =>
      Fin.elim0
  | .finconst _ _ =>
      Fin.elim0
  | .discrete _ =>
      Fin.elim0
  | .lt e₁ e₂ =>
      by
        simpa [skeletonOf, numHoles] using
          (Fin.addCases (holeValues e₁) (holeValues e₂))
  | .ifE e₁ e₂ e₃ =>
      by
        simpa [skeletonOf, numHoles, Nat.add_assoc] using
          (Fin.addCases (holeValues e₁) (Fin.addCases (holeValues e₂) (holeValues e₃)))
  | .letE _ e₁ e₂ =>
      by
        simpa [skeletonOf, numHoles] using
          (Fin.addCases (holeValues e₁) (holeValues e₂))
  | .uniform e₁ e₂ =>
      by
        simpa [skeletonOf, numHoles] using
          (Fin.addCases (holeValues e₁) (holeValues e₂))


-- The set of expressions whose skeleton is exactly s.
def ExprsOfSkel (s : Skeleton) : Type :=
  {e : Expr // skeletonOf e = s}


--- Show that every expression is uniquely determined by its hole-value vector

-- Extracting then filling the expression recovers the original expression.
--- Start from an Expr, decompose to (skeletonOf, holeValues), then rebuild. You recover the same Expr.
theorem fillSkeleton_holeValues (e : Expr) :
  fillSkeleton (skeletonOf e) (holeValues e) = e := by
  induction e with
  | var x =>
      simp [fillSkeleton, skeletonOf, holeValues]
  | const r =>
      simp [fillSkeleton, skeletonOf, holeValues]
  | trueE =>
      simp [fillSkeleton, skeletonOf, holeValues]
  | falseE =>
      simp [fillSkeleton, skeletonOf, holeValues]
  | finconst n k =>
      simp [fillSkeleton, skeletonOf, holeValues]
  | discrete ps =>
      simp [fillSkeleton, skeletonOf, holeValues]
  | lt e₁ e₂ ih₁ ih₂ =>
      simp [fillSkeleton, skeletonOf, holeValues, ih₁, ih₂]
  | ifE e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
      simp [fillSkeleton, skeletonOf, holeValues, ih₁, ih₂, ih₃]
  | letE x e₁ e₂ ih₁ ih₂ =>
      simp [fillSkeleton, skeletonOf, holeValues, ih₁, ih₂]
  | uniform e₁ e₂ ih₁ ih₂ =>
      simp [fillSkeleton, skeletonOf, holeValues, ih₁, ih₂]

-- Filling then extracting the skeleton recovers the original skeleton.
theorem skeletonOf_fillSkeleton (σ : Skeleton) (v : Fin (numHoles σ) → ℝ) :
  skeletonOf (fillSkeleton σ v) = σ := by
  induction σ with
  | hole =>
      simp [fillSkeleton, skeletonOf]
  | var x =>
      simp [fillSkeleton, skeletonOf]
  | trueE =>
      simp [fillSkeleton, skeletonOf]
  | falseE =>
      simp [fillSkeleton, skeletonOf]
  | finconst n k =>
      simp [fillSkeleton, skeletonOf]
  | discrete ps =>
      simp [fillSkeleton, skeletonOf]
  | lt s₁ s₂ ih₁ ih₂ =>
      simp [fillSkeleton, skeletonOf, ih₁, ih₂]
  | ifE s₁ s₂ s₃ ih₁ ih₂ ih₃ =>
      simp [fillSkeleton, skeletonOf, ih₁, ih₂, ih₃]
  | letE x s₁ s₂ ih₁ ih₂ =>
      simp [fillSkeleton, skeletonOf, ih₁, ih₂]
  | uniform s₁ s₂ ih₁ ih₂ =>
      simp [fillSkeleton, skeletonOf, ih₁, ih₂]

lemma fillSkeleton_eq_rec {s t : Skeleton} (h : s = t) (v : Fin (numHoles s) → ℝ) :
    fillSkeleton t (h ▸ v) = fillSkeleton s v := by
  cases h
  rfl

-- For a fixed s, the map fillSkeleton is injective: so if two hole assignments produce the same filled expression, those assignments were equal.
theorem fillSkeleton_injective (σ : Skeleton) :
  Function.Injective (fillSkeleton σ) := by
  intro v w h
  induction σ with
  | hole =>
      have h0 : v ⟨0, by simp [numHoles]⟩ = w ⟨0, by simp [numHoles]⟩ := by
        simpa [fillSkeleton, numHoles] using
          congrArg (fun e => match e with | .const r => r | _ => 0) h
      funext i
      fin_cases i
      simpa using h0
  | var x =>
      funext i
      exact Fin.elim0 i
  | trueE =>
      funext i
      exact Fin.elim0 i
  | falseE =>
      funext i
      exact Fin.elim0 i
  | finconst n k =>
      funext i
      exact Fin.elim0 i
  | discrete ps =>
      funext i
      exact Fin.elim0 i
  | lt s₁ s₂ ih₁ ih₂ =>
      let v1 : Fin (numHoles s₁) → ℝ := fun i => v (Fin.castAdd (numHoles s₂) i)
      let v2 : Fin (numHoles s₂) → ℝ := fun i => v (Fin.natAdd (numHoles s₁) i)
      let w1 : Fin (numHoles s₁) → ℝ := fun i => w (Fin.castAdd (numHoles s₂) i)
      let w2 : Fin (numHoles s₂) → ℝ := fun i => w (Fin.natAdd (numHoles s₁) i)
      have h' : Expr.lt (fillSkeleton s₁ v1) (fillSkeleton s₂ v2) =
          Expr.lt (fillSkeleton s₁ w1) (fillSkeleton s₂ w2) := by
        simpa [fillSkeleton, v1, v2, w1, w2] using h
      have h1 : fillSkeleton s₁ v1 = fillSkeleton s₁ w1 := by
        injection h' with h1 h2
      have h2 : fillSkeleton s₂ v2 = fillSkeleton s₂ w2 := by
        injection h' with h1 h2
      have hv1 : v1 = w1 := ih₁ h1
      have hv2 : v2 = w2 := ih₂ h2
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa [v1, w1] using congrFun hv1 j
      · intro j
        simpa [v2, w2] using congrFun hv2 j
  | ifE s₁ s₂ s₃ ih₁ ih₂ ih₃ =>
      let v1 : Fin (numHoles s₁) → ℝ := fun i => v (Fin.castAdd (numHoles s₂ + numHoles s₃) i)
      let v23 : Fin (numHoles s₂ + numHoles s₃) → ℝ := fun i => v (Fin.natAdd (numHoles s₁) i)
      let v2 : Fin (numHoles s₂) → ℝ := fun i => v23 (Fin.castAdd (numHoles s₃) i)
      let v3 : Fin (numHoles s₃) → ℝ := fun i => v23 (Fin.natAdd (numHoles s₂) i)
      let w1 : Fin (numHoles s₁) → ℝ := fun i => w (Fin.castAdd (numHoles s₂ + numHoles s₃) i)
      let w23 : Fin (numHoles s₂ + numHoles s₃) → ℝ := fun i => w (Fin.natAdd (numHoles s₁) i)
      let w2 : Fin (numHoles s₂) → ℝ := fun i => w23 (Fin.castAdd (numHoles s₃) i)
      let w3 : Fin (numHoles s₃) → ℝ := fun i => w23 (Fin.natAdd (numHoles s₂) i)
      have h' : Expr.ifE (fillSkeleton s₁ v1) (fillSkeleton s₂ v2) (fillSkeleton s₃ v3) =
          Expr.ifE (fillSkeleton s₁ w1) (fillSkeleton s₂ w2) (fillSkeleton s₃ w3) := by
        simpa [fillSkeleton, v1, v23, v2, v3, w1, w23, w2, w3] using h
      have h1 : fillSkeleton s₁ v1 = fillSkeleton s₁ w1 := by
        injection h' with h1 h2 h3
      have h2 : fillSkeleton s₂ v2 = fillSkeleton s₂ w2 := by
        injection h' with h1 h2 h3
      have h3 : fillSkeleton s₃ v3 = fillSkeleton s₃ w3 := by
        injection h' with h1 h2 h3
      have hv1 : v1 = w1 := ih₁ h1
      have hv2 : v2 = w2 := ih₂ h2
      have hv3 : v3 = w3 := ih₃ h3
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa [v1, w1] using congrFun hv1 j
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro k
          simpa [v23, v2, w23, w2] using congrFun hv2 k
        · intro k
          simpa [v23, v3, w23, w3] using congrFun hv3 k
  | letE x s₁ s₂ ih₁ ih₂ =>
      let v1 : Fin (numHoles s₁) → ℝ := fun i => v (Fin.castAdd (numHoles s₂) i)
      let v2 : Fin (numHoles s₂) → ℝ := fun i => v (Fin.natAdd (numHoles s₁) i)
      let w1 : Fin (numHoles s₁) → ℝ := fun i => w (Fin.castAdd (numHoles s₂) i)
      let w2 : Fin (numHoles s₂) → ℝ := fun i => w (Fin.natAdd (numHoles s₁) i)
      have h' : Expr.letE x (fillSkeleton s₁ v1) (fillSkeleton s₂ v2) =
          Expr.letE x (fillSkeleton s₁ w1) (fillSkeleton s₂ w2) := by
        simpa [fillSkeleton, v1, v2, w1, w2] using h
      have h1 : fillSkeleton s₁ v1 = fillSkeleton s₁ w1 := by
        injection h' with h1 h2
      have h2 : fillSkeleton s₂ v2 = fillSkeleton s₂ w2 := by
        injection h' with h1 h2
      have hv1 : v1 = w1 := ih₁ h1
      have hv2 : v2 = w2 := ih₂ h2
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa [v1, w1] using congrFun hv1 j
      · intro j
        simpa [v2, w2] using congrFun hv2 j
  | uniform s₁ s₂ ih₁ ih₂ =>
      let v1 : Fin (numHoles s₁) → ℝ := fun i => v (Fin.castAdd (numHoles s₂) i)
      let v2 : Fin (numHoles s₂) → ℝ := fun i => v (Fin.natAdd (numHoles s₁) i)
      let w1 : Fin (numHoles s₁) → ℝ := fun i => w (Fin.castAdd (numHoles s₂) i)
      let w2 : Fin (numHoles s₂) → ℝ := fun i => w (Fin.natAdd (numHoles s₁) i)
      have h' : Expr.uniform (fillSkeleton s₁ v1) (fillSkeleton s₂ v2) =
          Expr.uniform (fillSkeleton s₁ w1) (fillSkeleton s₂ w2) := by
        simpa [fillSkeleton, v1, v2, w1, w2] using h
      have h1 : fillSkeleton s₁ v1 = fillSkeleton s₁ w1 := by
        injection h' with h1 h2
      have h2 : fillSkeleton s₂ v2 = fillSkeleton s₂ w2 := by
        injection h' with h1 h2
      have hv1 : v1 = w1 := ih₁ h1
      have hv2 : v2 = w2 := ih₂ h2
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa [v1, w1] using congrFun hv1 j
      · intro j
        simpa [v2, w2] using congrFun hv2 j

-- If you fill a skeleton and then extract hole values, you get back the original hole assignment.
theorem holeValues_fillSkeleton (σ : Skeleton) (v : Fin (numHoles σ) → ℝ) :
  (skeletonOf_fillSkeleton σ v) ▸ holeValues (fillSkeleton σ v) = v := by
  have hs : skeletonOf (fillSkeleton σ v) = σ := skeletonOf_fillSkeleton σ v
  have hfill :
      fillSkeleton σ (hs ▸ holeValues (fillSkeleton σ v)) =
        fillSkeleton σ v := by
    calc
      fillSkeleton σ (hs ▸ holeValues (fillSkeleton σ v)) =
          fillSkeleton (skeletonOf (fillSkeleton σ v)) (holeValues (fillSkeleton σ v)) := by
            simpa using fillSkeleton_eq_rec hs (holeValues (fillSkeleton σ v))
      _ = fillSkeleton σ v := fillSkeleton_holeValues (fillSkeleton σ v)
  simpa [hs] using fillSkeleton_injective σ hfill


-- Bijection: ExprsOfSkel s <-> (Fin (numHoles s) → ℝ)
noncomputable def exprsOfSkel_equiv (σ : Skeleton) :
    ExprsOfSkel σ ≃ (Fin (numHoles σ) → ℝ) where
  toFun  := fun ⟨e, he⟩ => he ▸ holeValues e
  invFun := fun v => ⟨fillSkeleton σ v, skeletonOf_fillSkeleton σ v⟩
  left_inv := by
    intro x
    rcases x with ⟨e, rfl⟩
    apply Subtype.ext
    simpa using fillSkeleton_holeValues e
  right_inv := by
    intro v
    simpa using holeValues_fillSkeleton σ v

-- Transport the Borel sigma-algebra on Fin (numHoles s) → ℝ along the bijection exprsOfSkel_equiv s, to obtain exprsOfSkel measurable
noncomputable instance exprsOfSkel_measurableSpace (σ : Skeleton) :
    MeasurableSpace (ExprsOfSkel σ) :=
  MeasurableSpace.comap (exprsOfSkel_equiv σ) inferInstance

-- Take disjoint union of exprsOfSkel to obtain Expr measurable.
instance expr_measurableSpace : MeasurableSpace Expr where
  MeasurableSet' S :=
    ∀ σ : Skeleton, MeasurableSet (α := ExprsOfSkel σ)
      { p : ExprsOfSkel σ | p.1 ∈ S }
  measurableSet_empty := by
    intro σ
    simp
  measurableSet_compl := by
    intro S hS σ
    have hSσ := hS σ
    -- {p | p.1 ∈ Sᶜ} = ({p | p.1 ∈ S})ᶜ  in ExprsOfSkel σ
    convert MeasurableSet.compl hSσ using 1
  measurableSet_iUnion := by
    intro f hf σ
    have : { p : ExprsOfSkel σ | p.1 ∈ ⋃ i, f i } =
           ⋃ i, { p : ExprsOfSkel σ | p.1 ∈ f i } := by
      ext ⟨e, he⟩; simp [Set.mem_iUnion]
    rw [this]
    exact MeasurableSet.iUnion (fun i => hf i σ)

end Untyped

-- ---------------------------------------------------------------------------
-- Well-typed skeletons.
-- ---------------------------------------------------------------------------

/-- Typing judgement for skeletons. Identical to `HasType` on expressions, except holes stand for real constants. -/
inductive HasTypeSkel : Ctx → Untyped.Skeleton → Ty → Prop where
  | hole {Γ : Ctx} :
      HasTypeSkel Γ .hole .real

  | var {Γ : Ctx} {x : String} {τ : Ty} :
      Γ x = some τ →
      HasTypeSkel Γ (.var x) τ

  | trueE {Γ : Ctx} :
      HasTypeSkel Γ .trueE .bool

  | falseE {Γ : Ctx} :
      HasTypeSkel Γ .falseE .bool

  | finconst {Γ : Ctx} {n : Nat} (k : Fin n) :
      HasTypeSkel Γ (.finconst n k) (.fin n)

  | discrete {Γ : Ctx} {ps : DiscreteProbs} :
      HasTypeSkel Γ (.discrete ps) (.fin ps.1.length)

  | letE {Γ : Ctx} {x : String} {s1 s2 : Untyped.Skeleton} {τ1 τ2 : Ty} :
      HasTypeSkel Γ s1 τ1 →
      HasTypeSkel (Ctx.extend Γ x τ1) s2 τ2 →
      HasTypeSkel Γ (.letE x s1 s2) τ2

  | lt {Γ : Ctx} {s1 s2 : Untyped.Skeleton} :
      HasTypeSkel Γ s1 .real →
      HasTypeSkel Γ s2 .real →
      HasTypeSkel Γ (.lt s1 s2) .bool

  | ifE {Γ : Ctx} {c t f : Untyped.Skeleton} {τ : Ty} :
      HasTypeSkel Γ c .bool →
      HasTypeSkel Γ t τ →
      HasTypeSkel Γ f τ →
      HasTypeSkel Γ (.ifE c t f) τ

  | uniform {Γ : Ctx} {s1 s2 : Untyped.Skeleton} :
      HasTypeSkel Γ s1 .real →
      HasTypeSkel Γ s2 .real →
      HasTypeSkel Γ (.uniform s1 s2) .real

/-- Well-typed skeletons of type `τ` in the empty context. -/
def SkeletonsOfType (τ : Ty) : Type :=
  {s : Untyped.Skeleton // HasTypeSkel Ctx.empty s τ}

-- Number of holes in a well-typed skeleton is the same as in an untyped skeleton.
def numHoles {τ : Ty} (s : SkeletonsOfType τ) : ℕ :=
  Untyped.numHoles s.1

lemma fillSkeleton_preserves_type {Γ : Ctx} {s : Untyped.Skeleton} {τ : Ty}
    (hs : HasTypeSkel Γ s τ) :
    ∀ v : Fin (Untyped.numHoles s) → ℝ, HasType Γ (Untyped.fillSkeleton s v) τ := by
  induction hs with
  | hole =>
      intro v
      simpa [Untyped.fillSkeleton, Untyped.numHoles] using
        (HasType.const (r := v ⟨0, by simp [Untyped.numHoles]⟩))
  | var hx =>
      intro v
      simpa [Untyped.fillSkeleton] using (HasType.var hx)
  | trueE =>
      intro v
      simpa [Untyped.fillSkeleton] using (HasType.trueE)
  | falseE =>
      intro v
      simpa [Untyped.fillSkeleton] using (HasType.falseE)
  | finconst k =>
      intro v
      simpa [Untyped.fillSkeleton] using (HasType.finconst k)
  | discrete =>
      intro v
      simpa [Untyped.fillSkeleton] using (HasType.discrete)
  | letE hs1 hs2 ih1 ih2 =>
      intro v
      simpa [Untyped.fillSkeleton] using
        (HasType.letE
          (ih1 (fun i => v (Fin.castAdd _ i)))
          (ih2 (fun i => v (Fin.natAdd _ i))))
  | lt hs1 hs2 ih1 ih2 =>
      intro v
      simpa [Untyped.fillSkeleton] using
        (HasType.lt
          (ih1 (fun i => v (Fin.castAdd _ i)))
          (ih2 (fun i => v (Fin.natAdd _ i))))
  | ifE hc ht hf ihc iht ihf =>
      intro v
      simpa [Untyped.fillSkeleton] using
        (HasType.ifE
          (ihc (fun i => v (Fin.castAdd _ i)))
          (iht (fun i => v (Fin.natAdd _ (Fin.castAdd _ i))))
          (ihf (fun i => v (Fin.natAdd _ (Fin.natAdd _ i)))))
  | uniform hs1 hs2 ih1 ih2 =>
      intro v
      simpa [Untyped.fillSkeleton] using
        (HasType.uniform
          (ih1 (fun i => v (Fin.castAdd _ i)))
          (ih2 (fun i => v (Fin.natAdd _ i))))

-- Fills a well-typed skeleton s with hole assignment v, reading holes left-to-right, producing a well-typed expression
def fillSkeleton {τ : Ty} (s : SkeletonsOfType τ) :
    (Fin (numHoles s) → ℝ) → ExprsOfType τ
  | v => ⟨Untyped.fillSkeleton s.1 v, fillSkeleton_preserves_type s.2 v⟩

-- Replacing every real constant in a well-typed expression by a hole produces a well-typed skeleton (of the same type).
lemma hasTypeSkel_of_hasType {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Γ e τ) :
    HasTypeSkel Γ (Untyped.skeletonOf e) τ := by
  induction h with
  | var hx =>
      exact HasTypeSkel.var hx
  | const =>
      exact HasTypeSkel.hole
  | trueE =>
      exact HasTypeSkel.trueE
  | falseE =>
      exact HasTypeSkel.falseE
  | finconst k =>
      exact HasTypeSkel.finconst k
  | discrete =>
      exact HasTypeSkel.discrete
  | letE h1 h2 ih1 ih2 =>
      simpa [Untyped.skeletonOf] using HasTypeSkel.letE ih1 ih2
  | lt h1 h2 ih1 ih2 =>
      simpa [Untyped.skeletonOf] using HasTypeSkel.lt ih1 ih2
  | ifE hc ht hf ihc iht ihf =>
      simpa [Untyped.skeletonOf] using HasTypeSkel.ifE ihc iht ihf
  | uniform h1 h2 ih1 ih2 =>
      simpa [Untyped.skeletonOf] using HasTypeSkel.uniform ih1 ih2


-- Extract the well-typed skeleton of a well-typed expression.
def skeletonOf {τ : Ty} (e : ExprsOfType τ) : SkeletonsOfType τ :=
  ⟨Untyped.skeletonOf e.1, hasTypeSkel_of_hasType e.2⟩

-- The vector of real constants appearing in a well-typed expression, from left-to-right. This is the second component of dec₂.
def holeValues {τ : Ty} (e : ExprsOfType τ) : Fin (numHoles (skeletonOf e)) → ℝ := by
  simpa [numHoles, skeletonOf] using (Untyped.holeValues e.1)

-- The set of well-typed expressions whose skeleton is exactly s:τ.
def ExprsOfSkel {τ : Ty} (s : SkeletonsOfType τ) : Type :=
  {e : ExprsOfType τ // skeletonOf e = s}

theorem fillSkeleton_holeValues {τ : Ty} (e : ExprsOfType τ) :
  fillSkeleton (skeletonOf e) (holeValues e) = e := by
  apply Subtype.ext
  simpa [fillSkeleton, skeletonOf, holeValues, numHoles] using
    Untyped.fillSkeleton_holeValues e.1

theorem skeletonOf_fillSkeleton {τ : Ty} (σ : SkeletonsOfType τ) (v : Fin (numHoles σ) → ℝ) :
  skeletonOf (fillSkeleton σ v) = σ := by
  apply Subtype.ext
  simpa [fillSkeleton, skeletonOf, numHoles] using
    Untyped.skeletonOf_fillSkeleton σ.1 v

lemma fillSkeleton_eq_rec {τ : Ty} {s t : SkeletonsOfType τ}
    (h : s = t) (v : Fin (numHoles s) → ℝ) :
    fillSkeleton t (h ▸ v) = fillSkeleton s v := by
  cases h
  rfl

theorem fillSkeleton_injective {τ : Ty} (σ : SkeletonsOfType τ) :
  Function.Injective (fillSkeleton σ) := by
  intro v w h
  apply Untyped.fillSkeleton_injective σ.1
  exact congrArg Subtype.val h

theorem holeValues_fillSkeleton {τ : Ty} (σ : SkeletonsOfType τ) (v : Fin (numHoles σ) → ℝ) :
  (skeletonOf_fillSkeleton σ v) ▸ holeValues (fillSkeleton σ v) = v := by
  have hs : skeletonOf (fillSkeleton σ v) = σ := skeletonOf_fillSkeleton σ v
  have hfill :
      fillSkeleton σ (hs ▸ holeValues (fillSkeleton σ v)) =
        fillSkeleton σ v := by
    calc
      fillSkeleton σ (hs ▸ holeValues (fillSkeleton σ v)) =
          fillSkeleton (skeletonOf (fillSkeleton σ v)) (holeValues (fillSkeleton σ v)) := by
            simpa using fillSkeleton_eq_rec hs (holeValues (fillSkeleton σ v))
      _ = fillSkeleton σ v := fillSkeleton_holeValues (fillSkeleton σ v)
  simpa [hs] using fillSkeleton_injective σ hfill

-- Bijection: ExprsOfSkel s:τ <-> (Fin (numHoles s:τ) → ℝ)
noncomputable def exprsOfSkel_equiv {τ : Ty} (σ : SkeletonsOfType τ) :
    ExprsOfSkel σ ≃ (Fin (numHoles σ) → ℝ) where
  toFun  := fun ⟨e, he⟩ => he ▸ holeValues e
  invFun := fun v => ⟨fillSkeleton σ v, skeletonOf_fillSkeleton σ v⟩
  left_inv := by
    intro x
    rcases x with ⟨e, rfl⟩
    apply Subtype.ext
    simpa using fillSkeleton_holeValues e
  right_inv := by
    intro v
    simpa using holeValues_fillSkeleton σ v

noncomputable instance exprsOfSkel_measurableSpace {τ : Ty} (σ : SkeletonsOfType τ) :
    MeasurableSpace (ExprsOfSkel σ) :=
  MeasurableSpace.comap (exprsOfSkel_equiv σ) inferInstance

/-- Well-typed expressions of type τ is measurable. -/
noncomputable instance exprsOfType_measurableSpace (τ : Ty) :
    MeasurableSpace (ExprsOfType τ) :=
  MeasurableSpace.comap (fun ⟨e, _⟩ => e) Untyped.expr_measurableSpace

end Slice
