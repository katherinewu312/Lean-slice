import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace Slice

open MeasureTheory ProbabilityTheory


/-- Weights for finite mixtures. -/
abbrev Prob := ENNReal

/-- Distributions are Mathlib measures. -/
abbrev Dist (α : Type) [MeasurableSpace α] := Measure α

namespace Dist

noncomputable def ret {α : Type} [MeasurableSpace α] (a : α) : Dist α :=
  Measure.dirac a

noncomputable def bind {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Dist α) (k : α → Dist β) : Dist β :=
  Measure.bind μ k

/-- Finite convex combination of measures. -/
noncomputable def mix {α : Type} [MeasurableSpace α]
    (branches : List (Prob × Dist α)) : Dist α :=
  branches.foldl (fun acc br => acc + br.1 • br.2) 0

@[simp] theorem ret_is_dirac {α : Type} [MeasurableSpace α] (a : α) :
    Dist.ret a = Measure.dirac a := rfl

@[simp] theorem bind_is_measure_bind
    {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Dist α) (k : α → Dist β) :
    Dist.bind μ k = Measure.bind μ k := rfl

end Dist

infixl:55 " >>= " => Dist.bind
-- ---------------------------------------------------------------------------
-- Continuous distributions / sampling
-- ---------------------------------------------------------------------------

/-
/-- Continuous distributions -/
inductive SampleOp where
  | uniform   -- Uniform(lo, hi)
deriving DecidableEq, Repr

/-- Sampling -/
noncomputable def sampleSem (d : SampleOp) (x y : ℝ) : Dist ℝ :=
  match d with
  | .uniform =>
      let lo := min x y
      let hi := max x y
      if lo < hi then
        ProbabilityTheory.cond volume (Set.Icc lo hi)
      else
        Dist.ret lo
-/

-- ---------------------------------------------------------------------------
-- Comparison operators
-- ---------------------------------------------------------------------------

/-
inductive CmpOp where
  | lt
  | le
deriving DecidableEq, Repr

noncomputable def evalCmp : CmpOp → ℝ → ℝ → Bool
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b

def evalFinCmp : CmpOp → Nat → Nat → Bool
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
-/

-- ---------------------------------------------------------------------------
-- Expression AST
-- ---------------------------------------------------------------------------

/-
/-- Probability lists accepted by `discrete`: total mass must be exactly 1. -/
def ValidProbs (probs : List Prob) : Prop :=
  probs.sum = 1
-/

/--
Slice expressions.
-/
inductive Expr where
  | var       : String → Expr
  | const     : ℝ → Expr
  | letE      : String → Expr → Expr → Expr
  | lt        : Expr → Expr → Expr
  | ifE       : Expr → Expr → Expr → Expr
  /-
  | bool      : Bool → Expr
  | sample    : SampleOp → Expr → Expr → Expr
  | discrete  : (probs : List Prob) → ValidProbs probs → Expr
  | cmp       : CmpOp → Expr → Expr → Expr
  | andE      : Expr → Expr → Expr
  | orE       : Expr → Expr → Expr
  | notE      : Expr → Expr
  | pair      : Expr → Expr → Expr
  | fstE      : Expr → Expr
  | sndE      : Expr → Expr
  | funE      : String → Expr → Expr
  | app       : Expr → Expr → Expr
  | finConst  : Nat → Nat → Expr
  | finCmp    : CmpOp → Expr → Expr → Nat → Expr
  | finEq     : Expr → Expr → Nat → Expr
  | observe   : Expr → Expr
  | fixE      : String → String → Expr → Expr
  | nil       : Expr
  | cons      : Expr → Expr → Expr
  | matchList : Expr → Expr → String → String → Expr → Expr
  | unit      : Expr
  | seq       : Expr → Expr → Expr
  | runtimeError : String → Expr
  -/

-- Discrete measurable space for the kernel construction.
-- Need to give explicit sigma algebra
-- instance : MeasurableSpace Expr          := ⊤
-- instance : MeasurableSpace (Option Expr) := ⊤

-- ---------------------------------------------------------------------------
-- Syntactic values and substitution
-- ---------------------------------------------------------------------------

/-- Syntactic values: closed, fully-reduced expressions. -/
def isValue : Expr → Bool
  | .const _      => true
  /-
  | .bool _       => true
  | .finConst _ _ => true
  | .funE _ _     => true
  | .fixE _ _ _   => true
  | .unit         => true
  | .nil          => true
  | .pair e1 e2   => isValue e1 && isValue e2
  | .cons h t     => isValue h  && isValue t
  -/
  | _             => false

/-- Capture-avoiding substitution (alpha-renaming assumed). -/
partial def subst (x : String) (v : Expr) : Expr → Expr
  | .var y          => if x = y then v else .var y
  | .const r        => .const r
  | .letE y e1 e2   =>
      if x = y then .letE y (subst x v e1) e2
      else .letE y (subst x v e1) (subst x v e2)
  | .lt e1 e2           => .lt (subst x v e1) (subst x v e2)
  | .ifE c t f          => .ifE  (subst x v c) (subst x v t) (subst x v f)
  /-
  | .bool b         => .bool b
  | .sample d e1 e2     => .sample d (subst x v e1) (subst x v e2)
  | .discrete ps hps    => .discrete ps hps
  | .cmp op e1 e2       => .cmp op (subst x v e1) (subst x v e2)
  | .andE e1 e2         => .andE (subst x v e1) (subst x v e2)
  | .orE  e1 e2         => .orE  (subst x v e1) (subst x v e2)
  | .notE e             => .notE (subst x v e)
  | .pair e1 e2         => .pair (subst x v e1) (subst x v e2)
  | .fstE e             => .fstE (subst x v e)
  | .sndE e             => .sndE (subst x v e)
  | .funE y body        =>
      if x = y then .funE y body else .funE y (subst x v body)
  | .app e1 e2          => .app (subst x v e1) (subst x v e2)
  | .finConst k n       => .finConst k n
  | .finCmp op e1 e2 n  => .finCmp op (subst x v e1) (subst x v e2) n
  | .finEq e1 e2 n      => .finEq (subst x v e1) (subst x v e2) n
  | .observe e          => .observe (subst x v e)
  | .fixE f y body      =>
      if x = f ∨ x = y then .fixE f y body else .fixE f y (subst x v body)
  | .nil                => .nil
  | .cons h t           => .cons (subst x v h) (subst x v t)
  | .matchList e nb y ys cb =>
      let e'  := subst x v e
      let nb' := subst x v nb
      if x = y ∨ x = ys then .matchList e' nb' y ys cb
      else .matchList e' nb' y ys (subst x v cb)
  | .unit               => .unit
  | .seq e1 e2          => .seq (subst x v e1) (subst x v e2)
  | .runtimeError s     => .runtimeError s
  -/



--- Expression skeletons
--- A skeleton is syntactically identicak to Expr except that every const r is replaced by a hole. Formally, this is the paper's set Skel.
inductive Skeleton : Type where
  | hole : Skeleton
  | var : String → Skeleton
  | lt : Skeleton → Skeleton → Skeleton
  | ifE : Skeleton → Skeleton → Skeleton → Skeleton
  | letE : String → Skeleton → Skeleton → Skeleton
  -- etc.
deriving Repr, DecidableEq

--- Number of holes in a skeleton
def numHoles : Skeleton → ℕ
  | .hole => 1
  | .var _ => 0
  | .lt s1 s2 => numHoles s1 + numHoles s2
  | .ifE s1 s2 s3 => numHoles s1 + (numHoles s2 + numHoles s3)
  | .letE _ s1 s2 => numHoles s1 + numHoles s2

-- Fills skeleton s with hole assignment v, reading holes left-to-right, producing an expression
def fillSkeleton : (s : Skeleton) → (Fin (numHoles s) → ℝ) → Expr
  | .hole, v =>
      .const (v ⟨0, by simp [numHoles]⟩)
  | .var x, _ =>
      .var x
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


--- Decomposing an expression ---

-- Extract the skeleton of an expression.
def skeletonOf : Expr → Skeleton
  | .var x           => .var x
  | .const _         => .hole
  | .lt   e₁ e₂     => .lt   (skeletonOf e₁) (skeletonOf e₂)
  | .ifE  e₁ e₂ e₃  => .ifE  (skeletonOf e₁) (skeletonOf e₂) (skeletonOf e₃)
  | .letE x e₁ e₂  => .letE x (skeletonOf e₁) (skeletonOf e₂)

-- Extract real constants from e in left-to-right order, accumulating into a list.
def holeValuesList : Expr → List ℝ
  | .var _ => []
  | .const r => [r]
  | .lt e1 e2 => holeValuesList e1 ++ holeValuesList e2
  | .ifE e1 e2 e3 => holeValuesList e1 ++ holeValuesList e2 ++ holeValuesList e3
  | .letE _ e1 e2 => holeValuesList e1 ++ holeValuesList e2

-- Length of holeValuesList equals numHoles of the skeleton.
@[simp]
theorem holeValuesList_length (e : Expr) :
  (holeValuesList e).length = numHoles (skeletonOf e) := by
  induction e with
  | var _ => simp [holeValuesList, skeletonOf, numHoles]
  | const _         => simp [holeValuesList, skeletonOf, numHoles]
  | lt e₁ e₂ ih₁ ih₂ =>
      simp [holeValuesList, skeletonOf, numHoles, List.length_append, ih₁, ih₂]
  | ifE e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
      simp [holeValuesList, skeletonOf, numHoles, List.length_append, ih₁, ih₂, ih₃]
  | letE _ e₁ e₂ ih₁ ih₂ =>
      simp [holeValuesList, skeletonOf, numHoles, List.length_append, ih₁, ih₂]


-- The vector of real constants appearing in e, left-to-right. This is the second component of the decomposition function, dec₂.
def holeValues : (e : Expr) → Fin (numHoles (skeletonOf e)) → ℝ
  | .var _ =>
      Fin.elim0
  | .const r =>
      fun _ => r
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


-- The set of expressions whose skeleton is exactly s.
def ExprOfSkel (s : Skeleton) : Type :=
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
  | lt e₁ e₂ ih₁ ih₂ =>
      simp [fillSkeleton, skeletonOf, holeValues, ih₁, ih₂]
  | ifE e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
      simp [fillSkeleton, skeletonOf, holeValues, ih₁, ih₂, ih₃]
  | letE x e₁ e₂ ih₁ ih₂ =>
      simp [fillSkeleton, skeletonOf, holeValues, ih₁, ih₂]

-- Filling then extracting the skeleton recovers the original skeleton.
theorem skeletonOf_fillSkeleton (σ : Skeleton) (v : Fin (numHoles σ) → ℝ) :
  skeletonOf (fillSkeleton σ v) = σ := by
  induction σ with
  | hole =>
      simp [fillSkeleton, skeletonOf]
  | var x =>
      simp [fillSkeleton, skeletonOf]
  | lt s₁ s₂ ih₁ ih₂ =>
      simp [fillSkeleton, skeletonOf, ih₁, ih₂]
  | ifE s₁ s₂ s₃ ih₁ ih₂ ih₃ =>
      simp [fillSkeleton, skeletonOf, ih₁, ih₂, ih₃]
  | letE x s₁ s₂ ih₁ ih₂ =>
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


-- Bijection: ExprOfSkel s <-> (Fin (numHoles s) → ℝ)
noncomputable def exprOfSkel_equiv (σ : Skeleton) :
    ExprOfSkel σ ≃ (Fin (numHoles σ) → ℝ) where
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

-- Transport the Borel sigma-algebra on Fin (numHoles s) → ℝ along the bijection exprOfSkel_equiv s
noncomputable instance exprOfSkel_measurableSpace (σ : Skeleton) :
    MeasurableSpace (ExprOfSkel σ) :=
  MeasurableSpace.comap (exprOfSkel_equiv σ) inferInstance

-- Take disjoint union of exprOfSkel to obtain Expr measurable.
instance expr_measurableSpace : MeasurableSpace Expr where
  MeasurableSet' S :=
    ∀ σ : Skeleton, MeasurableSet (α := ExprOfSkel σ)
      { p : ExprOfSkel σ | p.1 ∈ S }
  measurableSet_empty := by
    intro σ
    simp
  measurableSet_compl := by
    intro S hS σ
    have hSσ := hS σ
    -- {p | p.1 ∈ Sᶜ} = ({p | p.1 ∈ S})ᶜ  in ExprOfSkel σ
    convert MeasurableSet.compl hSσ using 1
  measurableSet_iUnion := by
    intro f hf σ
    have : { p : ExprOfSkel σ | p.1 ∈ ⋃ i, f i } =
           ⋃ i, { p : ExprOfSkel σ | p.1 ∈ f i } := by
      ext ⟨e, he⟩; simp [Set.mem_iUnion]
    rw [this]
    exact MeasurableSet.iUnion (fun i => hf i σ)


/-
-- ---------------------------------------------------------------------------
-- Small-step semantics
--
-- `step e : Dist (Option Expr)`, where:
--   · `some e'` = transition to e'
--   · `none`    = observe-failure
--
-- Non-value subexpressions use monadic bind:
--   ⟦sub⟧ >>= λ g. δ_{ctx[g]}
--
-- Termination: `step` is defined by well-founded recursion on `sizeOf e`.
-- The top-level match is directly on `e` (no outer `if isValue` guard),
-- so Lean can see that every recursive call is on a strict subterm.
-- Value cases are handled inside each branch via an early `if isValue`
-- return, except for the base constructors which are listed as a catch-all.
-- ---------------------------------------------------------------------------

/-- δ_{some e} — Dirac on a successful next expression. -/
noncomputable def diracNext (e : Expr) : Dist (Option Expr) :=
  Dist.ret (some e)

/-- δ_{none} — Dirac on observe-failure. -/
noncomputable def diracFail : Dist (Option Expr) :=
  Dist.ret none

/-
/-- Dirac on a runtime error expression. -/
noncomputable def diracErr (msg : String) : Dist (Option Expr) :=
  diracNext (.runtimeError msg)
-/

/--
`bindStep μ ctx` implements  `μ >>= λ g. ctx g`
for the "subexpression not yet a value" rows of the denotational table.
Observe-failures propagate as `none`.
-/
noncomputable def bindStep
    (μ : Dist (Option Expr))
    (ctx : Expr → Dist (Option Expr)) : Dist (Option Expr) :=
  μ >>= fun
    | none   => diracFail
    | some g => ctx g

/--
One-step small-step semantics  `step e : Dist (Option Expr)`.

Structural termination is established by matching directly on `e` at the
top level, so every recursive call `step sub` is visibly on a constructor
argument of `e`, which Lean accepts as structurally smaller.
-/
noncomputable def step : Expr → Dist (Option Expr)
  | .const r =>
      diracNext (.const r)
  | .var _ =>
      -- Free variables are stuck in the fragment semantics.
      diracFail
  | .letE x e1 e2 =>
      if isValue e1 then
        diracNext (subst x e1 e2)
      else
        bindStep (step e1) (fun e1' => diracNext (.letE x e1' e2))
  | .lt e1 e2 =>
      if !isValue e1 then
        bindStep (step e1) (fun e1' => diracNext (.lt e1' e2))
      else if !isValue e2 then
        bindStep (step e2) (fun e2' => diracNext (.lt e1 e2'))
      else
        match (e1, e2) with
        | (.const r1, .const r2) =>
            diracNext (.const (if r1 < r2 then 1 else 0))
        | _ => diracFail
  | .ifE c tbr fbr =>
      if !isValue c then
        bindStep (step c) (fun c' => diracNext (.ifE c' tbr fbr))
      else
        match c with
        | .const r => if r = 0 then diracNext fbr else diracNext tbr
        | _        => diracFail

  /-
  Commented out constructs/rules outside the fragment:
  bool, sample, discrete, cmp, andE, orE, notE, pair, fstE, sndE, funE, app,
  finConst, finCmp, finEq, observe, fixE, nil, cons, matchList, unit, seq,
  runtimeError.
  -/

-- ---------------------------------------------------------------------------
-- Multi-step semantics
-- ---------------------------------------------------------------------------

/-- `n`-step semantics by iterating the one-step transformer. -/
noncomputable def bigStepN : Nat → Expr → Dist (Option Expr)
  | 0,          e => Dist.ret (some e)
  | Nat.succ n, e =>
      Dist.bind (bigStepN n e) fun s =>
        match s with
        | none    => Dist.ret none
        | some e' => if isValue e' then Dist.ret (some e') else step e'
-/



end Slice
