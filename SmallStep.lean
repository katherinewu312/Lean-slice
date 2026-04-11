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

/-- Finite weighted sum of Dirac measures on `.const i`, starting at index `i`. -/
noncomputable def discreteMeasureExprFrom (i : Nat) : List Prob → Dist Expr
  | [] => 0
  | p :: qs => p • Dist.ret (.const (i : ℝ)) + discreteMeasureExprFrom (i + 1) qs

def diverge : Dist Expr := 0

noncomputable def step (τ : Ty) : ExprsOfType τ → Dist (ExprsOfType τ)

  -- Values diverge
  | ⟨.const _, _⟩    => 0
  | ⟨.trueE, _⟩      => 0
  | ⟨.falseE, _⟩     => 0
  | ⟨.finconst _ _, _⟩ => 0
  | ⟨.var _, _⟩      => 0

  -- discrete: sorry for now
  | ⟨.discrete _, _⟩ => 0

  -- let x = e1 in e2
  | ⟨.letE x e1 e2, h⟩ =>
      by
        classical
        let hLet : ∃ τ1, HasType Ctx.empty e1 τ1 ∧ HasType (Ctx.extend Ctx.empty x τ1) e2 τ :=
          hasType_letE_inv h
        let τ1 : Ty := Classical.choose hLet
        let h1 : HasType Ctx.empty e1 τ1 := (Classical.choose_spec hLet).1
        let h2 : HasType (Ctx.extend Ctx.empty x τ1) e2 τ := (Classical.choose_spec hLet).2
        exact
          if isValue e1 then
            Dist.ret ⟨subst x e1 e2, subst_preserves_type h1 h2⟩
          else
            Dist.bind
              (step τ1 ⟨e1, h1⟩)
              (fun ⟨g, hg⟩ => Dist.ret ⟨.letE x g e2, HasType.letE hg h2⟩)

  -- if e1 then e2 else e3
  | ⟨.ifE e1 e2 e3, h⟩ =>
      let hc : HasType Ctx.empty e1 .bool := (hasType_ifE_inv h).1
      let ht : HasType Ctx.empty e2 τ := (hasType_ifE_inv h).2.1
      let hf : HasType Ctx.empty e3 τ := (hasType_ifE_inv h).2.2
      match e1 with
      | .trueE  => Dist.ret ⟨e2, ht⟩
      | .falseE => Dist.ret ⟨e3, hf⟩
      | _       =>
          -- e1 is not a boolean value; step e1 and rebuild
          Dist.bind
            (step .bool ⟨e1, hc⟩)
            (fun ⟨g, hg⟩ => Dist.ret ⟨.ifE g e2 e3, HasType.ifE hg ht hf⟩)

  -- e1 < e2
  | ⟨.lt e1 e2, h⟩ =>
      let hInv : τ = .bool ∧ HasType Ctx.empty e1 .real ∧ HasType Ctx.empty e2 .real :=
        hasType_lt_inv h
      let hBool : τ = .bool := hInv.1
      let h1 : HasType Ctx.empty e1 .real := hInv.2.1
      let h2 : HasType Ctx.empty e2 .real := hInv.2.2
      hBool ▸
      match e1 with
      | .const v1 =>
          match e2 with
          | .const v2 =>
              if v1 < v2 then Dist.ret ⟨.trueE, HasType.trueE⟩
              else            Dist.ret ⟨.falseE, HasType.falseE⟩
          | _ =>
              Dist.bind
                (step .real ⟨e2, h2⟩)
                (fun ⟨g, hg⟩ => Dist.ret ⟨.lt (.const v1) g, HasType.lt HasType.const hg⟩)
      | _ =>
          Dist.bind
            (step .real ⟨e1, h1⟩)
            (fun ⟨g, hg⟩ => Dist.ret ⟨.lt g e2, HasType.lt hg h2⟩)

  -- uniform e1 e2: sorry for now
  | ⟨.uniform _ _, _⟩ => 0

termination_by e => sizeOf e.1


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

lemma step_is_subprob_measure (τ : Ty) (e : ExprsOfType τ) :
    IsSubProbabilityMeasure (step τ e) := by sorry

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
lemma step_is_measurable (τ : Ty) : Measurable (step τ) := by
  sorry

noncomputable def stepKernel (τ : Ty) : Kernel (ExprsOfType τ) (ExprsOfType τ) where
  toFun    := step τ
  measurable' := step_is_measurable τ

/-- For typed inputs, `stepKernel` is subprobability. -/
theorem stepKernel_subprob_on_welltyped (τ : Ty) (e : ExprsOfType τ) :
    IsSubProbabilityMeasure (stepKernel τ e) := by
  simpa [stepKernel] using step_is_subprob_measure τ e

end Slice
