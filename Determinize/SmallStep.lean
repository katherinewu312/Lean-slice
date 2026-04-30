import Determinize.Syntax
import Determinize.TypeSystem
import Determinize.Monad

namespace Determinize

open MeasureTheory ProbabilityTheory

/-- TODO: Fill in measurable space later -/
instance : MeasurableSpace Expr := ⊤

instance (τ : Ty) : MeasurableSpace (ExprsOfType τ) := ⊤

/-- Syntactic values in the current fragment. -/
def isValue : Expr → Bool
  | .const _ => true
  | .trueE => true
  | .falseE => true
  | _ => false

namespace Untyped

/-- Small-step semantics over untyped expressions. -/
noncomputable def step : Expr → Dist Expr
  | .const c =>
      Dist.ret (.const c)
  | .trueE =>
      Dist.ret .trueE
  | .falseE =>
      Dist.ret .falseE
  | .var x =>
      Dist.ret (.var x)
  | .letE x e1 e2 =>
      if isValue e1 then
        Dist.ret (subst x e1 e2)
      else
        Dist.bind (step e1) (fun g => Dist.ret (.letE x g e2))
  | .ifE e1 e2 e3 =>
      match e1 with
      | .trueE => Dist.ret e2
      | .falseE => Dist.ret e3
      | _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.ifE g e2 e3))
  | .add e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          Dist.ret (.const (v1 + v2))
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.add (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.add g e2))
  | .mul e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          Dist.ret (.const (v1 * v2))
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.mul (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.mul g e2))
  | .lt e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          if v1 < v2 then Dist.ret .trueE else Dist.ret .falseE
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.lt (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.lt g e2))
  | .uniform e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          if v1 < v2 then
            Dist.bind (Dist.uniform v1 v2) (fun r => Dist.ret (.const r))
          else
            0
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.uniform (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.uniform g e2))
  | .gaussian e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          Dist.bind (Dist.gaussian v1 v2) (fun r => Dist.ret (.const r))
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.gaussian (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.gaussian g e2))
  | .beta e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          Dist.bind (Dist.beta v1 v2) (fun r => Dist.ret (.const r))
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.beta (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.beta g e2))
  | .gamma e1 e2 =>
      match e1, e2 with
      | .const v1, .const v2 =>
          Dist.bind (Dist.gamma v1 v2) (fun r => Dist.ret (.const r))
      | .const v1, _ =>
          Dist.bind (step e2) (fun g => Dist.ret (.gamma (.const v1) g))
      | _, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.gamma g e2))
  | .exponential e1 =>
      match e1 with
      | .const v1 =>
          Dist.bind (Dist.exponential v1) (fun r => Dist.ret (.const r))
      | _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.exponential g))
  | .poisson e1 =>
      match e1 with
      | .const v1 =>
          Dist.bind (Dist.poisson v1) (fun r => Dist.ret (.const r))
      | _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.poisson g))

end Untyped

/-- Typed small-step semantics. -/
noncomputable def step {τ : Ty} (e : ExprsOfType τ) : Dist (ExprsOfType τ) := by
  classical
  exact
    (Untyped.step e.1).map (fun e' =>
      if h : HasType Ctx.empty e' τ then
        (⟨e', h⟩ : ExprsOfType τ)
      else
        e)

/-- Well-definedness for typed inputs: stepping a typed term yields a distribution on typed terms. -/
lemma step_well_defined {τ : Ty} (e : ExprsOfType τ) :
    ∃ μ : Dist (ExprsOfType τ), μ = step e := by
  exact ⟨step e, rfl⟩

end Determinize
