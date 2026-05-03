import Determinize.Syntax
import Determinize.Monad

namespace Determinize

open MeasureTheory ProbabilityTheory

/-- TODO: Fill in measurable space later. -/
instance (τ : Ty) : MeasurableSpace (TExpr τ) := ⊤

namespace TExpr

def subsumedValue? {τ1 τ2 : Ty} (e : TExpr τ1) (h : τ1 <: τ2) : Option (TExpr τ2) :=
  match h with
  | .unit =>
      match unitValue? e with
      | some _ => some .unitE
      | none => none
  | .bool =>
      match boolValue? e with
      | some true => some .trueE
      | some false => some .falseE
      | none => none
  | .float (m2 := m2) _ =>
      match floatValue? e with
      | some v => some (.const (m := m2) v)
      | none => none

/-- Small-step semantics over typed expressions. -/
noncomputable def step : {τ : Ty} → TExpr τ → Dist (TExpr τ)
  | _, .var x =>
      Dist.ret (.var x)
  | _, .unitE =>
      Dist.ret .unitE
  | _, .const c =>
      Dist.ret (.const c)
  | _, .trueE =>
      Dist.ret .trueE
  | _, .falseE =>
      Dist.ret .falseE
  | _, .letE x e1 e2 =>
      if isValue e1 then
        Dist.ret (subst x e1 e2)
      else
        Dist.bind (step e1) (fun g => Dist.ret (.letE x g e2))
  | _, .ifE c t f =>
      match boolValue? c with
      | some true =>
          Dist.ret t
      | some false =>
          Dist.ret f
      | none =>
          Dist.bind (step c) (fun g => Dist.ret (.ifE g t f))
  | _, .lt e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          if v1 < v2 then Dist.ret .trueE else Dist.ret .falseE
      | some v1, none =>
          Dist.bind (step e2) (fun g => Dist.ret (.lt (.const v1) g h1 h2))
      | none, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.lt g e2 h1 h2))
  | .float m, .add e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.ret (.const (m := m) (v1 + v2))
      | some v1, none =>
          Dist.bind (step e2) (fun g => Dist.ret (.add (.const v1) g h1 h2))
      | none, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.add g e2 h1 h2))
  | .float m, .mulG e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.ret (.const (m := m) (v1 * v2))
      | some v1, none =>
          Dist.bind (step e2) (fun g => Dist.ret (.mulG (.const v1) g h1 h2))
      | none, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.mulG g e2 h1 h2))
  | .float m, .mulConstL c e h1 h2 =>
      match floatValue? e with
      | some v =>
          Dist.ret (.const (m := m) (c * v))
      | none =>
          Dist.bind (step e) (fun g => Dist.ret (.mulConstL c g h1 h2))
  | .float m, .mulConstR e c h1 h2 =>
      match floatValue? e with
      | some v =>
          Dist.ret (.const (m := m) (v * c))
      | none =>
          Dist.bind (step e) (fun g => Dist.ret (.mulConstR g c h1 h2))
  | .float m, .div e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.ret (.const (m := m) (v1 / v2))
      | some v1, none =>
          Dist.bind (step e2) (fun g => Dist.ret (.div (.const v1) g h1 h2))
      | none, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.div g e2 h1 h2))
  | .float m, .uniform e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          if v1 < v2 then
            Dist.bind (Dist.uniform v1 v2) (fun r => Dist.ret (.const (m := m) r))
          else
            0
      | some v1, none =>
          Dist.bind (step e2) (fun g => Dist.ret (.uniform (.const v1) g h1 h2))
      | none, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.uniform g e2 h1 h2))
  | .float m, .gaussian e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.bind (Dist.gaussian v1 v2) (fun r => Dist.ret (.const (m := m) r))
      | some v1, none =>
          Dist.bind (step e2) (fun g => Dist.ret (.gaussian (.const v1) g h1 h2))
      | none, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.gaussian g e2 h1 h2))
  | .float m, .poisson e h =>
      match floatValue? e with
      | some v =>
          Dist.bind (Dist.poisson v) (fun r => Dist.ret (.const (m := m) r))
      | none =>
          Dist.bind (step e) (fun g => Dist.ret (.poisson g h))
  | .float m, .exponential e h =>
      match floatValue? e with
      | some v =>
          Dist.bind (Dist.exponential v) (fun r => Dist.ret (.const (m := m) r))
      | none =>
          Dist.bind (step e) (fun g => Dist.ret (.exponential g h))
  | .float m, .beta e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.bind (Dist.beta v1 v2) (fun r => Dist.ret (.const (m := m) r))
      | some v1, none =>
          Dist.bind (step e2) (fun g => Dist.ret (.beta (.const v1) g h1 h2))
      | none, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.beta g e2 h1 h2))
  | .float m, .gamma e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.bind (Dist.gamma v1 v2) (fun r => Dist.ret (.const (m := m) r))
      | some v1, none =>
          Dist.bind (step e2) (fun g => Dist.ret (.gamma (.const v1) g h1 h2))
      | none, _ =>
          Dist.bind (step e1) (fun g => Dist.ret (.gamma g e2 h1 h2))
  | _, .subsume e h =>
      match subsumedValue? e h with
      | some v => Dist.ret v
      | none => Dist.bind (step e) (fun g => Dist.ret (.subsume g h))

/-- Examples. -/
example :
    let g0 : TExpr (.float .G) :=
      .gaussian
        (m := .G)
        (.const (m := .G) (0 : ℝ))
        (.const (m := .G) (1 : ℝ))
        (ModeLE.refl .G)
        (ModeLE.refl .G)
    let g1 : TExpr (.float .G) :=
      .gaussian
        (m := .G)
        (.const (m := .G) (1 : ℝ))
        (.const (m := .G) (1 : ℝ))
        (ModeLE.refl .G)
        (ModeLE.refl .G)
    let g2 : TExpr (.float .G) :=
      .gaussian
        (m := .G)
        (.const (m := .G) (2 : ℝ))
        (.const (m := .G) (1 : ℝ))
        (ModeLE.refl .G)
        (ModeLE.refl .G)
    step
      (.add
        (m := .G)
        (.add
          (m := .G)
          g0
          g1
          (ModeLE.refl .G)
          (ModeLE.refl .G))
        g2
        (ModeLE.refl .G)
        (ModeLE.refl .G)) =
      Dist.bind
        (Dist.bind
          (Dist.bind
            (Dist.gaussian (0 : ℝ) (1 : ℝ))
            (fun r => Dist.ret (.const (m := .G) r)))
          (fun g =>
            Dist.ret
              (.add
                (m := .G)
                g
                g1
                (ModeLE.refl .G)
                (ModeLE.refl .G))))
        (fun g =>
          Dist.ret
            (.add
              (m := .G)
              g
              g2
              (ModeLE.refl .G)
              (ModeLE.refl .G))) :=
  rfl

example :
    let c0 : TExpr (.float .G) := .const (m := .G) (0 : ℝ)
    let c1 : TExpr (.float .G) := .const (m := .G) (1 : ℝ)
    let c2 : TExpr (.float .G) := .const (m := .G) (2 : ℝ)
    step
      (.add
        (m := .G)
        (.add
          (m := .G)
          c0
          c1
          (ModeLE.refl .G)
          (ModeLE.refl .G))
        c2
        (ModeLE.refl .G)
        (ModeLE.refl .G)) =
      Dist.bind
        (Dist.ret (.const (m := .G) ((0 : ℝ) + (1 : ℝ))))
        (fun g =>
          Dist.ret
            (.add
              (m := .G)
              g
              c2
              (ModeLE.refl .G)
              (ModeLE.refl .G))) :=
  rfl


/-- Relational presentation of the same typed step semantics. -/
inductive Step {τ : Ty} : TExpr τ → Dist (TExpr τ) → Prop where
  | eval (e : TExpr τ) : Step e (step e)

/-- Well-definedness is immediate from the indexed result type. -/
lemma step_well_defined {τ : Ty} (e : TExpr τ) :
    ∃ μ : Dist (TExpr τ), Step e μ := by
  exact ⟨step e, Step.eval e⟩

end TExpr

end Determinize
