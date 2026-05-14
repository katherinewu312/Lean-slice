import Determinize.SmallStep
import Determinize.Determinization

namespace Determinize

open MeasureTheory ProbabilityTheory

namespace TExpr

/-- A syntactic random source, indexed by the float mode it returns. -/
inductive SRandom : Mode → Type where
  | uniform {m1 m2 m : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ m → m2 ≼ m → SRandom m
  | gaussian {m1 m2 m : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ m → m2 ≼ .G → SRandom m
  | poisson {m1 m : Mode} (e : TExpr (.float m1)) :
      m1 ≼ m → SRandom m
  | exponential {m1 m : Mode} (e : TExpr (.float m1)) :
      m1 ≼ .G → SRandom m
  | beta {m1 m2 m : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ .G → m2 ≼ .G → SRandom m
  | gamma {m1 m2 m : Mode}
      (e1 : TExpr (.float m1)) (e2 : TExpr (.float m2)) :
      m1 ≼ m → m2 ≼ .G → SRandom m

namespace SRandom

def expr : {m : Mode} → SRandom m → TExpr (.float m)
  | _, .uniform e1 e2 h1 h2 =>
      .uniform e1 e2 h1 h2
  | _, .gaussian e1 e2 h1 h2 =>
      .gaussian e1 e2 h1 h2
  | _, .poisson e h =>
      .poisson e h
  | _, .exponential e h =>
      .exponential e h
  | _, .beta e1 e2 h1 h2 =>
      .beta e1 e2 h1 h2
  | _, .gamma e1 e2 h1 h2 =>
      .gamma e1 e2 h1 h2

/-- Concrete sampling for a random source whose parameters have become numerals. -/
noncomputable def sample : {m : Mode} → SRandom m → Dist (TExpr (.float m))
  | m, r@(.uniform e1 e2 _ _) =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.bind (Dist.uniform v1 v2) (fun v => Dist.ret (.const (m := m) v))
      | _, _ =>
          Dist.ret r.expr
  | m, r@(.gaussian e1 e2 _ _) =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.bind (Dist.gaussian v1 v2) (fun v => Dist.ret (.const (m := m) v))
      | _, _ =>
          Dist.ret r.expr
  | m, r@(.poisson e _) =>
      match floatValue? e with
      | some v =>
          Dist.bind (Dist.poisson v) (fun v => Dist.ret (.const (m := m) v))
      | none =>
          Dist.ret r.expr
  | m, r@(.exponential e _) =>
      match floatValue? e with
      | some v =>
          Dist.bind (Dist.exponential v) (fun v => Dist.ret (.const (m := m) v))
      | none =>
          Dist.ret r.expr
  | m, r@(.beta e1 e2 _ _) =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.bind (Dist.beta v1 v2) (fun v => Dist.ret (.const (m := m) v))
      | _, _ =>
          Dist.ret r.expr
  | m, r@(.gamma e1 e2 _ _) =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.bind (Dist.gamma v1 v2) (fun v => Dist.ret (.const (m := m) v))
      | _, _ =>
          Dist.ret r.expr

/-- Symbolic expectation of an expectation-mode random source. -/
noncomputable def mean : SRandom .E → TExpr (.float .E)
  | .uniform e1 e2 h1 h2 =>
      .mulConstR
        (m1 := .E) (m2 := .E) (m := .E)
        (.add (m := .E) e1 e2 h1 h2)
        (2 : ℝ)⁻¹
        (ModeLE.refl .E)
        (ModeLE.refl .E)
  | .gaussian e1 _ h1 _ =>
      subsumeFloat h1 e1
  | .poisson e h =>
      subsumeFloat h e
  | .exponential e h =>
      .div
        (m := .E)
        (.const (m := .E) (1 : ℝ))
        e
        (ModeLE.refl .E)
        h
  | .beta e1 e2 h1 h2 =>
      .div
        (m := .E)
        e1
        (.add (m := .G) e1 e2 h1 h2)
        (modeLe_trans h1 ModeLE.g_le_e)
        (ModeLE.refl .G)
  | .gamma e1 e2 h1 h2 =>
      .div (m := .E) e1 e2 h1 h2

end SRandom

/-- The samples on the LHS of the ||. -/
structure SymSample where
  name : String
  random : SRandom .E

/-- This gives the local result of stepping inside one expression.
It only carries the new samples produced by this one step, not the whole existing environment. -/
structure SymOut (τ : Ty) where
  samples : List SymSample
  residual : TExpr τ

/-- This represents the actual state of the symbolic semantics.
In other words, SymState.sigma is all symbolic samples accumulated so far. -/
structure SymState (τ : Ty) where
  sigma : List SymSample
  residual : TExpr τ

instance : MeasurableSpace SymSample := ⊤
instance (τ : Ty) : MeasurableSpace (SymState τ) := ⊤
instance (τ : Ty) : MeasurableSpace (SymOut τ) := ⊤

namespace SymOut

def ret {τ : Ty} (e : TExpr τ) : SymOut τ :=
  { samples := [], residual := e }

def map {σ τ : Ty} (f : TExpr σ → TExpr τ) (o : SymOut σ) : SymOut τ :=
  { samples := o.samples, residual := f o.residual }

end SymOut

def freshName (next : Nat) : String :=
  "u" ++ toString next

/-- Symbolic float values: constants, symbolic variables, and arithmetic over them. -/
def isSymFloat : {m : Mode} → TExpr (.float m) → Bool
  | _, .var _ =>
      true
  | _, .const _ =>
      true
  | _, .add e1 e2 _ _ =>
      isSymFloat e1 && isSymFloat e2
  | _, .mulG e1 e2 _ _ =>
      isSymFloat e1 && isSymFloat e2
  | _, .mulConstL _ e _ _ =>
      isSymFloat e
  | _, .mulConstR e _ _ _ =>
      isSymFloat e
  | _, .div e1 e2 _ _ =>
      isSymFloat e1 && isSymFloat e2
  | _, .subsume e h =>
      match h with
      | .float _ => isSymFloat e
  | _, _ =>
      false

/-- Values for symbolic stepping; unlike concrete stepping, variables are values. -/
def isSymValue : {τ : Ty} → TExpr τ → Bool
  | _, .var _ =>
      true
  | _, .subsume e _ =>
      isSymValue e
  | .unit, e =>
      (unitValue? e).isSome
  | .bool, e =>
      (boolValue? e).isSome
  | .float _, e =>
      isSymFloat e
  | .pair _ _, .pair e1 e2 =>
      isSymValue e1 && isSymValue e2
  | .pair _ _, _ =>
      false

noncomputable def mapOut {σ τ : Ty}
    (μ : Dist (SymOut σ)) (f : TExpr σ → TExpr τ) : Dist (SymOut τ) :=
  Dist.bind μ (fun o => Dist.ret (o.map f))

noncomputable def finishFloat {m : Mode} (next : Nat)
    (r : SRandom m) : Dist (SymOut (.float m)) :=
  match m with
  | .E =>
      let x := freshName next
      Dist.ret { samples := [{ name := x, random := r }], residual := .var x }
  | .G =>
      Dist.bind r.sample (fun e => Dist.ret (SymOut.ret e))

/-- One symbolic step inside an expression. Expectation-mode samples are
recorded; general-mode samples are sampled immediately. -/
noncomputable def symbolicStepExpr (next : Nat) : {τ : Ty} → TExpr τ → Dist (SymOut τ)
  | _, .var x =>
      Dist.ret (SymOut.ret (.var x))
  | _, .unitE =>
      Dist.ret (SymOut.ret .unitE)
  | _, .const c =>
      Dist.ret (SymOut.ret (.const c))
  | _, .trueE =>
      Dist.ret (SymOut.ret .trueE)
  | _, .falseE =>
      Dist.ret (SymOut.ret .falseE)
  | _, .pair e1 e2 =>
      if isSymValue e1 then
        if isSymValue e2 then
          Dist.ret (SymOut.ret (.pair e1 e2))
        else
          mapOut (symbolicStepExpr next e2) (fun g => .pair e1 g)
      else
        mapOut (symbolicStepExpr next e1) (fun g => .pair g e2)
  | _, .letE x e1 e2 =>
      if isSymValue e1 then
        Dist.ret (SymOut.ret (subst x e1 e2))
      else
        mapOut (symbolicStepExpr next e1) (fun g => .letE x g e2)
  | _, .ifE c t f =>
      match boolValue? c with
      | some true =>
          Dist.ret (SymOut.ret t)
      | some false =>
          Dist.ret (SymOut.ret f)
      | none =>
          if isSymValue c then
            Dist.ret (SymOut.ret (.ifE c t f))
          else
            mapOut (symbolicStepExpr next c) (fun g => .ifE g t f)
  | _, .lt e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.ret (SymOut.ret (if v1 < v2 then .trueE else .falseE))
      | _, _ =>
          if isSymValue e1 then
            if isSymValue e2 then
              Dist.ret (SymOut.ret (.lt e1 e2 h1 h2))
            else
              mapOut (symbolicStepExpr next e2) (fun g => .lt e1 g h1 h2)
          else
            mapOut (symbolicStepExpr next e1) (fun g => .lt g e2 h1 h2)
  | .float m, .add e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.ret (SymOut.ret (.const (m := m) (v1 + v2)))
      | _, _ =>
          if isSymValue e1 then
            if isSymValue e2 then
              Dist.ret (SymOut.ret (.add (m := m) e1 e2 h1 h2))
            else
              mapOut (symbolicStepExpr next e2) (fun g => .add (m := m) e1 g h1 h2)
          else
            mapOut (symbolicStepExpr next e1) (fun g => .add (m := m) g e2 h1 h2)
  | .float m, .mulG e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.ret (SymOut.ret (.const (m := m) (v1 * v2)))
      | _, _ =>
          if isSymValue e1 then
            if isSymValue e2 then
              Dist.ret (SymOut.ret (.mulG (m := m) e1 e2 h1 h2))
            else
              mapOut (symbolicStepExpr next e2) (fun g => .mulG (m := m) e1 g h1 h2)
          else
            mapOut (symbolicStepExpr next e1) (fun g => .mulG (m := m) g e2 h1 h2)
  | .float m, .mulConstL c e h1 h2 =>
      match floatValue? e with
      | some v =>
          Dist.ret (SymOut.ret (.const (m := m) (c * v)))
      | none =>
          if isSymValue e then
            Dist.ret (SymOut.ret (.mulConstL (m := m) c e h1 h2))
          else
            mapOut (symbolicStepExpr next e) (fun g => .mulConstL (m := m) c g h1 h2)
  | .float m, .mulConstR e c h1 h2 =>
      match floatValue? e with
      | some v =>
          Dist.ret (SymOut.ret (.const (m := m) (v * c)))
      | none =>
          if isSymValue e then
            Dist.ret (SymOut.ret (.mulConstR (m := m) e c h1 h2))
          else
            mapOut (symbolicStepExpr next e) (fun g => .mulConstR (m := m) g c h1 h2)
  | .float m, .div e1 e2 h1 h2 =>
      match floatValue? e1, floatValue? e2 with
      | some v1, some v2 =>
          Dist.ret (SymOut.ret (.const (m := m) (v1 / v2)))
      | _, _ =>
          if isSymValue e1 then
            if isSymValue e2 then
              Dist.ret (SymOut.ret (.div (m := m) e1 e2 h1 h2))
            else
              mapOut (symbolicStepExpr next e2) (fun g => .div (m := m) e1 g h1 h2)
          else
            mapOut (symbolicStepExpr next e1) (fun g => .div (m := m) g e2 h1 h2)
  | .float m, .uniform e1 e2 h1 h2 =>
      if isSymValue e1 then
        if isSymValue e2 then
          finishFloat next (.uniform e1 e2 h1 h2)
        else
          mapOut (symbolicStepExpr next e2) (fun g => .uniform (m := m) e1 g h1 h2)
      else
        mapOut (symbolicStepExpr next e1) (fun g => .uniform (m := m) g e2 h1 h2)
  | .float m, .gaussian e1 e2 h1 h2 =>
      if isSymValue e1 then
        if isSymValue e2 then
          finishFloat next (.gaussian e1 e2 h1 h2)
        else
          mapOut (symbolicStepExpr next e2) (fun g => .gaussian (m := m) e1 g h1 h2)
      else
        mapOut (symbolicStepExpr next e1) (fun g => .gaussian (m := m) g e2 h1 h2)
  | .float m, .poisson e h =>
      if isSymValue e then
        finishFloat next (.poisson e h)
      else
        mapOut (symbolicStepExpr next e) (fun g => .poisson (m := m) g h)
  | .float m, .exponential e h =>
      if isSymValue e then
        finishFloat next (.exponential e h)
      else
        mapOut (symbolicStepExpr next e) (fun g => .exponential (m := m) g h)
  | .float m, .beta e1 e2 h1 h2 =>
      if isSymValue e1 then
        if isSymValue e2 then
          finishFloat next (.beta e1 e2 h1 h2)
        else
          mapOut (symbolicStepExpr next e2) (fun g => .beta (m := m) e1 g h1 h2)
      else
        mapOut (symbolicStepExpr next e1) (fun g => .beta (m := m) g e2 h1 h2)
  | .float m, .gamma e1 e2 h1 h2 =>
      if isSymValue e1 then
        if isSymValue e2 then
          finishFloat next (.gamma e1 e2 h1 h2)
        else
          mapOut (symbolicStepExpr next e2) (fun g => .gamma (m := m) e1 g h1 h2)
      else
        mapOut (symbolicStepExpr next e1) (fun g => .gamma (m := m) g e2 h1 h2)
  | _, .subsume e h =>
      match subsumedValue? e h with
      | some v =>
          Dist.ret (SymOut.ret v)
      | none =>
          if isSymValue e then
            Dist.ret (SymOut.ret (.subsume e h))
          else
            mapOut (symbolicStepExpr next e) (fun g => .subsume g h)

/-- One symbolic step on a state `<sigma || residual>`.
That is, run the local expression step symbolicStepExpr, then append out.samples onto the existing st.sigma. -/
noncomputable def symbolicStep {τ : Ty} (st : SymState τ) : Dist (SymState τ) :=
  Dist.bind (symbolicStepExpr st.sigma.length st.residual) fun out =>
    Dist.ret { sigma := st.sigma ++ out.samples, residual := out.residual }

/-- The symbolic small-step semantics iterated `n` times. -/
noncomputable def symbolicNstep {τ : Ty} : Nat → SymState τ → Dist (SymState τ)
  | 0, st =>
      Dist.ret st
  | n + 1, st =>
      Dist.bind (symbolicNstep n st) symbolicStep

/-- Initial symbolic state for an expression. -/
def symbolicInitial {τ : Ty} (e : TExpr τ) : SymState τ :=
  { sigma := [], residual := e }

/-- Relational presentation of the symbolic step function. -/
inductive SymbolicStep {τ : Ty} : SymState τ → Dist (SymState τ) → Prop where
  | eval (st : SymState τ) : SymbolicStep st (symbolicStep st)

lemma symbolic_step_well_defined {τ : Ty} (st : SymState τ) :
    ∃ μ : Dist (SymState τ), SymbolicStep st μ := by
  exact ⟨symbolicStep st, SymbolicStep.eval st⟩

/-- A value state is unchanged by one symbolic step. -/
example :
    symbolicStep (symbolicInitial (.const (m := .E) (3 : ℝ))) =
      Dist.ret
        ({ sigma := [], residual := .const (m := .E) (3 : ℝ) } :
          SymState (.float .E)) :=
  by
    simp [symbolicStep, symbolicInitial, symbolicStepExpr, SymOut.ret, Dist.ret,
      Dist.bind]
    rw [Measure.dirac_bind (by fun_prop)]

/-- An expectation-mode sample is recorded in `sigma` and replaced by a name. -/
example :
    symbolicStep
        (symbolicInitial
          (.uniform
            (m := .E)
            (.const (m := .E) (0 : ℝ))
            (.const (m := .E) (1 : ℝ))
            (ModeLE.refl .E)
            (ModeLE.refl .E))) =
      Dist.ret
        ({ sigma :=
            [{ name := freshName 0,
               random :=
                .uniform
                  (.const (m := .E) (0 : ℝ))
                  (.const (m := .E) (1 : ℝ))
                  (ModeLE.refl .E)
                  (ModeLE.refl .E) }],
           residual := .var (freshName 0) } :
          SymState (.float .E)) :=
  by
    simp [symbolicStep, symbolicInitial, symbolicStepExpr, finishFloat,
      Dist.ret, Dist.bind, isSymValue, isSymFloat]
    rw [Measure.dirac_bind (by fun_prop)]

/-- Existing symbolic samples are preserved; the next sample is appended. -/
example :
    let u0 : SymSample :=
      { name := freshName 0,
        random :=
          (.uniform
            (.const (m := .E) (0 : ℝ))
            (.const (m := .E) (1 : ℝ))
            (ModeLE.refl .E)
            (ModeLE.refl .E)) }
    symbolicStep
        ({ sigma := [u0],
           residual :=
            .uniform
              (m := .E)
              (.var "u0")
              (.const (m := .E) (2 : ℝ))
              (ModeLE.refl .E)
              (ModeLE.refl .E) } :
          SymState (.float .E)) =
      Dist.ret
        ({ sigma :=
            [u0,
             { name := freshName 1,
               random :=
                .uniform
                  (.var "u0")
                  (.const (m := .E) (2 : ℝ))
                  (ModeLE.refl .E)
                  (ModeLE.refl .E) }],
           residual := .var (freshName 1) } :
          SymState (.float .E)) :=
  by
    simp [symbolicStep, symbolicStepExpr, finishFloat,
      Dist.ret, Dist.bind, isSymValue, isSymFloat]
    rw [Measure.dirac_bind (by fun_prop)]

end TExpr

end Determinize
