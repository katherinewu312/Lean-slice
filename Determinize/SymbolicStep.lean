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

/-- Symbolic residual expressions.  The `value` node marks that its subtree
has taken one symbolic deterministic step, even when it is nested. -/
inductive SymExpr : Ty → Type where
  | expr {τ : Ty} : TExpr τ → SymExpr τ
  | sym : String → SymExpr (.float .E)
  | value {τ : Ty} : SymExpr τ → SymExpr τ
  | pair {τ1 τ2 : Ty} : SymExpr τ1 → SymExpr τ2 → SymExpr (.pair τ1 τ2)
  | letE {τ1 τ2 : Ty} : String → SymExpr τ1 → SymExpr τ2 → SymExpr τ2
  | lt {m1 m2 : Mode} :
      SymExpr (.float m1) → SymExpr (.float m2) →
      m1 ≼ .G → m2 ≼ .G → SymExpr .bool
  | add {m1 m2 m : Mode} :
      SymExpr (.float m1) → SymExpr (.float m2) →
      m1 ≼ m → m2 ≼ m → SymExpr (.float m)
  | mulG {m1 m2 m : Mode} :
      SymExpr (.float m1) → SymExpr (.float m2) →
      m1 ≼ .G → m2 ≼ .G → SymExpr (.float m)
  | mulConstL {m1 m2 m : Mode} :
      ℝ → SymExpr (.float m2) → m1 ≼ m → m2 ≼ m → SymExpr (.float m)
  | mulConstR {m1 m2 m : Mode} :
      SymExpr (.float m1) → ℝ → m1 ≼ m → m2 ≼ m → SymExpr (.float m)
  | div {m1 m2 m : Mode} :
      SymExpr (.float m1) → SymExpr (.float m2) →
      m1 ≼ m → m2 ≼ .G → SymExpr (.float m)
  | ifE {τ : Ty} : SymExpr .bool → SymExpr τ → SymExpr τ → SymExpr τ
  | uniform {m1 m2 m : Mode} :
      SymExpr (.float m1) → SymExpr (.float m2) →
      m1 ≼ m → m2 ≼ m → SymExpr (.float m)
  | gaussian {m1 m2 m : Mode} :
      SymExpr (.float m1) → SymExpr (.float m2) →
      m1 ≼ m → m2 ≼ .G → SymExpr (.float m)
  | poisson {m1 m : Mode} : SymExpr (.float m1) → m1 ≼ m → SymExpr (.float m)
  | exponential {m1 m : Mode} : SymExpr (.float m1) → m1 ≼ .G → SymExpr (.float m)
  | beta {m1 m2 m : Mode} :
      SymExpr (.float m1) → SymExpr (.float m2) →
      m1 ≼ .G → m2 ≼ .G → SymExpr (.float m)
  | gamma {m1 m2 m : Mode} :
      SymExpr (.float m1) → SymExpr (.float m2) →
      m1 ≼ m → m2 ≼ .G → SymExpr (.float m)
  | subsume {τ1 τ2 : Ty} : SymExpr τ1 → τ1 <: τ2 → SymExpr τ2

namespace SymExpr

/-- Converts a well-typed symbolic expresison back to its original well-typed expression. -/
def erase : {τ : Ty} → SymExpr τ → TExpr τ
  | _, .expr e =>
      e
  | _, .sym x =>
      .var x
  | _, .value e =>
      erase e
  | _, .pair e1 e2 =>
      .pair (erase e1) (erase e2)
  | _, .letE x e1 e2 =>
      .letE x (erase e1) (erase e2)
  | _, .lt e1 e2 h1 h2 =>
      .lt (erase e1) (erase e2) h1 h2
  | .float m, .add e1 e2 h1 h2 =>
      .add (m := m) (erase e1) (erase e2) h1 h2
  | .float m, .mulG e1 e2 h1 h2 =>
      .mulG (m := m) (erase e1) (erase e2) h1 h2
  | .float m, .mulConstL c e h1 h2 =>
      .mulConstL (m := m) c (erase e) h1 h2
  | .float m, .mulConstR e c h1 h2 =>
      .mulConstR (m := m) (erase e) c h1 h2
  | .float m, .div e1 e2 h1 h2 =>
      .div (m := m) (erase e1) (erase e2) h1 h2
  | _, .ifE c t f =>
      .ifE (erase c) (erase t) (erase f)
  | .float m, .uniform e1 e2 h1 h2 =>
      .uniform (m := m) (erase e1) (erase e2) h1 h2
  | .float m, .gaussian e1 e2 h1 h2 =>
      .gaussian (m := m) (erase e1) (erase e2) h1 h2
  | .float m, .poisson e h =>
      .poisson (m := m) (erase e) h
  | .float m, .exponential e h =>
      .exponential (m := m) (erase e) h
  | .float m, .beta e1 e2 h1 h2 =>
      .beta (m := m) (erase e1) (erase e2) h1 h2
  | .float m, .gamma e1 e2 h1 h2 =>
      .gamma (m := m) (erase e1) (erase e2) h1 h2
  | _, .subsume e h =>
      .subsume (erase e) h

/-- Lifts a well-typed expression to its well-typed symbolic expression. -/
def ofTExpr : {τ : Ty} → TExpr τ → SymExpr τ
  | _, .var x =>
      .expr (.var x)
  | _, .unitE =>
      .expr .unitE
  | _, .const c =>
      .expr (.const c)
  | _, .trueE =>
      .expr .trueE
  | _, .falseE =>
      .expr .falseE
  | _, .pair e1 e2 =>
      .pair (ofTExpr e1) (ofTExpr e2)
  | _, .letE x e1 e2 =>
      .letE x (ofTExpr e1) (ofTExpr e2)
  | _, .lt e1 e2 h1 h2 =>
      .lt (ofTExpr e1) (ofTExpr e2) h1 h2
  | .float m, .add e1 e2 h1 h2 =>
      .add (m := m) (ofTExpr e1) (ofTExpr e2) h1 h2
  | .float m, .mulG e1 e2 h1 h2 =>
      .mulG (m := m) (ofTExpr e1) (ofTExpr e2) h1 h2
  | .float m, .mulConstL c e h1 h2 =>
      .mulConstL (m := m) c (ofTExpr e) h1 h2
  | .float m, .mulConstR e c h1 h2 =>
      .mulConstR (m := m) (ofTExpr e) c h1 h2
  | .float m, .div e1 e2 h1 h2 =>
      .div (m := m) (ofTExpr e1) (ofTExpr e2) h1 h2
  | _, .ifE c t f =>
      .ifE (ofTExpr c) (ofTExpr t) (ofTExpr f)
  | .float m, .uniform e1 e2 h1 h2 =>
      .uniform (m := m) (ofTExpr e1) (ofTExpr e2) h1 h2
  | .float m, .gaussian e1 e2 h1 h2 =>
      .gaussian (m := m) (ofTExpr e1) (ofTExpr e2) h1 h2
  | .float m, .poisson e h =>
      .poisson (m := m) (ofTExpr e) h
  | .float m, .exponential e h =>
      .exponential (m := m) (ofTExpr e) h
  | .float m, .beta e1 e2 h1 h2 =>
      .beta (m := m) (ofTExpr e1) (ofTExpr e2) h1 h2
  | .float m, .gamma e1 e2 h1 h2 =>
      .gamma (m := m) (ofTExpr e1) (ofTExpr e2) h1 h2
  | _, .subsume e h =>
      .subsume (ofTExpr e) h

/-- Source-variable substitution.

This is used for source `letE`.
It replaces source variables `.expr (.var x)`, but it does not replace
symbolic atoms `.sym x`.
-/
def substVar {σ τ : Ty} (x : String) (v : SymExpr σ) : SymExpr τ → SymExpr τ
  | .expr (.var y) =>
      if x = y then
        if h : σ = τ then
          cast (congrArg SymExpr h) v
        else
          .expr (.var y)
      else
        .expr (.var y)

  | .expr e =>
      .expr (TExpr.subst x (erase v) e)

  | .sym y =>
      .sym y

  | .value e =>
      .value (substVar x v e)

  | .pair e1 e2 =>
      .pair (substVar x v e1) (substVar x v e2)

  | .letE y e1 e2 =>
      if x = y then
        .letE y (substVar x v e1) e2
      else
        .letE y (substVar x v e1) (substVar x v e2)

  | .lt e1 e2 h1 h2 =>
      .lt (substVar x v e1) (substVar x v e2) h1 h2

  | .add e1 e2 h1 h2 =>
      .add (substVar x v e1) (substVar x v e2) h1 h2

  | .mulG e1 e2 h1 h2 =>
      .mulG (substVar x v e1) (substVar x v e2) h1 h2

  | .mulConstL c e h1 h2 =>
      .mulConstL c (substVar x v e) h1 h2

  | .mulConstR e c h1 h2 =>
      .mulConstR (substVar x v e) c h1 h2

  | .div e1 e2 h1 h2 =>
      .div (substVar x v e1) (substVar x v e2) h1 h2

  | .ifE c t f =>
      .ifE (substVar x v c) (substVar x v t) (substVar x v f)

  | .uniform e1 e2 h1 h2 =>
      .uniform (substVar x v e1) (substVar x v e2) h1 h2

  | .gaussian e1 e2 h1 h2 =>
      .gaussian (substVar x v e1) (substVar x v e2) h1 h2

  | .poisson e h =>
      .poisson (substVar x v e) h

  | .exponential e h =>
      .exponential (substVar x v e) h

  | .beta e1 e2 h1 h2 =>
      .beta (substVar x v e1) (substVar x v e2) h1 h2

  | .gamma e1 e2 h1 h2 =>
      .gamma (substVar x v e1) (substVar x v e2) h1 h2

  | .subsume e h =>
      .subsume (substVar x v e) h


/-- Symbolic-atom substitution.

This is used by `actualWithSigma` and `expectedWithSigma`.
It replaces `.sym x`, but it does not touch source variables `.expr (.var x)`.
-/
def substSym {τ : Ty} (x : String) (v : TExpr (.float .E)) :
    SymExpr τ → SymExpr τ
  | .expr e =>
      .expr e

  | .sym y =>
      if x = y then
        ofTExpr v
      else
        .sym y

  | .value e =>
      .value (substSym x v e)

  | .pair e1 e2 =>
      .pair (substSym x v e1) (substSym x v e2)

  | .letE y e1 e2 =>
      .letE y (substSym x v e1) (substSym x v e2)

  | .lt e1 e2 h1 h2 =>
      .lt (substSym x v e1) (substSym x v e2) h1 h2

  | .add e1 e2 h1 h2 =>
      .add (substSym x v e1) (substSym x v e2) h1 h2

  | .mulG e1 e2 h1 h2 =>
      .mulG (substSym x v e1) (substSym x v e2) h1 h2

  | .mulConstL c e h1 h2 =>
      .mulConstL c (substSym x v e) h1 h2

  | .mulConstR e c h1 h2 =>
      .mulConstR (substSym x v e) c h1 h2

  | .div e1 e2 h1 h2 =>
      .div (substSym x v e1) (substSym x v e2) h1 h2

  | .ifE c t f =>
      .ifE (substSym x v c) (substSym x v t) (substSym x v f)

  | .uniform e1 e2 h1 h2 =>
      .uniform (substSym x v e1) (substSym x v e2) h1 h2

  | .gaussian e1 e2 h1 h2 =>
      .gaussian (substSym x v e1) (substSym x v e2) h1 h2

  | .poisson e h =>
      .poisson (substSym x v e) h

  | .exponential e h =>
      .exponential (substSym x v e) h

  | .beta e1 e2 h1 h2 =>
      .beta (substSym x v e1) (substSym x v e2) h1 h2

  | .gamma e1 e2 h1 h2 =>
      .gamma (substSym x v e1) (substSym x v e2) h1 h2

  | .subsume e h =>
      .subsume (substSym x v e) h


end SymExpr

/-- This gives the local result of stepping inside one expression.
It only carries the new samples produced by this one step, not the whole existing environment. -/
structure SymOut (τ : Ty) where
  samples : List SymSample
  residual : SymExpr τ

/-- This represents the actual state of the symbolic semantics.
In other words, SymState.sigma is all symbolic samples accumulated so far. -/
structure SymState (τ : Ty) where
  sigma : List SymSample
  residual : SymExpr τ

/-- TODO: Fix -/
instance : MeasurableSpace SymSample := ⊤
instance (τ : Ty) : MeasurableSpace (SymState τ) := ⊤
instance (τ : Ty) : MeasurableSpace (SymOut τ) := ⊤

namespace SymOut

def ret {τ : Ty} (e : TExpr τ) : SymOut τ :=
  { samples := [], residual := SymExpr.ofTExpr e }

def val {τ : Ty} (e : SymExpr τ) : SymOut τ :=
  { samples := [], residual := .value e }

def keep {τ : Ty} (e : SymExpr τ) : SymOut τ :=
  { samples := [], residual := e }

def map {σ τ : Ty} (f : SymExpr σ → SymExpr τ) (o : SymOut σ) : SymOut τ :=
  { samples := o.samples, residual := f o.residual }

end SymOut

def substRandom (x : String) (v : TExpr (.float .E)) :
    {m : Mode} → SRandom m → SRandom m
  | _, .uniform e1 e2 h1 h2 =>
      .uniform (subst x v e1) (subst x v e2) h1 h2
  | _, .gaussian e1 e2 h1 h2 =>
      .gaussian (subst x v e1) (subst x v e2) h1 h2
  | _, .poisson e h =>
      .poisson (subst x v e) h
  | _, .exponential e h =>
      .exponential (subst x v e) h
  | _, .beta e1 e2 h1 h2 =>
      .beta (subst x v e1) (subst x v e2) h1 h2
  | _, .gamma e1 e2 h1 h2 =>
      .gamma (subst x v e1) (subst x v e2) h1 h2

namespace SymSample

def subst (x : String) (v : TExpr (.float .E)) (sample : SymSample) : SymSample :=
  { sample with random := substRandom x v sample.random }

end SymSample

def freshName (next : Nat) : String :=
  "u" ++ toString next

/-- Sample the symbolic environment and substitute each sampled value through
the remaining environment and residual expression. -/
noncomputable def actualExpr : {τ : Ty} → SymExpr τ → Dist (TExpr τ)
  | _, .expr e =>
      Dist.ret e
  | _, .sym x =>
      Dist.ret (.var x)
  | _, .value e =>
      Dist.bind (actualExpr e) step
  | _, .pair e1 e2 =>
      Dist.bind (actualExpr e1) fun v1 =>
        Dist.bind (actualExpr e2) fun v2 =>
          Dist.ret (.pair v1 v2)
  | _, .letE x e1 e2 =>
      Dist.bind (actualExpr e1) fun v1 =>
        Dist.bind (actualExpr e2) fun v2 =>
          Dist.ret (.letE x v1 v2)
  | _, .lt e1 e2 h1 h2 =>
      Dist.bind (actualExpr e1) fun v1 =>
        Dist.bind (actualExpr e2) fun v2 =>
          Dist.ret (.lt v1 v2 h1 h2)
  | .float m, .add e1 e2 h1 h2 =>
      Dist.bind (actualExpr e1) fun v1 =>
        Dist.bind (actualExpr e2) fun v2 =>
          Dist.ret (.add (m := m) v1 v2 h1 h2)
  | .float m, .mulG e1 e2 h1 h2 =>
      Dist.bind (actualExpr e1) fun v1 =>
        Dist.bind (actualExpr e2) fun v2 =>
          Dist.ret (.mulG (m := m) v1 v2 h1 h2)
  | .float m, .mulConstL c e h1 h2 =>
      Dist.bind (actualExpr e) fun v =>
        Dist.ret (.mulConstL (m := m) c v h1 h2)
  | .float m, .mulConstR e c h1 h2 =>
      Dist.bind (actualExpr e) fun v =>
        Dist.ret (.mulConstR (m := m) v c h1 h2)
  | .float m, .div e1 e2 h1 h2 =>
      Dist.bind (actualExpr e1) fun v1 =>
        Dist.bind (actualExpr e2) fun v2 =>
          Dist.ret (.div (m := m) v1 v2 h1 h2)
  | _, .ifE c t f =>
      Dist.bind (actualExpr c) fun c' =>
        Dist.bind (actualExpr t) fun t' =>
          Dist.bind (actualExpr f) fun f' =>
            Dist.ret (.ifE c' t' f')
  | .float m, .uniform e1 e2 h1 h2 =>
      Dist.bind (actualExpr e1) fun v1 =>
        Dist.bind (actualExpr e2) fun v2 =>
          Dist.ret (.uniform (m := m) v1 v2 h1 h2)
  | .float m, .gaussian e1 e2 h1 h2 =>
      Dist.bind (actualExpr e1) fun v1 =>
        Dist.bind (actualExpr e2) fun v2 =>
          Dist.ret (.gaussian (m := m) v1 v2 h1 h2)
  | .float m, .poisson e h =>
      Dist.bind (actualExpr e) fun v =>
        Dist.ret (.poisson (m := m) v h)
  | .float m, .exponential e h =>
      Dist.bind (actualExpr e) fun v =>
        Dist.ret (.exponential (m := m) v h)
  | .float m, .beta e1 e2 h1 h2 =>
      Dist.bind (actualExpr e1) fun v1 =>
        Dist.bind (actualExpr e2) fun v2 =>
          Dist.ret (.beta (m := m) v1 v2 h1 h2)
  | .float m, .gamma e1 e2 h1 h2 =>
      Dist.bind (actualExpr e1) fun v1 =>
        Dist.bind (actualExpr e2) fun v2 =>
          Dist.ret (.gamma (m := m) v1 v2 h1 h2)
  | _, .subsume e h =>
      Dist.bind (actualExpr e) fun v =>
        Dist.ret (.subsume v h)

noncomputable def actualWithSigma {τ : Ty} :
    List SymSample → SymExpr τ → Dist (TExpr τ)
  | [], residual =>
      actualExpr residual
  | sample :: rest, residual =>
      Dist.bind sample.random.sample fun v =>
        actualWithSigma
          (rest.map (SymSample.subst sample.name v))
          (SymExpr.substSym sample.name v residual)
termination_by sigma _ => sigma.length
decreasing_by simp

/-- Actual interpretation of one symbolic state: sample the LHS of `||` and
plug the results into the RHS. -/
noncomputable def actualState {τ : Ty} (st : SymState τ) : Dist (TExpr τ) :=
  actualWithSigma st.sigma st.residual

/-- Actual interpretation of a symbolic semantics, such as `symbolicStep st`.
This returns an ordinary expression distribution. -/
noncomputable def actual {τ : Ty} (μ : Dist (SymState τ)) : Dist (TExpr τ) :=
  Dist.bind μ actualState

/-- Replace the symbolic environment by expectations, then determinize the
residual expression. -/
noncomputable def expectedWithSigma {τ : Ty} :
    List SymSample → SymExpr τ → Dist (TExpr τ)
  | [], residual =>
      Dist.ret (det residual.erase)
  | sample :: rest, residual =>
      let mean := sample.random.mean
      expectedWithSigma
        (rest.map (SymSample.subst sample.name mean))
        (SymExpr.substSym sample.name mean residual)
termination_by sigma _ => sigma.length
decreasing_by simp

/-- Expected interpretation of one symbolic state: replace each LHS symbolic
sample by its expectation and determinize the RHS. -/
noncomputable def expectedState {τ : Ty} (st : SymState τ) : Dist (TExpr τ) :=
  expectedWithSigma st.sigma st.residual

/-- Expected interpretation of a symbolic semantics, such as `symbolicStep st`.
This returns an ordinary expression distribution for the determinized program. -/
noncomputable def expected {τ : Ty} (μ : Dist (SymState τ)) : Dist (TExpr τ) :=
  Dist.bind μ expectedState

/-- Float expressions that can be treated as values without symbolic atoms. -/
def isSymFloat : {m : Mode} → TExpr (.float m) → Bool
  | _, .var _ =>
      false
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

/-- Values for plain expressions inside symbolic stepping. Source variables are not values. -/
def isSymValue : {τ : Ty} → TExpr τ → Bool
  | _, .var _ =>
      false
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

namespace SymExpr

def isValue : {τ : Ty} → SymExpr τ → Bool
  | _, .value _ =>
      true
  | _, .sym _ =>
      true
  | _, .expr .unitE =>
      true
  | _, .expr (.const _) =>
      true
  | _, .expr .trueE =>
      true
  | _, .expr .falseE =>
      true
  | .pair _ _, .pair e1 e2 =>
      isValue e1 && isValue e2
  | _, _ =>
      false

def floatValue? {m : Mode} (e : SymExpr (.float m)) : Option ℝ :=
  TExpr.floatValue? e.erase

def boolValue? (e : SymExpr .bool) : Option Bool :=
  TExpr.boolValue? e.erase

def subsumedValue? {τ1 τ2 : Ty} (e : SymExpr τ1) (h : τ1 <: τ2) :
    Option (TExpr τ2) :=
  TExpr.subsumedValue? e.erase h

end SymExpr

noncomputable def mapOut {σ τ : Ty}
    (μ : Dist (SymOut σ)) (f : SymExpr σ → SymExpr τ) : Dist (SymOut τ) :=
  Dist.bind μ (fun o => Dist.ret (o.map f))

noncomputable def finishFloat {m : Mode} (next : Nat)
    (r : SRandom m) : Dist (SymOut (.float m)) :=
  match m with
  | .E =>
      let x := freshName next
      Dist.ret { samples := [{ name := x, random := r }], residual := .sym x }
  | .G =>
      Dist.bind r.sample (fun e => Dist.ret (SymOut.ret e))

/-- One symbolic step inside an expression. Expectation-mode samples are
recorded; general-mode samples are sampled immediately.

For the lt, add, mul, div cases, ig the operands are symbolic values but floatValue? cannot compute concrete numbers, return SymOut.val (...), which constructs .value (...)

For example:
u0 + 2 → value(u0 + 2)
u0 + 2 + 5 → (value (u0 + 2)) + 5 → value ((value (u0 + 2)) + 5) -/
noncomputable def symbolicStepSym (next : Nat) : {τ : Ty} → SymExpr τ → Dist (SymOut τ)
  | _, .expr e =>
      Dist.ret (SymOut.ret e)
  | _, .sym x =>
      Dist.ret (SymOut.keep (.sym x))
  | _, .value e =>
      Dist.ret (SymOut.keep (.value e))
  | _, .pair e1 e2 =>
      if e1.isValue then
        if e2.isValue then
          Dist.ret (SymOut.keep (.pair e1 e2))
        else
          mapOut (symbolicStepSym next e2) (fun g => .pair e1 g)
      else
        mapOut (symbolicStepSym next e1) (fun g => .pair g e2)
  | _, .letE x e1 e2 =>
      if e1.isValue then
        Dist.ret (SymOut.keep (SymExpr.substVar x e1 e2))
      else
        mapOut (symbolicStepSym next e1) (fun g => .letE x g e2)
  | _, .ifE c t f =>
      match c.boolValue? with
      | some true =>
          Dist.ret (SymOut.keep t)
      | some false =>
          Dist.ret (SymOut.keep f)
      | none =>
          if c.isValue then
            Dist.ret (SymOut.keep (.ifE c t f))
          else
            mapOut (symbolicStepSym next c) (fun g => .ifE g t f)
  | _, .lt e1 e2 h1 h2 =>
      match e1.floatValue?, e2.floatValue? with
      | some v1, some v2 =>
          Dist.ret (SymOut.ret (if v1 < v2 then .trueE else .falseE))
      | _, _ =>
          if e1.isValue then
            if e2.isValue then
              Dist.ret (SymOut.val (.lt e1 e2 h1 h2))
            else
              mapOut (symbolicStepSym next e2) (fun g => .lt e1 g h1 h2)
          else
            mapOut (symbolicStepSym next e1) (fun g => .lt g e2 h1 h2)
  | .float m, .add e1 e2 h1 h2 =>
      match e1.floatValue?, e2.floatValue? with
      | some v1, some v2 =>
          Dist.ret (SymOut.ret (.const (m := m) (v1 + v2)))
      | _, _ =>
          if e1.isValue then
            if e2.isValue then
              Dist.ret (SymOut.val (.add (m := m) e1 e2 h1 h2))
            else
              mapOut (symbolicStepSym next e2) (fun g => .add (m := m) e1 g h1 h2)
          else
            mapOut (symbolicStepSym next e1) (fun g => .add (m := m) g e2 h1 h2)
  | .float m, .mulG e1 e2 h1 h2 =>
      match e1.floatValue?, e2.floatValue? with
      | some v1, some v2 =>
          Dist.ret (SymOut.ret (.const (m := m) (v1 * v2)))
      | _, _ =>
          if e1.isValue then
            if e2.isValue then
              Dist.ret (SymOut.val (.mulG (m := m) e1 e2 h1 h2))
            else
              mapOut (symbolicStepSym next e2) (fun g => .mulG (m := m) e1 g h1 h2)
          else
            mapOut (symbolicStepSym next e1) (fun g => .mulG (m := m) g e2 h1 h2)
  | .float m, .mulConstL c e h1 h2 =>
      match e.floatValue? with
      | some v =>
          Dist.ret (SymOut.ret (.const (m := m) (c * v)))
      | none =>
          if e.isValue then
            Dist.ret (SymOut.val (.mulConstL (m := m) c e h1 h2))
          else
            mapOut (symbolicStepSym next e) (fun g => .mulConstL (m := m) c g h1 h2)
  | .float m, .mulConstR e c h1 h2 =>
      match e.floatValue? with
      | some v =>
          Dist.ret (SymOut.ret (.const (m := m) (v * c)))
      | none =>
          if e.isValue then
            Dist.ret (SymOut.val (.mulConstR (m := m) e c h1 h2))
          else
            mapOut (symbolicStepSym next e) (fun g => .mulConstR (m := m) g c h1 h2)
  | .float m, .div e1 e2 h1 h2 =>
      match e1.floatValue?, e2.floatValue? with
      | some v1, some v2 =>
          Dist.ret (SymOut.ret (.const (m := m) (v1 / v2)))
      | _, _ =>
          if e1.isValue then
            if e2.isValue then
              Dist.ret (SymOut.val (.div (m := m) e1 e2 h1 h2))
            else
              mapOut (symbolicStepSym next e2) (fun g => .div (m := m) e1 g h1 h2)
          else
            mapOut (symbolicStepSym next e1) (fun g => .div (m := m) g e2 h1 h2)
  | .float m, .uniform e1 e2 h1 h2 =>
      if e1.isValue then
        if e2.isValue then
          finishFloat next (.uniform e1.erase e2.erase h1 h2)
        else
          mapOut (symbolicStepSym next e2) (fun g => .uniform (m := m) e1 g h1 h2)
      else
        mapOut (symbolicStepSym next e1) (fun g => .uniform (m := m) g e2 h1 h2)
  | .float m, .gaussian e1 e2 h1 h2 =>
      if e1.isValue then
        if e2.isValue then
          finishFloat next (.gaussian e1.erase e2.erase h1 h2)
        else
          mapOut (symbolicStepSym next e2) (fun g => .gaussian (m := m) e1 g h1 h2)
      else
        mapOut (symbolicStepSym next e1) (fun g => .gaussian (m := m) g e2 h1 h2)
  | .float m, .poisson e h =>
      if e.isValue then
        finishFloat next (.poisson e.erase h)
      else
        mapOut (symbolicStepSym next e) (fun g => .poisson (m := m) g h)
  | .float m, .exponential e h =>
      if e.isValue then
        finishFloat next (.exponential e.erase h)
      else
        mapOut (symbolicStepSym next e) (fun g => .exponential (m := m) g h)
  | .float m, .beta e1 e2 h1 h2 =>
      if e1.isValue then
        if e2.isValue then
          finishFloat next (.beta e1.erase e2.erase h1 h2)
        else
          mapOut (symbolicStepSym next e2) (fun g => .beta (m := m) e1 g h1 h2)
      else
        mapOut (symbolicStepSym next e1) (fun g => .beta (m := m) g e2 h1 h2)
  | .float m, .gamma e1 e2 h1 h2 =>
      if e1.isValue then
        if e2.isValue then
          finishFloat next (.gamma e1.erase e2.erase h1 h2)
        else
          mapOut (symbolicStepSym next e2) (fun g => .gamma (m := m) e1 g h1 h2)
      else
        mapOut (symbolicStepSym next e1) (fun g => .gamma (m := m) g e2 h1 h2)
  | _, .subsume e h =>
      match e.subsumedValue? h with
      | some v =>
          Dist.ret (SymOut.ret v)
      | none =>
          if e.isValue then
            Dist.ret (SymOut.val (.subsume e h))
          else
            mapOut (symbolicStepSym next e) (fun g => .subsume g h)

noncomputable def symbolicStepExpr (next : Nat) {τ : Ty} (e : TExpr τ) :
    Dist (SymOut τ) :=
  symbolicStepSym next (SymExpr.ofTExpr e)

/-- One symbolic step on a state `<sigma || residual>`.
That is, run the local expression step symbolicStepExpr, then append out.samples onto the existing st.sigma. -/
noncomputable def symbolicStep {τ : Ty} (st : SymState τ) : Dist (SymState τ) :=
  match st.residual with
  | .value _ =>
      Dist.ret st
  | .expr residual =>
      Dist.bind (symbolicStepExpr st.sigma.length residual) fun out =>
        Dist.ret { sigma := st.sigma ++ out.samples, residual := out.residual }
  | residual =>
      Dist.bind (symbolicStepSym st.sigma.length residual) fun out =>
        Dist.ret { sigma := st.sigma ++ out.samples, residual := out.residual }

/-- The symbolic small-step semantics iterated `n` times. -/
noncomputable def symbolicNstep {τ : Ty} : Nat → SymState τ → Dist (SymState τ)
  | 0, st =>
      Dist.ret st
  | n + 1, st =>
      Dist.bind (symbolicNstep n st) symbolicStep

/-- Initial symbolic state for an expression. -/
def symbolicInitial {τ : Ty} (e : TExpr τ) : SymState τ :=
  { sigma := [], residual := .expr e }

/-- Relational presentation of the symbolic step function. -/
inductive SymbolicStep {τ : Ty} : SymState τ → Dist (SymState τ) → Prop where
  | eval (st : SymState τ) : SymbolicStep st (symbolicStep st)

lemma symbolic_step_well_defined {τ : Ty} (st : SymState τ) :
    ∃ μ : Dist (SymState τ), SymbolicStep st μ := by
  exact ⟨symbolicStep st, SymbolicStep.eval st⟩

------------------------------
--- Examples ---
------------------------------
/-- A value state is unchanged by one symbolic step. -/
example :
    symbolicStep (symbolicInitial (.const (m := .E) (3 : ℝ))) =
      Dist.ret
        ({ sigma := [], residual := .expr (.const (m := .E) (3 : ℝ)) } :
          SymState (.float .E)) :=
  by
    simp [symbolicStep, symbolicInitial, symbolicStepExpr, symbolicStepSym,
      SymExpr.ofTExpr, SymOut.ret, Dist.ret, Dist.bind]
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
           residual := .sym (freshName 0) } :
          SymState (.float .E)) :=
  by
    simp [symbolicStep, symbolicInitial, symbolicStepExpr, symbolicStepSym,
      SymExpr.ofTExpr, SymExpr.erase, SymExpr.isValue, finishFloat, Dist.ret,
      Dist.bind]
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
              (.sym "u0")
              (.expr (.const (m := .E) (2 : ℝ)))
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
           residual := .sym (freshName 1) } :
          SymState (.float .E)) :=
  by
    simp [symbolicStep, symbolicStepSym, SymExpr.erase, SymExpr.isValue,
      finishFloat, Dist.ret, Dist.bind]
    rw [Measure.dirac_bind (by fun_prop)]

/-- Nested symbolic arithmetic is marked locally, not only at the residual root. -/
example :
    let u : SymExpr (.float .E) := .sym "u0"
    let two : SymExpr (.float .E) := .expr (.const (m := .E) (2 : ℝ))
    let five : SymExpr (.float .E) := .expr (.const (m := .E) (5 : ℝ))
    let inner : SymExpr (.float .E) :=
      .add (m := .E) u two (ModeLE.refl .E) (ModeLE.refl .E)
    symbolicStep
        ({ sigma := [],
           residual := .add (m := .E) inner five
            (ModeLE.refl .E) (ModeLE.refl .E) } :
          SymState (.float .E)) =
      Dist.ret
        ({ sigma := [],
           residual := .add (m := .E) (.value inner) five
            (ModeLE.refl .E) (ModeLE.refl .E) } :
          SymState (.float .E)) :=
  by
    simp [symbolicStep, symbolicStepSym, mapOut, SymOut.map, SymOut.val,
      SymExpr.erase, SymExpr.floatValue?, SymExpr.isValue, floatValue?,
      Dist.ret, Dist.bind]
    repeat rw [Measure.dirac_bind (by fun_prop)]

end TExpr

end Determinize
