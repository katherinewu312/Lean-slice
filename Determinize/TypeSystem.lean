import Determinize.Syntax

namespace Determinize

/-- Typing context: partial map from variables to types. -/
abbrev Ctx := String → Option Ty

namespace Ctx

def empty : Ctx := fun _ => none

def extend (Γ : Ctx) (x : String) (τ : Ty) : Ctx :=
  fun y => if y = x then some τ else Γ y

end Ctx

/-- Mode preorder (`G ≼ E`, and reflexive). -/
inductive ModeLE : Mode → Mode → Prop where
  | refl (m : Mode) : ModeLE m m
  | g_le_e : ModeLE .G .E

infix:50 " ≼ " => ModeLE

lemma modeLe_trans {m1 m2 m3 : Mode} (h12 : m1 ≼ m2) (h23 : m2 ≼ m3) : m1 ≼ m3 := by
  cases h12 with
  | refl m =>
      simpa using h23
  | g_le_e =>
      cases h23 with
      | refl =>
          exact ModeLE.g_le_e

/-- Type subtyping for modes and standard type structure. -/
inductive TySub : Ty → Ty → Prop where
  | refl {τ : Ty} : TySub τ τ
  | float {m1 m2 : Mode} :
      m1 ≼ m2 →
      TySub (.float m1) (.float m2)

infix:50 " <: " => TySub

/-- Declarative typing relation for the current expression fragment. -/
inductive HasType : Ctx → Expr → Ty → Prop where
  | var {Γ : Ctx} {x : String} {τ : Ty} :
      Γ x = some τ →
      HasType Γ (.var x) τ

  | const {Γ : Ctx} {c : ℝ} {m : Mode} :
      HasType Γ (.const c) (.float m)

  | trueE {Γ : Ctx} :
      HasType Γ .trueE .bool

  | falseE {Γ : Ctx} :
      HasType Γ .falseE .bool

  | letE {Γ : Ctx} {x : String} {e1 e2 : Expr} {τ1 τ2 : Ty} :
      HasType Γ e1 τ1 →
      HasType (Ctx.extend Γ x τ1) e2 τ2 →
      HasType Γ (.letE x e1 e2) τ2

  | lt {Γ : Ctx} {e1 e2 : Expr} {m1 m2 : Mode} :
      HasType Γ e1 (.float m1) →
      HasType Γ e2 (.float m2) →
      m1 ≼ .G →
      m2 ≼ .G →
      HasType Γ (.lt e1 e2) .bool

  | add {Γ : Ctx} {e1 e2 : Expr} {m1 m2 m : Mode} :
      HasType Γ e1 (.float m1) →
      HasType Γ e2 (.float m2) →
      m1 ≼ m →
      m2 ≼ m →
      HasType Γ (.add e1 e2) (.float m)

  /-- General-mode multiplication (`Mul-G`). -/
  | mul_g {Γ : Ctx} {e1 e2 : Expr} {m1 m2 m : Mode} :
      HasType Γ e1 (.float m1) →
      HasType Γ e2 (.float m2) →
      m1 ≼ .G →
      m2 ≼ .G →
      HasType Γ (.mul e1 e2) (.float m)

  /-- Literal-left multiplication (`Mul-ConstL`). -/
  | mul_const_l {Γ : Ctx} {c : ℝ} {e : Expr} {m1 m2 m : Mode} :
      HasType Γ (.const c) (.float m1) →
      HasType Γ e (.float m2) →
      m1 ≼ m →
      m2 ≼ m →
      HasType Γ (.mul (.const c) e) (.float m)

  /-- Literal-right multiplication (`Mul-ConstR`). -/
  | mul_const_r {Γ : Ctx} {e : Expr} {c : ℝ} {m1 m2 m : Mode} :
      HasType Γ e (.float m1) →
      HasType Γ (.const c) (.float m2) →
      m1 ≼ m →
      m2 ≼ m →
      HasType Γ (.mul e (.const c)) (.float m)

  | ifE {Γ : Ctx} {c t f : Expr} {τ : Ty} :
      HasType Γ c .bool →
      HasType Γ t τ →
      HasType Γ f τ →
      HasType Γ (.ifE c t f) τ

  | uniform {Γ : Ctx} {e1 e2 : Expr} {m1 m2 m : Mode} :
      HasType Γ e1 (.float m1) →
      HasType Γ e2 (.float m2) →
      m1 ≼ m →
      m2 ≼ m →
      HasType Γ (.uniform e1 e2) (.float m)

  | gaussian {Γ : Ctx} {e1 e2 : Expr} {m1 m2 m : Mode} :
      HasType Γ e1 (.float m1) →
      HasType Γ e2 (.float m2) →
      m1 ≼ m →
      m2 ≼ .G →
      HasType Γ (.gaussian e1 e2) (.float m)

  | poisson {Γ : Ctx} {e1 : Expr} {m1 m : Mode} :
      HasType Γ e1 (.float m1) →
      m1 ≼ m →
      HasType Γ (.poisson e1) (.float m)

  | exponential {Γ : Ctx} {e1 : Expr} {m1 m : Mode} :
      HasType Γ e1 (.float m1) →
      m1 ≼ .G →
      HasType Γ (.exponential e1) (.float m)

  | beta {Γ : Ctx} {e1 e2 : Expr} {m1 m2 m : Mode} :
      HasType Γ e1 (.float m1) →
      HasType Γ e2 (.float m2) →
      m1 ≼ .G →
      m2 ≼ .G →
      HasType Γ (.beta e1 e2) (.float m)

  | gamma {Γ : Ctx} {e1 e2 : Expr} {m1 m2 m : Mode} :
      HasType Γ e1 (.float m1) →
      HasType Γ e2 (.float m2) →
      m1 ≼ m →
      m2 ≼ .G →
      HasType Γ (.gamma e1 e2) (.float m)

  | subsume {Γ : Ctx} {e : Expr} {τ1 τ2 : Ty} :
      HasType Γ e τ1 →
      τ1 <: τ2 →
      HasType Γ e τ2

/-- Closed well-typed terms. -/
def WellTyped (e : Expr) : Prop :=
  ∃ τ, HasType Ctx.empty e τ

/-- Well-typed expressions of type τ in the empty context. -/
def ExprsOfType (τ : Ty) : Type :=
  {e : Expr // HasType Ctx.empty e τ}

end Determinize
