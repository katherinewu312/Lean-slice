import Determinize.Syntax

namespace Determinize

namespace TExpr

/-- The mode preorder does not relate `E` to `G`. -/
lemma not_e_le_g : ¬ (.E ≼ .G) := by
  intro h
  cases h

/-- Preserves a float expression, in particular from Float G to Float E.
For cases like gaussian(0 : G, 1 : G) : E, where det = 0 : G, but the original expression has outer type E. -/
def subsumeFloat {m1 m2 : Mode} (h : m1 ≼ m2) (e : TExpr (.float m1)) :
    TExpr (.float m2) :=
  match m1, m2 with
  | .E, .E =>
      e
  | .G, .G =>
      e
  | .G, .E =>
      .subsume e (Sub.float h)
  | .E, .G =>
      False.elim (not_e_le_g h)

/-- Determinization function. -/
def det : {τ : Ty} → TExpr τ → TExpr τ
  | _, .var x =>
      .var x
  | _, .unitE =>
      .unitE
  | _, .const c =>
      .const c
  | _, .trueE =>
      .trueE
  | _, .falseE =>
      .falseE
  | _, .pair e1 e2 =>
      .pair (det e1) (det e2)
  | _, .letE x e1 e2 =>
      .letE x (det e1) (det e2)
  | _, .lt e1 e2 h1 h2 =>
      .lt (det e1) (det e2) h1 h2
  | .float m, .add e1 e2 h1 h2 =>
      .add (m := m) (det e1) (det e2) h1 h2
  | .float m, .mulG e1 e2 h1 h2 =>
      .mulG (m := m) (det e1) (det e2) h1 h2
  | .float m, .mulConstL c e h1 h2 =>
      .mulConstL (m := m) c (det e) h1 h2
  | .float m, .mulConstR e c h1 h2 =>
      .mulConstR (m := m) (det e) c h1 h2
  | .float m, .div e1 e2 h1 h2 =>
      .div (m := m) (det e1) (det e2) h1 h2
  | _, .subsume e h =>
      .subsume (det e) h
  | _, .ifE c t f =>
      .ifE (det c) (det t) (det f)
  | .float .E, .uniform e1 e2 h1 h2 =>
      let e1' := det e1
      let e2' := det e2
      .mulConstR
        (m1 := .E)
        (m2 := .E)
        (m := .E)
        (.add (m := .E) e1' e2' h1 h2)
        (0.5 : ℝ)
        (ModeLE.refl .E)
        (ModeLE.refl .E)
  | .float .G, .uniform e1 e2 h1 h2 =>
      .uniform (m := .G) (det e1) (det e2) h1 h2
  | .float .E, .gaussian e1 _e2 h1 _h2 =>
      subsumeFloat h1 (det e1)
  | .float .G, .gaussian e1 e2 h1 h2 =>
      .gaussian (m := .G) (det e1) (det e2) h1 h2
  | .float .E, .poisson e h =>
      subsumeFloat h (det e)
  | .float .G, .poisson e h =>
      .poisson (m := .G) (det e) h
  | .float .E, .exponential e h =>
      .div
        (m := .E)
        (.const (m := .E) (1 : ℝ))
        (det e)
        (ModeLE.refl .E)
        h
  | .float .G, .exponential e h =>
      .exponential (m := .G) (det e) h
  | .float .E, .beta e1 e2 h1 h2 =>
      let h1E := modeLe_trans h1 ModeLE.g_le_e
      let e1' := det e1
      let e2' := det e2
      .div
        (m := .E)
        e1'
        (.add (m := .G) e1' e2' h1 h2)
        h1E
        (ModeLE.refl .G)
  | .float .G, .beta e1 e2 h1 h2 =>
      .beta (m := .G) (det e1) (det e2) h1 h2
  | .float .E, .gamma e1 e2 h1 h2 =>
      .div
        (m := .E)
        (det e1)
        (det e2)
        h1
        h2
  | .float .G, .gamma e1 e2 h1 h2 =>
      .gamma (m := .G) (det e1) (det e2) h1 h2

/-- Examples. -/
example (c : ℝ) :
    det (.const (m := .G) c) = .const (m := .G) c :=
  rfl

example :
    det
      (.poisson
        (m := .E)
        (.const (m := .G) (8 : ℝ))
        ModeLE.g_le_e) =
      .subsume
        (.const (m := .G) (8 : ℝ))
        (Sub.float ModeLE.g_le_e) :=
  rfl

example :
    det
      (.gaussian
        (m := .E)
        (.const (m := .G) (0 : ℝ))
        (.const (m := .G) (1 : ℝ))
        ModeLE.g_le_e
        (ModeLE.refl .G)) =
      .subsume
        (.const (m := .G) (0 : ℝ))
        (Sub.float ModeLE.g_le_e) :=
  rfl

example :
    det
      (.gaussian
        (m := .E)
        (.uniform
          (.const (m := .E) (0 : ℝ))
          (.const (m := .E) (1 : ℝ))
          (ModeLE.refl .E)
          (ModeLE.refl .E))
        (.const (m := .G) (1 : ℝ))
        (ModeLE.refl .E)
        (ModeLE.refl .G)) =
      .mulConstR
        (m1 := .E)
        (m2 := .E)
        (m := .E)
        (.add
          (m := .E)
          (.const (m := .E) (0 : ℝ))
          (.const (m := .E) (1 : ℝ))
          (ModeLE.refl .E)
          (ModeLE.refl .E))
        (0.5 : ℝ)
        (ModeLE.refl .E)
        (ModeLE.refl .E) :=
  rfl

example :
    det
      (.exponential
        (m := .E)
        (.const (m := .G) (2 : ℝ))
        (ModeLE.refl .G)) =
      .div
        (m := .E)
        (.const (m := .E) (1 : ℝ))
        (.const (m := .G) (2 : ℝ))
        (ModeLE.refl .E)
        (ModeLE.refl .G) :=
  rfl

end TExpr

end Determinize
