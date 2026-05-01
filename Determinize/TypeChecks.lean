import Determinize.Syntax

namespace Determinize

/-- Some examples of typed expressions. -/

-- const can be typed at either mode
example : TExpr (.float .E) :=
  .const (1 : ℝ)

example : TExpr (.float .G) :=
  .const (1 : ℝ)

-- comparison requires both operands ≼ G
example : TExpr .bool :=
  .lt
    (.const (m := .G) (1 : ℝ))
    (.const (m := .G) (2 : ℝ))
    (ModeLE.refl .G)
    (ModeLE.refl .G)

-- addition is mode-parametric
example : TExpr (.float .E) :=
  .add
    (.const (m := .G) (1 : ℝ))
    (.const (m := .G) (2 : ℝ))
    ModeLE.g_le_e
    ModeLE.g_le_e

example : TExpr (.float .G) :=
  .add
    (.const (m := .G) (1 : ℝ))
    (.const (m := .G) (2 : ℝ))
    (ModeLE.refl .G)
    (ModeLE.refl .G)

example : TExpr (.float .E) :=
  .add
    (.const (m := .G) (1 : ℝ))
    (.const (m := .E) (2 : ℝ))
    ModeLE.g_le_e
    (ModeLE.refl .E)

-- general multiplication
example : TExpr (.float .E) :=
  .mulG
    (.const (m := .G) (2 : ℝ))
    (.const (m := .G) (3 : ℝ))
    (ModeLE.refl .G)
    (ModeLE.refl .G)

-- literal-specialized multiplication into E
example : TExpr (.float .E) :=
  .mulConstL
    (m1 := .E)
    (m2 := .G)
    (2 : ℝ)
    (.const (m := .G) (3 : ℝ))
    (ModeLE.refl .E)
    ModeLE.g_le_e

-- if
example : TExpr (.float .E) :=
  .ifE
    .trueE
    (.const (m := .E) (0 : ℝ))
    (.const (m := .E) (1 : ℝ))

-- let
example : TExpr (.float .E) :=
  .letE
    "x"
    (.const (m := .E) (1 : ℝ))
    (.add
      (.var "x")
      (.const (m := .G) (2 : ℝ))
      (ModeLE.refl .E)
      ModeLE.g_le_e)

-- uniform
example : TExpr (.float .E) :=
  .uniform
    (.const (m := .G) (0 : ℝ))
    (.const (m := .G) (1 : ℝ))
    ModeLE.g_le_e
    ModeLE.g_le_e

example : TExpr (.float .E) :=
  .uniform
    (.const (m := .E) (0 : ℝ))
    (.const (m := .G) (1 : ℝ))
    (ModeLE.refl .E)
    ModeLE.g_le_e

-- gaussian: second param must be ≼ G
example : TExpr (.float .E) :=
  .gaussian
    (.const (m := .E) (0 : ℝ))
    (.const (m := .G) (1 : ℝ))
    (ModeLE.refl .E)
    (ModeLE.refl .G)

-- poisson
example : TExpr (.float .E) :=
  .poisson
    (.const (m := .G) (2 : ℝ))
    ModeLE.g_le_e

-- exponential: input mode must be ≼ G
example : TExpr (.float .E) :=
  .exponential
    (.const (m := .G) (2 : ℝ))
    (ModeLE.refl .G)

-- beta: both params must be ≼ G
example : TExpr (.float .E) :=
  .beta
    (.const (m := .G) (1 : ℝ))
    (.const (m := .G) (2 : ℝ))
    (ModeLE.refl .G)
    (ModeLE.refl .G)

-- gamma: second param ≼ G
example : TExpr (.float .E) :=
  .gamma
    (.const (m := .G) (1 : ℝ))
    (.const (m := .G) (2 : ℝ))
    ModeLE.g_le_e
    (ModeLE.refl .G)

-- float subtyping at the type level
example : (.float .G) <: (.float .E) :=
  TySub.float ModeLE.g_le_e

end Determinize
