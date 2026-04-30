import Determinize.TypeSystem

namespace Determinize

/-- Some examples of well-typed expressions. -/

-- const can be typed at either mode
example : HasType Ctx.empty (.const (1 : ℝ)) (.float .E) :=
  HasType.const

example : HasType Ctx.empty (.const (1 : ℝ)) (.float .G) :=
  HasType.const

-- comparison requires both operands ≼ G
example : HasType Ctx.empty (.lt (.const (1 : ℝ)) (.const (2 : ℝ))) .bool := by
  exact HasType.lt
    (HasType.const (m := .G))
    (HasType.const (m := .G))
    (ModeLE.refl .G)
    (ModeLE.refl .G)

-- addition is mode-parametric
example : HasType Ctx.empty (.add (.const (1 : ℝ)) (.const (2 : ℝ))) (.float .E) := by
  exact HasType.add
    (HasType.const (m := .G))
    (HasType.const (m := .G))
    ModeLE.g_le_e
    ModeLE.g_le_e

example : HasType Ctx.empty (.add (.const (1 : ℝ)) (.const (2 : ℝ))) (.float .G) := by
  exact HasType.add
    (HasType.const (m := .G))
    (HasType.const (m := .G))
    (ModeLE.refl .G)
    (ModeLE.refl .G)

example : HasType Ctx.empty (.add (.const (1 : ℝ)) (.const (2 : ℝ))) (.float .E) := by
  exact HasType.add
    (HasType.const (m := .G))
    (HasType.const (m := .E))
    ModeLE.g_le_e
    (ModeLE.refl .E)

-- general multiplication
example : HasType Ctx.empty (.mul (.const (2 : ℝ)) (.const (3 : ℝ))) (.float .E) := by
  exact HasType.mul_g
    (HasType.const (m := .G))
    (HasType.const (m := .G))
    (ModeLE.refl .G)
    (ModeLE.refl .G)

-- literal-specialized multiplication into E
example : HasType Ctx.empty (.mul (.const (2 : ℝ)) (.const (3 : ℝ))) (.float .E) := by
  exact HasType.mul_const_l
    (HasType.const (m := .E))
    (HasType.const (m := .G))
    (ModeLE.refl .E)
    ModeLE.g_le_e

-- if
example : HasType Ctx.empty (.ifE .trueE (.const (0 : ℝ)) (.const (1 : ℝ))) (.float .E) := by
  exact HasType.ifE
    HasType.trueE
    (HasType.const (m := .E))
    (HasType.const (m := .E))

-- let
example :
    HasType Ctx.empty
      (.letE "x" (.const (1 : ℝ)) (.add (.var "x") (.const (2 : ℝ))))
      (.float .E) := by
  refine HasType.letE (τ1 := .float .E) ?h1 ?h2
  · exact HasType.const (m := .E)
  · have hx : (Ctx.extend Ctx.empty "x" (.float .E)) "x" = some (.float .E) := by
      simp [Ctx.extend]
    exact HasType.add
      (HasType.var hx)
      (HasType.const (m := .G))
      (ModeLE.refl .E)
      ModeLE.g_le_e

-- uniform
example : HasType Ctx.empty (.uniform (.const (0 : ℝ)) (.const (1 : ℝ))) (.float .E) := by
  exact HasType.uniform
    (HasType.const (m := .G))
    (HasType.const (m := .G))
    ModeLE.g_le_e
    ModeLE.g_le_e

example : HasType Ctx.empty (.uniform (.const (0 : ℝ)) (.const (1 : ℝ))) (.float .E) := by
  exact HasType.uniform
    (HasType.const (m := .E))
    (HasType.const (m := .G))
    (ModeLE.refl .E)
    ModeLE.g_le_e

-- gaussian: second arg must be ≼ G
example : HasType Ctx.empty (.gaussian (.const (0 : ℝ)) (.const (1 : ℝ))) (.float .E) := by
  exact HasType.gaussian
    (HasType.const (m := .E))
    (HasType.const (m := .G))
    (ModeLE.refl .E)
    (ModeLE.refl .G)

-- float subtyping at the type level
example : (.float .G) <: (.float .E) :=
  TySub.float ModeLE.g_le_e

-- subsumption
example : HasType Ctx.empty (.const (5 : ℝ)) (.float .E) := by
  exact HasType.subsume
    (HasType.const (m := .G))
    (TySub.float ModeLE.g_le_e)

end Determinize
