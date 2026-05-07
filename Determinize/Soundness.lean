import Determinize.BigStep
import Determinize.Determinization
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Determinize

open MeasureTheory

namespace TExpr

/-- Read the real number out of a float value. Non-value cases are unreachable
for elements of `Val (.float m)`. -/
def floatVal {m : Mode} (v : Val (.float m)) : ℝ :=
  match (v : TExpr (.float m)) with
  | .const c =>
      c
  | _ =>
      0

/-- The expression measurable spaces are discrete in the current model, so the
float observation is measurable. -/
theorem measurable_floatVal {m : Mode} :
    Measurable (@floatVal m) := by
  intro s _hs
  exact ⟨_, by trivial, Set.preimage_image_eq _ Subtype.val_injective⟩

/-- Expected value of the big-step semantics of a float expression. -/
noncomputable def expectedFloat {m : Mode} (e : TExpr (.float m)) : ℝ :=
  ∫ v, floatVal v ∂(sem e)

/-- Expected value of a real-valued distribution. -/
noncomputable def expectedReal (μ : Dist ℝ) : ℝ :=
  ∫ r, r ∂μ

/-- Expected value of a distribution over float values. -/
noncomputable def expectedFloatDist {m : Mode} (μ : Dist (Val (.float m))) : ℝ :=
  ∫ v, floatVal v ∂μ

/-- Semantic equivalence of distributions at a type.

At `Float E`, only the expected float observation is compared. At `Float G`,
`Bool`, and `Unit`, the whole value distribution is compared. Product types are
not present in the current `Ty` language; when they are added, their case should
compare the projected distributions structurally. -/
noncomputable def ExpectedEquiv : (τ : Ty) → Dist (Val τ) → Dist (Val τ) → Prop
  | .float .E, μ, ν =>
      expectedFloatDist μ = expectedFloatDist ν
  | .float .G, μ, ν =>
      μ = ν
  | .bool, μ, ν =>
      μ = ν
  | .unit, μ, ν =>
      μ = ν

notation "Eqv[" τ "](" μ ", " ν ")" => ExpectedEquiv τ μ ν

/-- Continuation bind followed by real expectation. -/
noncomputable def expectedBind {τ : Ty} (μ : Dist (Val τ)) (K : Val τ → Dist ℝ) : ℝ :=
  expectedReal (Dist.bind μ K)

/-- Binding the float observation continuation is the same as directly taking
the float expectation. -/
theorem expectedBind_floatVal_ret {m : Mode} (μ : Dist (Val (.float m))) :
    expectedBind μ (fun v => Dist.ret (floatVal v)) = expectedFloatDist μ := by
  unfold expectedBind expectedReal expectedFloatDist Dist.ret
  rw [show (μ.bind fun v => Measure.dirac (floatVal v)) = μ.map floatVal by
    exact Measure.bind_dirac_eq_map μ measurable_floatVal]
  exact integral_map measurable_floatVal.aemeasurable (by fun_prop)

/-- A continuation respects the observation equivalence at its input type when
equivalent input distributions produce the same real expectation after bind. -/
def RespectsExpectedEquiv {τ : Ty} (K : Val τ → Dist ℝ) : Prop :=
  ∀ μ ν : Dist (Val τ), ExpectedEquiv τ μ ν → expectedBind μ K = expectedBind ν K

/-- The n step distribution restricted to values. -/
noncomputable def valueDistAt {τ : Ty} (n : ℕ) (e : TExpr τ) : Dist (Val τ) :=
  Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n e)

/-- Continuation expectation against the value-only `n`-step approximant. -/
noncomputable def expectedBindAt {τ : Ty} (n : ℕ) (e : TExpr τ)
    (K : Val τ → Dist ℝ) : ℝ :=
  expectedBind (valueDistAt n e) K

/-- Expected value of the `n`-step semantics, restricted to values.
Mass on non-value expressions is ignored by the comap to `Val`. -/
noncomputable def expectedFloatAt {m : Mode} (n : ℕ) (e : TExpr (.float m)) : ℝ :=
  ∫ v, floatVal v ∂(valueDistAt n e)

/-- The typed distribution equivalence is reflexive. -/
theorem expectedEquiv_refl {τ : Ty} (μ : Dist (Val τ)) :
    ExpectedEquiv τ μ μ := by
  cases τ with
  | unit =>
      rfl
  | bool =>
      rfl
  | float m =>
      cases m <;> rfl

/-- The typed distribution equivalence is symmetric. -/
theorem expectedEquiv_symm {τ : Ty} {μ ν : Dist (Val τ)}
    (h : ExpectedEquiv τ μ ν) :
    ExpectedEquiv τ ν μ := by
  cases τ with
  | unit =>
      exact h.symm
  | bool =>
      exact h.symm
  | float m =>
      cases m <;> exact h.symm

/-- The typed distribution equivalence is transitive. -/
theorem expectedEquiv_trans {τ : Ty} {μ ν ξ : Dist (Val τ)}
    (hμν : ExpectedEquiv τ μ ν) (hνξ : ExpectedEquiv τ ν ξ) :
    ExpectedEquiv τ μ ξ := by
  cases τ with
  | unit =>
      exact hμν.trans hνξ
  | bool =>
      exact hμν.trans hνξ
  | float m =>
      cases m <;> exact hμν.trans hνξ

/-- Continuations that respect expected equivalence give equal expectations on
any pair of equivalent value distributions. -/
theorem det_sound_continuation {τ : Ty} (μ₁ μ₂ : Dist (Val τ))
    (K : Val τ → Dist ℝ) (hK : RespectsExpectedEquiv K)
    (hμ : ExpectedEquiv τ μ₁ μ₂) :
    expectedBind μ₁ K = expectedBind μ₂ K := by
  exact hK μ₁ μ₂ hμ


/-- Boolean true as a value. -/
def trueVal : Val .bool :=
  ⟨.trueE, by simp [Val, isValue, boolValue?]⟩

/-- Boolean false as a value. -/
def falseVal : Val .bool :=
  ⟨.falseE, by simp [Val, isValue, boolValue?]⟩

/-- At `Float G`, `ExpectedEquiv` is equality of value distributions, so every
continuation respects it. -/
theorem respectsExpectedEquiv_floatG_any
    (K : Val (.float .G) → Dist ℝ) :
    RespectsExpectedEquiv K := by
  intro μ ν hμν
  change μ = ν at hμν
  subst ν
  rfl

/-- At `Bool`, `ExpectedEquiv` is equality of value distributions, so every
continuation respects it. -/
theorem respectsExpectedEquiv_bool_any
    (K : Val .bool → Dist ℝ) :
    RespectsExpectedEquiv K := by
  intro μ ν hμν
  change μ = ν at hμν
  subst ν
  rfl

/-- Right-hand continuation for `<`.

Once the left value `v1` has been evaluated, this continuation evaluates the
right value `v2`, performs the comparison, and then continues with `K`.
-/
noncomputable def ltRightK
    (v1 : Val (.float .G))
    (K : Val .bool → Dist ℝ) :
    Val (.float .G) → Dist ℝ :=
  fun v2 =>
    if floatVal v1 < floatVal v2 then
      K trueVal
    else
      K falseVal

/-- Left-hand continuation for `<`.

This is the continuation passed to the IH for `e1`.
-/
noncomputable def ltLeftK
    (e2 : TExpr (.float .G))
    (K : Val .bool → Dist ℝ) :
    Val (.float .G) → Dist ℝ :=
  fun v1 =>
    Dist.bind (sem e2) (ltRightK v1 K)

/-- Comapping a Dirac measure at an embedded value recovers the Dirac measure
on the value subtype. -/
theorem comap_dirac_value {τ : Ty} (v : Val τ) :
    Measure.comap (Subtype.val : Val τ → TExpr τ) (Measure.dirac (v : TExpr τ)) =
      Measure.dirac v := by
  ext A hA
  rw [Measure.comap_apply (Subtype.val : Val τ → TExpr τ) Subtype.val_injective
    (fun _ _ => by trivial) _ hA]
  rw [Measure.dirac_apply, Measure.dirac_apply]
  by_cases hv : v ∈ A
  · have himg : (v : TExpr τ) ∈ Set.image (Subtype.val : Val τ → TExpr τ) A :=
      ⟨v, hv, rfl⟩
    simp [Set.indicator_of_mem, hv, himg]
  · have himg : (v : TExpr τ) ∉ Set.image (Subtype.val : Val τ → TExpr τ) A := by
      intro h
      rcases h with ⟨w, hw, hwv⟩
      exact hv (Subtype.val_injective hwv ▸ hw)
    simp [Set.indicator_of_notMem, hv, himg]

/-- Values are absorbing for the small-step semantics. -/
theorem step_value {τ : Ty} (v : Val τ) :
    step (v : TExpr τ) = Dist.ret (v : TExpr τ) := by
  rcases v with ⟨t, hv⟩
  cases τ <;> cases t <;>
    simp [Val, isValue, unitValue?, boolValue?, floatValue?, step] at hv ⊢

/-- Any finite-step approximation of a value is the same value. -/
theorem nstep_value {τ : Ty} (v : Val τ) (n : ℕ) :
    nstep n (v : TExpr τ) = Dist.ret (v : TExpr τ) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [nstep, ih]
      unfold Dist.ret Dist.bind
      rw [Measure.dirac_bind]
      · exact step_value v
      · fun_prop

/-- The big-step semantics of a value is the corresponding Dirac distribution. -/
theorem sem_value {τ : Ty} (v : Val τ) :
    sem (v : TExpr τ) = Dist.ret v := by
  apply le_antisymm
  · apply iSup_le
    intro n
    rw [nstep_value v n]
    simp [Dist.ret, comap_dirac_value]
  · exact le_iSup_of_le 0 (by
      rw [nstep_value v 0]
      simp [Dist.ret, comap_dirac_value])

/-- Every function out of a value subtype is measurable in the current discrete
expression model. -/
theorem measurable_from_val {τ : Ty} {α : Type} [MeasurableSpace α]
    (f : Val τ → α) :
    Measurable f := by
  intro s _hs
  rw [← Set.preimage_image_eq (Set.preimage f s) Subtype.val_injective]
  exact ⟨_, by trivial, rfl⟩

/-- A monotone supremum of measures is pointwise on measurable sets. -/
theorem measure_iSup_apply_of_monotone {α : Type} [MeasurableSpace α]
    (μ : ℕ → Measure α) (hμ : Monotone μ) {A : Set α} (hA : MeasurableSet A) :
    (⨆ n, μ n) A = ⨆ n, μ n A := by
  let ν : Measure α := Measure.ofMeasurable (fun s _ => ⨆ n, μ n s)
    (by simp)
    (by
      intro f hf hdisj
      simp_rw [measure_iUnion hdisj hf]
      simp_rw [ENNReal.tsum_eq_iSup_sum]
      have hsum : ∀ s : Finset ℕ,
          (∑ a ∈ s, ⨆ n, μ n (f a)) = ⨆ n, ∑ a ∈ s, μ n (f a) := by
        intro s
        exact ENNReal.finsetSum_iSup_of_monotone
          (fun i n m hnm => hμ hnm (f i))
      simp_rw [hsum]
      rw [iSup_comm])
  have hν_apply : ∀ s, MeasurableSet s → ν s = ⨆ n, μ n s := by
    intro s hs
    exact Measure.ofMeasurable_apply s hs
  have hle : (⨆ n, μ n) ≤ ν := by
    apply iSup_le
    intro n
    rw [Measure.le_iff]
    intro s hs
    rw [hν_apply s hs]
    exact le_iSup (fun m => μ m s) n
  have hν_le : ν ≤ (⨆ n, μ n) := by
    rw [Measure.le_iff]
    intro s hs
    rw [hν_apply s hs]
    exact iSup_le fun n => le_iSup (fun m => μ m) n s
  rw [← hν_apply A hA]
  exact le_antisymm (hle A) (hν_le A)

/-- Big-step decomposition for evaluating the left operand of `<`. -/
theorem sem_lt_left
    (e1 e2 : TExpr (.float .G)) :
    sem (.lt e1 e2 (ModeLE.refl .G) (ModeLE.refl .G))
      =
    Dist.bind (sem e1) fun v1 =>
      sem (.lt (v1 : TExpr (.float .G)) e2 (ModeLE.refl .G) (ModeLE.refl .G)) := by
  /-
  This is the finite-approximant/iSup step: the total fuel used by
  `lt e1 e2` splits into fuel for `e1` and then fuel for the continuation.
  -/
  sorry

/-- Big-step decomposition for evaluating the right operand of `<` once the
left operand is already a value. -/
theorem sem_lt_right
    (v1 : Val (.float .G))
    (e2 : TExpr (.float .G)) :
    sem (.lt (v1 : TExpr (.float .G)) e2 (ModeLE.refl .G) (ModeLE.refl .G))
      =
    Dist.bind (sem e2) fun v2 =>
      if floatVal v1 < floatVal v2 then
        Dist.ret trueVal
      else
        Dist.ret falseVal := by
  /-
  This is the second finite-approximant/iSup step: with the left value fixed,
  the remaining fuel is exactly the fuel for `e2`, followed by one comparison
  step.
  -/
  sorry

/-- Big-step/continuation form of the semantics of `<`.

This packages the left-to-right evaluation behavior of `lt`: evaluate `e1`,
then evaluate `e2`, then compare the resulting float values.
-/
theorem sem_lt
    (e1 e2 : TExpr (.float .G)) :
    sem (.lt e1 e2 (ModeLE.refl .G) (ModeLE.refl .G))
      =
    Dist.bind (sem e1) fun v1 =>
      Dist.bind (sem e2) fun v2 =>
        if floatVal v1 < floatVal v2 then
          Dist.ret trueVal
        else
          Dist.ret falseVal := by
  rw [sem_lt_left e1 e2]
  apply Measure.bind_congr_right
  filter_upwards with v1
  exact sem_lt_right v1 e2

theorem expectedBind_sem_lt
    (e1 e2 : TExpr (.float .G))
    (K : Val .bool → Dist ℝ) :
    expectedBind (sem (.lt e1 e2 (ModeLE.refl .G) (ModeLE.refl .G))) K
      =
    expectedBind (sem e1) (ltLeftK e2 K) := by
  rw [sem_lt]
  unfold expectedBind ltLeftK ltRightK
  unfold Dist.bind
  apply congrArg expectedReal
  rw [Measure.bind_bind]
  ·
    apply Measure.bind_congr_right
    filter_upwards with v1
    rw [Measure.bind_bind]
    · apply Measure.bind_congr_right
      filter_upwards with v2
      by_cases h : floatVal v1 < floatVal v2
      · simp [h, Dist.ret, Measure.dirac_bind (measurable_from_val K) trueVal]
      · simp [h, Dist.ret, Measure.dirac_bind (measurable_from_val K) falseVal]
    · exact (measurable_from_val _).aemeasurable
    · exact (measurable_from_val K).aemeasurable
  · exact (measurable_from_val _).aemeasurable
  · exact (measurable_from_val K).aemeasurable


/-- If two right-hand expressions give the same expected result under every
comparison continuation, then the corresponding left continuations have the
same expected result pointwise.
-/
theorem ltLeftK_det_congr
    (e2 : TExpr (.float .G))
    (ih2 :
      ∀ K : Val (.float .G) → Dist ℝ,
        RespectsExpectedEquiv K →
        expectedBind (sem e2) K = expectedBind (sem (det e2)) K)
    (K : Val .bool → Dist ℝ)
    (v1 : Val (.float .G)) :
    expectedReal (ltLeftK e2 K v1)
      =
    expectedReal (ltLeftK (det e2) K v1) := by
  unfold ltLeftK
  exact ih2 (ltRightK v1 K) (respectsExpectedEquiv_floatG_any (ltRightK v1 K))

/-- Expectation law for bind. -/
theorem expectedReal_bind {τ : Ty}
    (μ : Dist (Val τ))
    (K : Val τ → Dist ℝ) :
    expectedReal (Dist.bind μ K) = ∫ v, expectedReal (K v) ∂μ := by
  /-
  This is the real-valued bind law:

      E[μ >>= K] = ∫ v, E[K v] dμ.

  The proof should follow from the corresponding `lintegral` bind law plus the
  positive/negative decomposition of the Bochner integral.
  -/
  sorry

/-- Congruence for `expectedBind`.

If two continuations have the same real expectation at every value, then
binding either one against the same input distribution gives the same real
expectation.
-/
theorem expectedBind_congr_expected {τ : Ty}
    (μ : Dist (Val τ))
    (K₁ K₂ : Val τ → Dist ℝ)
    (hK : ∀ v, expectedReal (K₁ v) = expectedReal (K₂ v)) :
    expectedBind μ K₁ = expectedBind μ K₂ := by
  calc
    expectedBind μ K₁ = ∫ v, expectedReal (K₁ v) ∂μ := by
      simpa [expectedBind] using expectedReal_bind μ K₁
    _ = ∫ v, expectedReal (K₂ v) ∂μ := by
      exact integral_congr_ae (Filter.Eventually.of_forall hK)
    _ = expectedBind μ K₂ := by
      simpa [expectedBind] using (expectedReal_bind μ K₂).symm

/-- Strong continuation form of determinization soundness.

This is the theorem that should be proved by induction. Intuitively, every context/continuation that respects
the observation equivalence cannot distinguish `e` from `det e`.
-/
theorem det_sound_cps {τ : Ty} (e : TExpr τ) :
    ∀ K : Val τ → Dist ℝ,
      RespectsExpectedEquiv K →
      expectedBind (sem e) K = expectedBind (sem (det e)) K := by
  induction e with
  | var x =>
      intro K hK
      simp [det]

  | unitE =>
      intro K hK
      simp [det]

  | const c =>
      intro K hK
      simp [det]

  | trueE =>
      intro K hK
      simp [det]

  | falseE =>
      intro K hK
      simp [det]

  | letE x e1 e2 ih1 ih2 =>
      intro K hK
      /-
      Desired proof shape:

      1. Expand the semantics of `let`.
      2. Use `ih1` on `e1`.
      3. The continuation passed to `e1` is the semantics of the body.
      4. Prove that this continuation respects `ExpectedEquiv` using `ih2`.

      This case will probably require a substitution/environment version of
      the induction hypothesis if your `let` semantics substitutes values into
      `e2`.
      -/
      sorry

  | lt e1 e2 h1 h2 ih1 ih2 =>
      intro K hK

      /-
      Since `<` needs `Float G` operands, these cases should force the operand
      modes to be `.G`. The impossible `.E ≼ .G` cases disappear because of
      `not_e_le_g`.
      -/
      cases h1
      cases h2

      /-
      Goal is now morally:

        expectedBind (sem (e1 < e2)) K
        =
        expectedBind (sem (det e1 < det e2)) K

      Expand both sides using the semantic lemma for `<`.
      -/
      simp only [det]
      rw [expectedBind_sem_lt e1 e2 K]
      rw [expectedBind_sem_lt (det e1) (det e2) K]

      /-
      Now use the IH for `e1`.

      The continuation for `e1` is:
        ltLeftK e2 K

      Since `e1 : Float G`, every continuation respects `ExpectedEquiv`.
      -/
      calc
        expectedBind (sem e1) (ltLeftK e2 K)
            =
        expectedBind (sem (det e1)) (ltLeftK e2 K) := by
          exact ih1 (ltLeftK e2 K)
            (respectsExpectedEquiv_floatG_any (ltLeftK e2 K))

        _ =
        expectedBind (sem (det e1)) (ltLeftK (det e2) K) := by
          /-
          This step uses `ih2` pointwise inside the continuation.

          You will probably need an expectation-bind congruence lemma here:
          if two continuations have the same expected real result pointwise,
          then binding against the same distribution gives the same expected
          real result.
          -/
          apply expectedBind_congr_expected
          intro v1
          exact ltLeftK_det_congr e2 ih2 K v1

  | add e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      Use linearity of expectation.

      The proof should reduce to:
        E[e1 + e2] = E[e1] + E[e2]
      and then use `ih1` and `ih2`.
      -/
      sorry

  | mulG e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      This should only be sound if the inputs are in a mode where full
      distributional equivalence is available, e.g. Float G.

      If this consumes Float E inputs, this theorem is probably false.
      -/
      sorry

  | mulConstL c e h1 h2 ih =>
      intro K hK
      /-
      Use:
        E[c * e] = c * E[e]
      then use `ih`.
      -/
      sorry

  | mulConstR e c h1 h2 ih =>
      intro K hK
      /-
      Use:
        E[e * c] = E[e] * c
      then use `ih`.
      -/
      sorry

  | div e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      Be careful: this is not expectation-preserving in general.

      In general:
        E[e1 / e2] ≠ E[e1] / E[e2].

      This case should only go through if your typing rule forces enough
      distributional information, for example if both operands are Float G, or
      if division is restricted to constants.
      -/
      sorry

  | ifE c t f ihc iht ihf =>
      intro K hK
      /-
      Proof shape:

      1. Use `ihc` to show the condition is preserved.
      2. Since booleans use full distributional equality in `ExpectedEquiv`,
         the probability of each branch is preserved.
      3. Use `iht` and `ihf` for the branches.
      -/
      sorry

  | uniform e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      For Float E result, use:
        E[uniform(a,b)] = (E[a] + E[b]) / 2

      More precisely, if the endpoints are themselves expressions:
        E[let a = e1 in let b = e2 in uniform(a,b)]
        =
        (E[e1] + E[e2]) / 2

      Then use `ih1` and `ih2`.
      -/
      sorry

  | gaussian e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      If `gaussian(mean, variance)` has expectation `mean`, use:
        E[gaussian(e1,e2)] = E[e1]

      Then use `ih1`.

      The variance argument usually does not affect the expected value, but
      it still must be well-typed/valid.
      -/
      sorry

  | poisson e h ih =>
      intro K hK
      /-
      If `poisson(rate)` has expectation `rate`, use:
        E[poisson(e)] = E[e]
      then use `ih`.
      -/
      sorry

  | exponential e h ih =>
      intro K hK
      /-
      Be careful about parameterization.

      If `exponential(a)` means rate `a`, then:
        E[exponential(a)] = 1 / a

      That is not expectation-preserving under replacing `a` by E[a].

      If `exponential(a)` means mean `a`, then:
        E[exponential(a)] = a

      This case is sound only under the second convention or with stronger
      restrictions.
      -/
      sorry

  | beta e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      Be careful:
        E[beta(a,b)] = a / (a + b)

      This is nonlinear in `a` and `b`, so replacing parameters by expectations
      is not sound in general unless your typing rules force `a` and `b` to be
      distributionally preserved or deterministic.
      -/
      sorry

  | gamma e1 e2 h1 h2 ih1 ih2 =>
      intro K hK
      /-
      Depends on parameterization.

      Shape/rate:
        E[gamma(a,b)] = a / b

      Shape/scale:
        E[gamma(a,b)] = a * b

      The shape/rate version is nonlinear because of division.
      -/
      sorry

  | subsume e h ih =>
      intro K hK
      /-
      Usually use `ih`, plus a lemma saying subsumption does not change
      semantics except for the observation relation.
      -/
      sorry

/-- Main determinization soundness theorem: determinization preserves the
expected value of float expressions. -/
theorem det_sound {m : Mode} (e : TExpr (.float m)) :
    expectedFloat e = expectedFloat (det e) := by
  let K : Val (.float m) → Dist ℝ :=
    fun v => Dist.ret (floatVal v)
  have hK : RespectsExpectedEquiv K := by
    intro μ ν hμν
    cases m with
    | E =>
        change expectedFloatDist μ = expectedFloatDist ν at hμν
        rw [expectedBind_floatVal_ret, expectedBind_floatVal_ret]
        exact hμν
    | G =>
        unfold ExpectedEquiv at hμν
        subst ν
        rfl
  have hleft : expectedFloat e = expectedBind (sem e) K := by
    exact (expectedBind_floatVal_ret (sem e)).symm
  have hright : expectedFloat (det e) = expectedBind (sem (det e)) K := by
    exact (expectedBind_floatVal_ret (sem (det e))).symm
  calc
    expectedFloat e
        = expectedBind (sem e) K := hleft
    _   = expectedBind (sem (det e)) K := det_sound_cps e K hK
    _   = expectedFloat (det e) := hright.symm

end TExpr

end Determinize
