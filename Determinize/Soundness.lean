import Determinize.BigStep
import Determinize.Determinization
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace Determinize

open MeasureTheory
open scoped ENNReal

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
`Bool`, `Unit`, and pair types, the whole value distribution is compared. -/
noncomputable def ExpectedEquiv : (τ : Ty) → Dist (Val τ) → Dist (Val τ) → Prop
  | .float .E, μ, ν =>
      expectedFloatDist μ = expectedFloatDist ν
  | .float .G, μ, ν =>
      μ = ν
  | .bool, μ, ν =>
      μ = ν
  | .unit, μ, ν =>
      μ = ν
  | .pair _ _, μ, ν =>
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
  | pair τ1 τ2 =>
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
  | pair τ1 τ2 =>
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
  | pair τ1 τ2 =>
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
  exact step_of_isValue v.property

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

/-- Every function out of a typed expression space is measurable in the
current discrete expression model. -/
theorem measurable_from_texpr {τ : Ty} {α : Type} [MeasurableSpace α]
    (f : TExpr τ → α) :
    Measurable f := by
  intro s _hs
  trivial

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

/-- Value-only finite approximants are monotone as measures. -/
theorem value_approximants_mono {τ : Ty} (e : TExpr τ) :
    Monotone
      (fun n : ℕ =>
        Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n e)) := by
  intro n m hnm
  induction hnm with
  | refl =>
      exact le_rfl
  | @step m _ ih =>
      exact le_trans ih (by
        rw [Measure.le_iff]
        intro A hA
        exact nstep_value_succ_le e hA m)

/-- The `n + 1` step distribution can be factored through the first step. -/
theorem nstep_succ_bind {τ : Ty} (e : TExpr τ) :
    ∀ n : ℕ,
      nstep (n + 1) e =
        Measure.bind (step e) (fun e' => nstep n e') := by
  intro n
  induction n generalizing e with
  | zero =>
      simp [nstep, Dist.bind, Dist.ret,
        Measure.dirac_bind
          (measurable_from_texpr (step : TExpr τ → Dist (TExpr τ))) e,
        Measure.bind_dirac]
  | succ n ih =>
      rw [nstep, ih]
      change
        Measure.bind
            (Measure.bind (step e) (fun e' => nstep n e'))
            (fun e' => step e')
          =
        Measure.bind (step e) (fun e' => nstep (n + 1) e')
      rw [Measure.bind_bind
        ((measurable_from_texpr
          (fun e' : TExpr τ => nstep n e')).aemeasurable)
        ((measurable_from_texpr
          (step : TExpr τ → Dist (TExpr τ))).aemeasurable)]
      apply Measure.bind_congr_right
      filter_upwards with e'
      rw [nstep]
      rfl

/-- Integrating against a monotone supremum of measures is the supremum of the
integrals. -/
theorem lintegral_iSup_measure_of_monotone {α : Type} [MeasurableSpace α]
    (μ : ℕ → Measure α) (hμ : Monotone μ)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂(⨆ n, μ n)) =
      ⨆ n, (∫⁻ x, f x ∂(μ n)) := by
  have hsimple : ∀ φ : SimpleFunc α ℝ≥0∞,
      φ.lintegral (⨆ n, μ n) = ⨆ n, φ.lintegral (μ n) := by
    intro φ
    calc
      φ.lintegral (⨆ n, μ n)
          = ∑ x ∈ φ.range, x * (⨆ n, μ n) (φ ⁻¹' {x}) := by
              rfl
      _ = ∑ x ∈ φ.range, x * (⨆ n, μ n (φ ⁻¹' {x})) := by
              apply Finset.sum_congr rfl
              intro x _hx
              rw [measure_iSup_apply_of_monotone μ hμ
                (SimpleFunc.measurableSet_preimage φ {x})]
      _ = ∑ x ∈ φ.range, ⨆ n, x * μ n (φ ⁻¹' {x}) := by
              simp [ENNReal.mul_iSup]
      _ = ⨆ n, ∑ x ∈ φ.range, x * μ n (φ ⁻¹' {x}) := by
              rw [ENNReal.finsetSum_iSup_of_monotone]
              intro x n m hnm
              exact mul_le_mul_right (hμ hnm (φ ⁻¹' {x})) x
      _ = ⨆ n, φ.lintegral (μ n) := by
              rfl
  calc
    (∫⁻ x, f x ∂(⨆ n, μ n))
        = ⨆ k, (SimpleFunc.eapprox f k).lintegral (⨆ n, μ n) := by
            exact lintegral_eq_iSup_eapprox_lintegral hf
    _ = ⨆ k, ⨆ n, (SimpleFunc.eapprox f k).lintegral (μ n) := by
            simp_rw [hsimple]
    _ = ⨆ n, ⨆ k, (SimpleFunc.eapprox f k).lintegral (μ n) := by
            exact iSup_comm
    _ = ⨆ n, (∫⁻ x, f x ∂(μ n)) := by
            simp_rw [lintegral_eq_iSup_eapprox_lintegral hf]

/-- Continuation expectation against a value-only finite approximant. -/
noncomputable def linExpectedAt {τ : Ty} (n : ℕ) (e : TExpr τ)
    (K : Val τ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ v, K v ∂(valueDistAt n e)

/-- The zeroth value approximant of a non-value has no value mass. -/
theorem valueDistAt_zero_nonvalue {τ : Ty} {e : TExpr τ}
    (he : isValue e = false) :
    valueDistAt 0 e = 0 := by
  ext A hA
  unfold valueDistAt nstep Dist.ret
  rw [Measure.comap_apply (Subtype.val : Val τ → TExpr τ)
    Subtype.val_injective (fun _ _ => by trivial) _ hA]
  rw [Measure.dirac_apply' _ (by trivial :
    MeasurableSet ((Subtype.val : Val τ → TExpr τ) '' A))]
  have hnot : e ∉ (Subtype.val : Val τ → TExpr τ) '' A := by
    intro hmem
    rcases hmem with ⟨v, _hvA, hv⟩
    have hvval : isValue e = true := by
      rw [← hv]
      exact v.property
    rw [he] at hvval
    contradiction
  simp [hnot]

/-- The zeroth value approximant of a value is the corresponding Dirac mass. -/
theorem valueDistAt_zero_value {τ : Ty} (v : Val τ) :
    valueDistAt 0 (v : TExpr τ) = Dist.ret v := by
  unfold valueDistAt nstep Dist.ret
  rw [comap_dirac_value v]

/-- Every finite value approximant is bounded by the big-step semantics. -/
theorem valueDistAt_le_sem {τ : Ty} (n : ℕ) (e : TExpr τ) :
    valueDistAt n e ≤ sem e := by
  unfold valueDistAt sem
  exact le_iSup (fun n : ℕ =>
    Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n e)) n

/-- Scalar finite approximants unfold through one small step. -/
theorem linExpectedAt_succ {τ : Ty} (K : Val τ → ℝ≥0∞)
    (n : ℕ) (e : TExpr τ) :
    linExpectedAt (n + 1) e K =
      ∫⁻ e', linExpectedAt n e' K ∂(step e) := by
  let Kt : TExpr τ → ℝ≥0∞ :=
    fun x => if h : isValue x = true then K ⟨x, h⟩ else 0
  have hKt : ∀ v : Val τ, Kt (v : TExpr τ) = K v := by
    intro v
    rcases v with ⟨x, hx⟩
    change isValue x = true at hx
    dsimp [Kt]
    rw [dif_pos hx]
  unfold linExpectedAt valueDistAt
  rw [nstep_succ_bind e n]
  calc
    (∫⁻ v : Val τ, K v ∂Measure.comap
        (Subtype.val : Val τ → TExpr τ)
        (Measure.bind (step e) fun e' => nstep n e'))
        =
      ∫⁻ v : Val τ, Kt (v : TExpr τ) ∂Measure.comap
        (Subtype.val : Val τ → TExpr τ)
        (Measure.bind (step e) fun e' => nstep n e') := by
          exact lintegral_congr_ae
            (Filter.Eventually.of_forall fun v => (hKt v).symm)
    _ = ∫⁻ x in Val τ, Kt x
          ∂(Measure.bind (step e) fun e' => nstep n e') := by
          exact lintegral_subtype_comap
            (show MeasurableSet (Val τ) by trivial) Kt
    _ = ∫⁻ e', ∫⁻ x in Val τ, Kt x ∂(nstep n e') ∂(step e) := by
          rw [← lintegral_indicator
            (show MeasurableSet (Val τ) by trivial) Kt]
          conv_rhs =>
            enter [2, e']
            rw [← lintegral_indicator
              (show MeasurableSet (Val τ) by trivial) Kt]
          rw [Measure.lintegral_bind]
          · exact (measurable_from_texpr
              (fun e' : TExpr τ => nstep n e')).aemeasurable
          · exact (measurable_from_texpr
              ((Val τ).indicator Kt)).aemeasurable
    _ = ∫⁻ e', ∫⁻ v : Val τ, Kt (v : TExpr τ)
          ∂Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n e')
          ∂(step e) := by
          congr
          funext e'
          exact (lintegral_subtype_comap
            (show MeasurableSet (Val τ) by trivial) Kt).symm
    _ = ∫⁻ e', ∫⁻ v : Val τ, K v
          ∂Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n e')
          ∂(step e) := by
          apply lintegral_congr_ae
          filter_upwards with e'
          exact lintegral_congr_ae
            (Filter.Eventually.of_forall fun v => hKt v)

/-- The big-step scalar expectation is the supremum of scalar finite
approximants. -/
theorem linExpected_sem_eq_iSup {τ : Ty} (e : TExpr τ)
    (K : Val τ → ℝ≥0∞) :
    (∫⁻ v, K v ∂(sem e)) =
      ⨆ n, linExpectedAt n e K := by
  unfold sem linExpectedAt valueDistAt
  exact lintegral_iSup_measure_of_monotone
    (fun n : ℕ =>
      Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n e))
    (value_approximants_mono e)
    (measurable_from_val K)

/-- Big-step semantics is invariant under adding one small-step in front.

This is the Markov/unfolding property of the `iSup`-defined big-step
semantics. Intuitively:

  sem e = step e >>= sem

because `sem e` collects all finite numbers of steps to values.
-/
theorem sem_step_unfold {τ : Ty} (e : TExpr τ) :
    sem e = Dist.bind (step e) (fun e' => sem e') := by
  ext A hA
  unfold sem Dist.bind
  rw [measure_iSup_apply_of_monotone
    (fun n : ℕ =>
      Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n e))
    (value_approximants_mono e) hA]

  have hshift :
      (⨆ n : ℕ,
        (Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n e)) A)
        =
      (⨆ n : ℕ,
        (Measure.comap (Subtype.val : Val τ → TExpr τ)
          (nstep (n + 1) e)) A) := by
    apply le_antisymm
    · exact iSup_le fun n =>
        le_iSup_of_le n (nstep_value_succ_le e hA n)
    · exact iSup_le fun n =>
        le_iSup_of_le (n + 1) le_rfl
  rw [hshift]
  simp_rw [nstep_succ_bind e]
  simp_rw [Measure.comap_apply (Subtype.val : Val τ → TExpr τ)
    Subtype.val_injective (fun _ _ => by trivial) _ hA]

  rw [Measure.bind_apply hA]
  · simp_rw [measure_iSup_apply_of_monotone
      (fun n : ℕ =>
        Measure.comap (Subtype.val : Val τ → TExpr τ) (nstep n _))
      (value_approximants_mono _) hA]
    rw [lintegral_iSup
      (fun n => measurable_from_texpr
        (fun e' : TExpr τ =>
          (Measure.comap (Subtype.val : Val τ → TExpr τ)
            (nstep n e')) A))
      (by
        intro n m hnm e'
        exact value_approximants_mono e' hnm A)]
    congr
    funext n
    rw [Measure.bind_apply
      (by trivial :
        MeasurableSet ((Subtype.val : Val τ → TExpr τ) '' A))]
    · simp_rw [Measure.comap_apply (Subtype.val : Val τ → TExpr τ)
        Subtype.val_injective (fun _ _ => by trivial) _ hA]
    · exact (measurable_from_texpr
        (fun e' : TExpr τ => nstep n e')).aemeasurable
  · exact (measurable_from_texpr
      (fun e' : TExpr τ =>
        ⨆ n, Measure.comap (Subtype.val : Val τ → TExpr τ)
          (nstep n e'))).aemeasurable

/-- Evaluation-context compatibility for a unary context.

If stepping `C e` while `e` is not yet a value is the same as stepping `e`
and rebuilding the context, and the context cannot become a value before the
hole does, then big-step semantics factors through the big-step semantics of
`e`.
-/
theorem sem_eval_context
    {τ σ : Ty}
    (C : TExpr τ → TExpr σ)
    (hvalue :
      ∀ e : TExpr τ,
        isValue (C e) = true →
          isValue e = true)
    (hstep :
      ∀ e : TExpr τ,
        isValue e = false →
          step (C e) =
            Dist.bind (step e) fun e' =>
              Dist.ret (C e'))
    (e : TExpr τ) :
    sem (C e) =
      Dist.bind (sem e) fun v =>
        sem (C (v : TExpr τ)) := by
  ext A hA
  let K : Val τ → ℝ≥0∞ :=
    fun v => sem (C (v : TExpr τ)) A
  let R : TExpr τ → ℝ≥0∞ :=
    fun e => ∫⁻ v, K v ∂(sem e)
  let S : TExpr τ → ℝ≥0∞ :=
    fun e => sem (C e) A

  have hR_value : ∀ v : Val τ, R (v : TExpr τ) = S (v : TExpr τ) := by
    intro v
    simp [R, K, S, sem_value v, Dist.ret]

  have hR_step : ∀ e : TExpr τ,
      R e = ∫⁻ e', R e' ∂(step e) := by
    intro e
    unfold R
    rw [sem_step_unfold e]
    unfold Dist.bind
    rw [Measure.lintegral_bind]
    · exact (measurable_from_texpr
        (fun e' : TExpr τ => sem e')).aemeasurable
    · exact (measurable_from_val K).aemeasurable

  have hS_step : ∀ e : TExpr τ, isValue e = false →
      S e = ∫⁻ e', S e' ∂(step e) := by
    intro e hnon
    unfold S
    have hbind :
        Dist.bind (step (C e)) (fun t => sem t) =
          Dist.bind (step e) (fun e' => sem (C e')) := by
      rw [hstep e hnon]
      unfold Dist.bind Dist.ret
      rw [Measure.bind_bind
        ((measurable_from_texpr
          (fun e' : TExpr τ => Measure.dirac (C e'))).aemeasurable)
        ((measurable_from_texpr
          (fun t : TExpr σ => sem t)).aemeasurable)]
      apply Measure.bind_congr_right
      filter_upwards with e'
      rw [Measure.dirac_bind]
      exact measurable_from_texpr (fun t : TExpr σ => sem t)
    calc
      sem (C e) A
          = (Dist.bind (step (C e)) (fun t => sem t)) A := by
              rw [sem_step_unfold (C e)]
      _ = (Dist.bind (step e) (fun e' => sem (C e'))) A := by
              rw [hbind]
      _ = ∫⁻ e', sem (C e') A ∂(step e) := by
              change (Measure.bind (step e) (fun e' => sem (C e'))) A =
                ∫⁻ e', sem (C e') A ∂(step e)
              rw [Measure.bind_apply hA]
              exact (measurable_from_texpr
                (fun e' : TExpr τ => sem (C e'))).aemeasurable

  have hlin_zero_nonvalue : ∀ {e : TExpr τ},
      isValue e = false → linExpectedAt 0 e K = 0 := by
    intro e hnon
    unfold linExpectedAt
    rw [valueDistAt_zero_nonvalue hnon]
    simp

  have hlin_zero_value : ∀ v : Val τ,
      linExpectedAt 0 (v : TExpr τ) K = R (v : TExpr τ) := by
    intro v
    unfold linExpectedAt R
    rw [valueDistAt_zero_value v, sem_value v]

  have hR_le_S : ∀ e : TExpr τ, R e ≤ S e := by
    intro e
    rw [show R e = ⨆ n, linExpectedAt n e K by
      unfold R
      exact linExpected_sem_eq_iSup e K]
    apply iSup_le
    intro n
    induction n generalizing e with
    | zero =>
        by_cases hv : isValue e = true
        · let v : Val τ := ⟨e, hv⟩
          calc
            linExpectedAt 0 e K = R (v : TExpr τ) := by
              change linExpectedAt 0 (v : TExpr τ) K = R (v : TExpr τ)
              exact hlin_zero_value v
            _ = S (v : TExpr τ) := hR_value v
            _ ≤ S e := le_rfl
        · have hfalse : isValue e = false := by
            exact Bool.eq_false_iff.mpr hv
          rw [hlin_zero_nonvalue hfalse]
          exact zero_le _
    | succ n ih =>
        rw [linExpectedAt_succ K n e]
        calc
          (∫⁻ e', linExpectedAt n e' K ∂(step e))
              ≤ ∫⁻ e', S e' ∂(step e) := by
                  exact lintegral_mono fun e' => ih e'
          _ ≤ S e := by
            by_cases hv : isValue e = true
            · let v : Val τ := ⟨e, hv⟩
              rw [show step e = Dist.ret e by
                change step (v : TExpr τ) = Dist.ret (v : TExpr τ)
                exact step_value v]
              simp [Dist.ret]
            · have hfalse : isValue e = false := by
                exact Bool.eq_false_iff.mpr hv
              rw [← hS_step e hfalse]

  have hcontext_succ : ∀ (n : ℕ) (e : TExpr τ),
      isValue e = false →
        valueDistAt (n + 1) (C e) A =
          ∫⁻ e', valueDistAt n (C e') A ∂(step e) := by
    intro n e hnon
    unfold valueDistAt
    rw [nstep_succ_bind (C e) n]
    rw [hstep e hnon]
    rw [Measure.comap_apply (Subtype.val : Val σ → TExpr σ)
      Subtype.val_injective (fun _ _ => by trivial) _ hA]
    unfold Dist.bind Dist.ret
    rw [Measure.bind_bind
      ((measurable_from_texpr
        (fun e' : TExpr τ => Measure.dirac (C e'))).aemeasurable)
      ((measurable_from_texpr
        (fun t : TExpr σ => nstep n t)).aemeasurable)]
    rw [Measure.bind_apply
      (by trivial :
        MeasurableSet ((Subtype.val : Val σ → TExpr σ) '' A))]
    · congr
      funext e'
      rw [Measure.dirac_bind]
      · rw [Measure.comap_apply (Subtype.val : Val σ → TExpr σ)
          Subtype.val_injective (fun _ _ => by trivial) _ hA]
      · exact measurable_from_texpr (fun t : TExpr σ => nstep n t)
    · exact (measurable_from_texpr
        (fun e' : TExpr τ => Measure.bind (Measure.dirac (C e'))
          (fun t : TExpr σ => nstep n t))).aemeasurable

  have hS_le_R : ∀ e : TExpr τ, S e ≤ R e := by
    intro e
    unfold S
    rw [show sem (C e) A =
        ⨆ n, valueDistAt n (C e) A by
      unfold sem valueDistAt
      exact measure_iSup_apply_of_monotone
        (fun n : ℕ =>
          Measure.comap (Subtype.val : Val σ → TExpr σ) (nstep n (C e)))
        (value_approximants_mono (C e)) hA]
    apply iSup_le
    intro n
    induction n generalizing e with
    | zero =>
        by_cases hCv : isValue (C e) = true
        · have he : isValue e = true := hvalue e hCv
          let v : Val τ := ⟨e, he⟩
          calc
            valueDistAt 0 (C e) A
                ≤ sem (C e) A := valueDistAt_le_sem 0 (C e) A
            _ = S (v : TExpr τ) := rfl
            _ = R (v : TExpr τ) := (hR_value v).symm
            _ = R e := rfl
        · have hfalse : isValue (C e) = false := by
            exact Bool.eq_false_iff.mpr hCv
          rw [valueDistAt_zero_nonvalue hfalse]
          exact zero_le _
    | succ n ih =>
        by_cases hv : isValue e = true
        · let v : Val τ := ⟨e, hv⟩
          calc
            valueDistAt (n + 1) (C e) A
                ≤ sem (C e) A :=
                  valueDistAt_le_sem (n + 1) (C e) A
            _ = S (v : TExpr τ) := rfl
            _ = R (v : TExpr τ) := (hR_value v).symm
            _ = R e := rfl
        · have hfalse : isValue e = false := by
            exact Bool.eq_false_iff.mpr hv
          rw [hcontext_succ n e hfalse]
          calc
            (∫⁻ e', valueDistAt n (C e') A ∂(step e))
                ≤ ∫⁻ e', R e' ∂(step e) := by
                    exact lintegral_mono fun e' => ih e'
            _ = R e := (hR_step e).symm

  calc
    sem (C e) A = S e := rfl
    _ = R e := le_antisymm (hS_le_R e) (hR_le_S e)
    _ = (Dist.bind (sem e) fun v => sem (C (v : TExpr τ))) A := by
      unfold R K Dist.bind
      rw [Measure.bind_apply hA]
      exact (measurable_from_val
        (fun v : Val τ => sem (C (v : TExpr τ)))).aemeasurable

/-- Big-step decomposition for evaluating the left operand of `<`. -/
theorem sem_lt_left
    (e1 e2 : TExpr (.float .G)) :
    sem (.lt e1 e2 (ModeLE.refl .G) (ModeLE.refl .G))
      =
    Dist.bind (sem e1) fun v1 =>
      sem (.lt (v1 : TExpr (.float .G)) e2 (ModeLE.refl .G) (ModeLE.refl .G)) := by
  let C : TExpr (.float .G) → TExpr .bool :=
    fun e1' => .lt e1' e2 (ModeLE.refl .G) (ModeLE.refl .G)

  change sem (C e1) =
      Dist.bind (sem e1) fun v1 =>
        sem (C (v1 : TExpr (.float .G)))

  apply sem_eval_context C
  · intro e hval
    simp [C, isValue, boolValue?] at hval
  · intro e hnonval
    unfold C
    cases h : floatValue? e with
    | some v =>
        have hv : isValue e = true := by
          cases e <;> simp [floatValue?, isValue] at h ⊢
        rw [hv] at hnonval
        contradiction
    | none =>
        simp [step, h]

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
  let C : TExpr (.float .G) → TExpr .bool :=
    fun e2' => .lt (v1 : TExpr (.float .G)) e2'
      (ModeLE.refl .G) (ModeLE.refl .G)

  have hctx :
      sem (C e2) =
        Dist.bind (sem e2) fun v2 =>
          sem (C (v2 : TExpr (.float .G))) := by
    apply sem_eval_context C
    · intro e hval
      simp [C, isValue, boolValue?] at hval
    · intro e hnonval
      unfold C

      rcases v1 with ⟨v1e, hv1⟩
      cases v1e <;>
        simp [Val, isValue, floatValue?] at hv1

      cases h : floatValue? e with
      | some v =>
          have hv : isValue e = true := by
            cases e <;> simp [floatValue?, isValue] at h ⊢
          rw [hv] at hnonval
          contradiction
      | none =>
          cases e <;> simp [floatValue?, step, Dist.bind, Dist.ret] at h ⊢

  rw [hctx]
  apply Measure.bind_congr_right
  filter_upwards with v2

  have hstep_values :
      step (C (v2 : TExpr (.float .G))) =
        if floatVal v1 < floatVal v2 then
          Dist.ret (.trueE)
        else
          Dist.ret (.falseE) := by
    rcases v1 with ⟨v1e, hv1⟩
    rcases v2 with ⟨v2e, hv2⟩
    cases v1e <;> simp [Val, isValue, floatValue?] at hv1
    cases v2e <;>
      simp [Val, isValue, floatValue?, C, step, floatVal, Dist.ret] at hv2 ⊢

  rw [sem_step_unfold]
  rw [hstep_values]
  by_cases hlt : floatVal v1 < floatVal v2
  · simp [hlt, Dist.ret]
    rw [Measure.dirac_bind
      (measurable_from_texpr (fun e' : TExpr .bool => sem e'))]
    exact sem_value trueVal
  · simp [hlt, Dist.ret]
    rw [Measure.dirac_bind
      (measurable_from_texpr (fun e' : TExpr .bool => sem e'))]
    exact sem_value falseVal

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

  | pair e1 e2 ih1 ih2 =>
      intro K hK
      sorry

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
