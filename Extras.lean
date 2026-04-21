/-- A sub-Markov kernel presented as a plain function `α → Measure β`. -/
-- We need sub- Markov kernels because we have diverge.
def IsSubMarkovKernel {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (K : α → Measure β) : Prop :=
  Measurable K ∧ ∀ a, IsSubProbabilityMeasure (K a)


/-- `ret ∘ f` is a sub-Markov kernel. -/
lemma ret_is_subMarkovKernel
    {α β : Type}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β}
    (hf : Measurable f) :
    IsSubMarkovKernel (fun a : α => (Dist.ret (f a) : Dist β)) := by
  refine ⟨
    (by
      simpa [Dist.ret_is_dirac] using
        (MeasureTheory.Measure.measurable_dirac.comp hf)),
    (by
      intro a
      simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
  ⟩

/-- A constant measure-valued map is a sub-Markov kernel if the measure is subprobability. -/
lemma const_is_subMarkovKernel
    {α β : Type}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure β}
    (hμ : IsSubProbabilityMeasure μ) :
    IsSubMarkovKernel (fun _ : α => μ) := by
  exact ⟨measurable_const, fun _ => hμ⟩

-- General bind closure for sub-Markov kernels.
lemma bind_preserves_subMarkovKernel
    {α β γ : Type}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : α → Measure β}
    [∀ a, SFinite (μ a)]
    {κ : α → β → Measure γ}
    (hμ : IsSubMarkovKernel μ)
    (hκ : IsSubMarkovKernel (Function.uncurry κ)) :
    IsSubMarkovKernel
      (fun a : α => (Dist.bind (μ a) (κ a) : Dist γ)) := by
  rcases hμ with ⟨hμ_meas, hμ_sub⟩
  rcases hκ with ⟨hκ_meas, hκ_sub'⟩
  have hκ_sub : ∀ a b, IsSubProbabilityMeasure (κ a b) := fun a b => hκ_sub' (a, b)
  let μK : Kernel α β := ⟨μ, hμ_meas⟩
  let κK : Kernel (α × β) γ := ⟨Function.uncurry κ, hκ_meas⟩
  have hμK_fin : IsFiniteKernel μK := by
    refine ⟨⟨1, by simp, by intro a; exact hμ_sub a⟩⟩
  letI : IsFiniteKernel μK := hμK_fin
  letI : IsSFiniteKernel μK := inferInstance
  have hbind_meas :
      Measurable (fun a : α => (Dist.bind (μ a) (κ a) : Dist γ)) := by
    let K : Kernel α γ := κK ∘ₖ Kernel.prod Kernel.id μK
    have hEq :
        (fun a : α => (Dist.bind (μ a) (κ a) : Dist γ)) =
          (fun a : α => (K a : Measure γ)) := by
      funext a
      ext s hs
      calc
        (Dist.bind (μ a) (κ a)) s
            = ∫⁻ b, κ a b s ∂(μ a) := by
              rw [Dist.bind_is_measure_bind, Measure.bind_apply hs]
              exact (Measurable.of_uncurry_left (f := κ) hκ_meas (x := a)).aemeasurable
        _ = ((κK ∘ₖ Kernel.prod Kernel.id μK) a) s := by
              symm
              rw [Kernel.comp_apply' (η := κK)
                (κ := Kernel.prod Kernel.id μK) (a := a) (hs := hs)]
              rw [Kernel.lintegral_id_prod (κ := μK) (a := a)
                (f := fun p : α × β => κK p s) (hf := Kernel.measurable_coe κK hs)]
              simp [μK, κK, Function.uncurry]
        _ = K a s := rfl
    rw [hEq]
    exact Kernel.measurable K
  refine ⟨hbind_meas, by
    intro a
    unfold IsSubProbabilityMeasure
    change (Dist.bind (μ a) (κ a) Set.univ ≤ 1)
    rw [Dist.bind_is_measure_bind, Measure.bind_apply MeasurableSet.univ]
    · calc
        ∫⁻ b, κ a b Set.univ ∂(μ a)
            ≤ ∫⁻ b, 1 ∂(μ a) := lintegral_mono (fun b => hκ_sub a b)
        _ = (μ a) Set.univ := by simp
        _ ≤ 1 := hμ_sub a
    · exact (Measurable.of_uncurry_left (f := κ) hκ_meas (x := a)).aemeasurable
  ⟩

/-- Specialization of bind closure when the RHS is `ret (f a b)`. -/
lemma bind_ret_preserves_subMarkovKernel
    {α β γ : Type}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : α → Measure β}
    [∀ a, SFinite (μ a)]
    (hμ : IsSubMarkovKernel μ)
    {f : α → β → γ}
    (hf : Measurable (Function.uncurry f)) :
    IsSubMarkovKernel
      (fun a : α => (Dist.bind (μ a) (fun b => Dist.ret (f a b)) : Dist γ)) := by
  refine bind_preserves_subMarkovKernel
    (μ := μ)
    (κ := fun a b => Dist.ret (f a b))
    hμ
    (by
      refine ⟨
        (by
          simpa [Function.uncurry, Dist.ret_is_dirac] using
            (MeasureTheory.Measure.measurable_dirac.comp hf)),
        (by
          intro p
          rcases p with ⟨a, b⟩
          simp [IsSubProbabilityMeasure, Dist.ret_is_dirac])
      ⟩)


-- If K : Expr → Measure Expr is already a sub-Markov kernel for stepping a subexpression, then plugging that stepped subexpression back into a larger expression form still gives a sub-Markov kernel.
lemma let_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (x : String) (e2 : Expr) :
    IsSubMarkovKernel
      (fun e1 : Expr =>
        if isValue e1 then
          (Dist.ret (subst x e1 e2) : Dist Expr)
        else
          Dist.bind (K e1) (fun g => Dist.ret (Expr.letE x g e2))) := by
  sorry

lemma if_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (t f : Expr) :
    IsSubMarkovKernel
      (fun c : Expr =>
        match c with
        | .trueE  => Dist.ret t
        | .falseE => Dist.ret f
        | _       => Dist.bind (K c) (fun g => Dist.ret (Expr.ifE g t f))) := by
  classical
  rcases hK with ⟨hK_meas, hK_sub⟩
  letI : ∀ a : Expr, IsFiniteMeasure (K a) := fun a =>
    ⟨lt_of_le_of_lt (hK_sub a) (by simp)⟩
  letI : ∀ a : Expr, SFinite (K a) := fun a => inferInstance
  have hif_uncurry :
      Measurable (Function.uncurry (fun (_ : Expr) (g : Expr) => Expr.ifE g t f)) := by
    simpa [Function.uncurry] using (if_wrap_measurable t f).comp measurable_snd
  have hbind :
      IsSubMarkovKernel
        (fun c : Expr =>
          (Dist.bind (K c) (fun g => Dist.ret (Expr.ifE g t f)) : Dist Expr)) :=
    bind_ret_preserves_subMarkovKernel
      (μ := K) ⟨hK_meas, hK_sub⟩ (f := fun (_ : Expr) (g : Expr) => Expr.ifE g t f) hif_uncurry
  rcases hbind with ⟨hbind_meas, hbind_sub⟩
  have hEq :
      (fun c : Expr =>
        match c with
        | .trueE  => Dist.ret t
        | .falseE => Dist.ret f
        | _       => Dist.bind (K c) (fun g => Dist.ret (Expr.ifE g t f)))
      =
      (fun c : Expr =>
        if c = Expr.trueE then (Dist.ret t : Dist Expr)
        else if c = Expr.falseE then (Dist.ret f : Dist Expr)
        else (Dist.bind (K c) (fun g => Dist.ret (Expr.ifE g t f)) : Dist Expr)) := by
    funext c
    cases c <;> simp
  refine ⟨?_, ?_⟩
  · rw [hEq]
    have htrueSet : MeasurableSet {c : Expr | c = Expr.trueE} := by
      simpa [Set.setOf_eq_eq_singleton] using
        (measurableSet_singleton (a := Expr.trueE))
    have hfalseSet : MeasurableSet {c : Expr | c = Expr.falseE} := by
      simpa [Set.setOf_eq_eq_singleton] using
        (measurableSet_singleton (a := Expr.falseE))
    refine Measurable.ite htrueSet measurable_const ?_
    exact Measurable.ite hfalseSet measurable_const hbind_meas
  · intro c
    rw [hEq]
    by_cases htrue : c = Expr.trueE
    · simp [htrue, IsSubProbabilityMeasure, Dist.ret_is_dirac]
    · by_cases hfalse : c = Expr.falseE
      · simp [hfalse, IsSubProbabilityMeasure, Dist.ret_is_dirac]
      · simpa [htrue, hfalse] using hbind_sub c

lemma lt_left_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (e2 : Expr) :
    IsSubMarkovKernel
      (fun e1 : Expr =>
        Dist.bind (K e1) (fun g => Dist.ret (Expr.lt g e2))) := by
  rcases hK with ⟨hK_meas, hK_sub⟩
  letI : ∀ a : Expr, IsFiniteMeasure (K a) := fun a =>
    ⟨lt_of_le_of_lt (hK_sub a) (by simp)⟩
  letI : ∀ a : Expr, SFinite (K a) := fun a => inferInstance
  exact bind_ret_preserves_subMarkovKernel
    (μ := K)
    ⟨hK_meas, hK_sub⟩
    (f := fun (_ : Expr) (g : Expr) => Expr.lt g e2)
    (by
      simpa [Function.uncurry] using (lt_left_wrap_measurable e2).comp measurable_snd)

lemma lt_right_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (v1 : ℝ) :
    IsSubMarkovKernel
      (fun e2 : Expr =>
        Dist.bind (K e2) (fun g => Dist.ret (Expr.lt (.const v1) g))) := by
  rcases hK with ⟨hK_meas, hK_sub⟩
  letI : ∀ a : Expr, IsFiniteMeasure (K a) := fun a =>
    ⟨lt_of_le_of_lt (hK_sub a) (by simp)⟩
  letI : ∀ a : Expr, SFinite (K a) := fun a => inferInstance
  exact bind_ret_preserves_subMarkovKernel
    (μ := K)
    ⟨hK_meas, hK_sub⟩
    (f := fun (_ : Expr) (g : Expr) => Expr.lt (.const v1) g)
    (by
      simpa [Function.uncurry] using (lt_right_wrap_measurable v1).comp measurable_snd)

lemma uniform_left_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (e2 : Expr) :
    IsSubMarkovKernel
      (fun e1 : Expr =>
        Dist.bind (K e1) (fun g => Dist.ret (Expr.uniform g e2))) := by
  rcases hK with ⟨hK_meas, hK_sub⟩
  letI : ∀ a : Expr, IsFiniteMeasure (K a) := fun a =>
    ⟨lt_of_le_of_lt (hK_sub a) (by simp)⟩
  letI : ∀ a : Expr, SFinite (K a) := fun a => inferInstance
  exact bind_ret_preserves_subMarkovKernel
    (μ := K)
    ⟨hK_meas, hK_sub⟩
    (f := fun (_ : Expr) (g : Expr) => Expr.uniform g e2)
    (by
      simpa [Function.uncurry] using (uniform_left_wrap_measurable e2).comp measurable_snd)

lemma uniform_right_clause_kernel
    {K : Expr → Measure Expr}
    (hK : IsSubMarkovKernel K)
    (v1 : ℝ) :
    IsSubMarkovKernel
      (fun e2 : Expr =>
        Dist.bind (K e2) (fun g => Dist.ret (Expr.uniform (.const v1) g))) := by
  rcases hK with ⟨hK_meas, hK_sub⟩
  letI : ∀ a : Expr, IsFiniteMeasure (K a) := fun a =>
    ⟨lt_of_le_of_lt (hK_sub a) (by simp)⟩
  letI : ∀ a : Expr, SFinite (K a) := fun a => inferInstance
  exact bind_ret_preserves_subMarkovKernel
    (μ := K)
    ⟨hK_meas, hK_sub⟩
    (f := fun (_ : Expr) (g : Expr) => Expr.uniform (.const v1) g)
    (by
      simpa [Function.uncurry] using (uniform_right_wrap_measurable v1).comp measurable_snd)















-- ---------------------------------------------------------------------------
-- 1. Subprobability measure
-- ---------------------------------------------------------------------------


-- Dirac.ret e is a subprobability measure.
lemma ret_is_subprob_measure {α : Type} [MeasurableSpace α] (a : α) :
    IsSubProbabilityMeasure (Dist.ret a) := by
  unfold IsSubProbabilityMeasure
  simp [Dist.ret_is_dirac]

-- Bind preserves subprobability measures.
lemma bind_is_subprob_measure {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (k : α → Measure β)
    (hμ : IsSubProbabilityMeasure μ)
    (hk : ∀ x, IsSubProbabilityMeasure (k x))
    (hkm : Measurable k) :
    IsSubProbabilityMeasure (Dist.bind μ k) := by
  unfold IsSubProbabilityMeasure at hμ hk ⊢
  rw [Dist.bind_is_measure_bind, Measure.bind_apply MeasurableSet.univ hkm.aemeasurable]
  exact (lintegral_mono (fun a => hk a)).trans (by simp [hμ])

lemma step_is_subprob_measure {τ : Ty} (e : ExprsOfType τ) :
    IsSubProbabilityMeasure (step e) := by
  classical
  have step_untyped_subprob : ∀ e' : Expr, IsSubProbabilityMeasure (Untyped.step e') := by
    intro e'
    induction e' with
    | diverge =>
        unfold IsSubProbabilityMeasure
        simp [Untyped.step]
    | const _ | finconst _ _ | trueE | falseE | var _ =>
        simp only [Untyped.step]
        exact ret_is_subprob_measure _
    | discrete ps =>
        simp only [Untyped.step]
        apply bind_is_subprob_measure
        · unfold IsSubProbabilityMeasure
          simpa [Dist.ret_is_dirac, ps.2] using (le_rfl : (1 : ENNReal) ≤ 1)
        · intro i; exact ret_is_subprob_measure _
        · simpa [Dist.ret_is_dirac] using
            MeasureTheory.Measure.measurable_dirac.comp (finconst_wrap_measurable _)
    | letE x e1 e2 ih1 _ =>
        simp only [Untyped.step]
        split_ifs
        · exact ret_is_subprob_measure _
        · exact bind_is_subprob_measure _ _ ih1
            (fun _ => ret_is_subprob_measure _)
            (by simpa [Dist.ret_is_dirac] using
              MeasureTheory.Measure.measurable_dirac.comp (let_wrap_measurable x e2))
    | lt e1 e2 ih1 ih2 =>
        simp only [Untyped.step]
        split
        · split
          · exact ret_is_subprob_measure _
          · exact ret_is_subprob_measure _
        · exact bind_is_subprob_measure _ _ ih2
            (fun _ => ret_is_subprob_measure _)
            (by simpa [Dist.ret_is_dirac] using
              MeasureTheory.Measure.measurable_dirac.comp (lt_right_wrap_measurable _))
        · exact bind_is_subprob_measure _ _ ih1
            (fun _ => ret_is_subprob_measure _)
            (by simpa [Dist.ret_is_dirac] using
              MeasureTheory.Measure.measurable_dirac.comp (lt_left_wrap_measurable e2))
    | ifE e1 e2 e3 ih1 _ _ =>
        simp only [Untyped.step]
        split
        · exact ret_is_subprob_measure _
        · exact ret_is_subprob_measure _
        · exact bind_is_subprob_measure _ _ ih1
            (fun _ => ret_is_subprob_measure _)
            (by simpa [Dist.ret_is_dirac] using
              MeasureTheory.Measure.measurable_dirac.comp (if_wrap_measurable e2 e3))
    | uniform e1 e2 ih1 ih2 =>
        simp only [Untyped.step]
        split
        · split
          · apply bind_is_subprob_measure
            · unfold IsSubProbabilityMeasure
              simpa using prob_le_one (μ := ProbabilityTheory.cond volume (Set.Icc _ _)) (s := Set.univ)
            · intro _; exact ret_is_subprob_measure _
            · simpa [Dist.ret_is_dirac] using
                MeasureTheory.Measure.measurable_dirac.comp const_wrap_measurable
          · exact ret_is_subprob_measure _
        · exact bind_is_subprob_measure _ _ ih2
            (fun _ => ret_is_subprob_measure _)
            (by simpa [Dist.ret_is_dirac] using
              MeasureTheory.Measure.measurable_dirac.comp (uniform_right_wrap_measurable _))
        · exact bind_is_subprob_measure _ _ ih1
            (fun _ => ret_is_subprob_measure _)
            (by simpa [Dist.ret_is_dirac] using
              MeasureTheory.Measure.measurable_dirac.comp (uniform_left_wrap_measurable e2))
  have hUntyped := step_untyped_subprob e.1
  unfold step IsSubProbabilityMeasure at hUntyped ⊢
  let f : Expr → ExprsOfType τ :=
    fun e' => if h : HasType Ctx.empty e' τ then (⟨e', h⟩ : ExprsOfType τ) else e
  by_cases hf : AEMeasurable
      f
      (Untyped.step e.1)
  · calc
      (Measure.map f (Untyped.step e.1)) Set.univ
          = (Untyped.step e.1) Set.univ := by
            rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ, Set.preimage_univ]
      _ ≤ 1 := hUntyped
  · rw [Measure.map_of_not_aemeasurable hf]
    change (0 : ENNReal) ≤ 1
    exact zero_le (1 : ENNReal)

-- ---------------------------------------------------------------------------
-- 2. Measurability
-- ---------------------------------------------------------------------------
-- Dist.ret ∘ f is measurable.
lemma ret_comp_measurable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) :
    Measurable (fun e : α => (Dist.ret (f e) : Dist β)) := by
  simpa [Dist.ret_is_dirac] using
    (MeasureTheory.Measure.measurable_dirac.comp hf)


-- Substitution is measurable
lemma subst_is_measurable (x : String) (body : Expr) :
    Measurable (fun e : Expr => Dist.ret (subst x e body)) := by sorry

-- Bind preserves measurability.
lemma bind_is_measurable {α β γ : Type}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α → Measure β} {k : β → Measure γ}
    (hf : Measurable f) (hk : Measurable k) :
    Measurable (fun x : α => (Dist.bind (f x) k : Dist γ)) := by
  simp only [Dist.bind]
  exact (MeasureTheory.Measure.measurable_bind' hk).comp hf

-- Bind with a fixed source measure and a dependent `ret` kernel is measurable.
lemma bind_dep_dirac_is_measurable {α β γ : Type}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : α → Measure β}
    [∀ x, SFinite (μ x)]
    (hμ : Measurable μ)
    {f : α → β → γ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun x : α => (Dist.bind (μ x) (fun y => Dist.ret (f x y)) : Dist γ)) := by
  -- same proof pattern as your fixed-μ lemma, but now with `μ x` inside the lintegral
  sorry

lemma let_wrap_dep_measurable {α}
    [MeasurableSpace α] {e₂ : α → Expr}
    (he₂ : Measurable e₂) :
    Measurable (fun p : α × Expr => Expr.letE x p.2 (e₂ p.1)) := by sorry

lemma if_wrap_dep_measurable {α}
    [MeasurableSpace α] {t f : α → Expr}
    (ht : Measurable t) (hf : Measurable f) :
    Measurable (fun p : α × Expr => Expr.ifE p.2 (t p.1) (f p.1)) := by sorry

lemma lt_wrap_dep_measurable {α}
    [MeasurableSpace α] {e₂ : α → Expr}
    (he₂ : Measurable e₂) :
    Measurable (fun p : α × Expr => Expr.lt p.2 (e₂ p.1)) := by sorry

lemma uniform_wrap_dep_measurable {α}
    [MeasurableSpace α] {e₂ : α → Expr}
    (he₂ : Measurable e₂) :
    Measurable (fun p : α × Expr => Expr.uniform p.2 (e₂ p.1)) := by sorry

lemma step_untyped_measurable :
    Measurable (fun e : Expr => Untyped.step e) := by sorry




-- noncomputable def stepKernel (τ : Ty) : Kernel (ExprsOfType τ) (ExprsOfType τ) where
--   toFun    := step
--   measurable' := step_is_measurable τ

-- /-- For typed inputs, `stepKernel` is subprobability. -/
-- theorem stepKernel_subprob_on_welltyped {τ : Ty} (e : ExprsOfType τ) :
--     IsSubProbabilityMeasure (stepKernel τ e) := by
--   simpa [stepKernel] using step_is_subprob_measure e
