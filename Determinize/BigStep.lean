import Determinize.SmallStep

namespace Determinize

open MeasureTheory
open Filter
open scoped ENNReal Topology

namespace TExpr

/-- The `n`-step semantics obtained by iterating small-step `n` times. -/
noncomputable def nstep {τ : Ty} : Nat → TExpr τ → Dist (TExpr τ)
  | 0, e =>
      Dist.ret e
  | n + 1, e =>
      Dist.bind (nstep n e) (fun e' => step e')

/-- Value terms of a given type. -/
def Val (τ : Ty) : Set (TExpr τ) :=
  {e | isValue e = true}

/-- The big-step semantics, defined over value terms. -/
noncomputable def sem {τ : Ty} (e : TExpr τ) : Dist (Val τ) :=
  ⨆ n, (nstep n e).comap (Subtype.val : Val τ → TExpr τ)

/-- The pointwise big-step value of an event `A`. -/
noncomputable def semAt {τ : Ty} (e : TExpr τ) (A : Set (Val τ)) : ℝ≥0∞ :=
  ⨆ n, ((nstep n e).comap (Subtype.val : Val τ → TExpr τ)) A

/-- Monotone accummulation of mass:
⟨e : τ⟩_{n}(A) ≤ ⟨e : τ⟩_{n+1}(A) for measurable A ⊆ Val τ -/
lemma nstep_value_succ_le {τ : Ty} (e : TExpr τ) {A : Set (Val τ)}
    (hAm : MeasurableSet A) (n : Nat) :
    ((nstep n e).comap (Subtype.val : Val τ → TExpr τ)) A ≤
      ((nstep (n + 1) e).comap (Subtype.val : Val τ → TExpr τ)) A := by
  simp only [Measure.comap_apply (Subtype.val : Val τ → TExpr τ) Subtype.val_injective
    (fun _ _ => by trivial) _ hAm, nstep]
  change nstep n e ((Subtype.val : Val τ → TExpr τ) '' A) ≤
    (Measure.bind (nstep n e) (fun e' => step e')) ((Subtype.val : Val τ → TExpr τ) '' A)
  rw [Measure.bind_apply (by trivial : MeasurableSet ((Subtype.val : Val τ → TExpr τ) '' A))]
  · rw [← lintegral_indicator_one (by trivial : MeasurableSet ((Subtype.val : Val τ → TExpr τ) '' A))]
    refine lintegral_mono fun e' => ?_
    by_cases he' : e' ∈ (Subtype.val : Val τ → TExpr τ) '' A
    · rcases he' with ⟨v, _hvA, rfl⟩
      have hstep : step (v : TExpr τ) = Dist.ret (v : TExpr τ) := by
        rcases v with ⟨t, hv⟩
        cases τ <;> cases t <;>
          simp [Val, isValue, unitValue?, boolValue?, floatValue?, step] at hv ⊢
      rw [hstep]
      simp [Measure.dirac_apply' _ (by trivial : MeasurableSet ((Subtype.val : Val τ → TExpr τ) '' A)),
        _hvA]
    · simp [Set.indicator_of_notMem he']
  · exact (by fun_prop : Measurable (step : TExpr τ → Dist (TExpr τ))).aemeasurable

/-- The pointwise big-step limit exists for every measurable event in `Val τ`:
lim_{n → ∞} ⟨e : τ⟩_{n}(A) exists whenever measurable A ⊆ Val τ -/

-- TODO: Change L. Should be ≤ 1.
lemma bigstep_exists {τ : Ty} (e : TExpr τ) {A : Set (Val τ)}
    (hAm : MeasurableSet A) :
    ∃ L : ℝ≥0∞,
      Tendsto
        (fun n : Nat => ((nstep n e).comap (Subtype.val : Val τ → TExpr τ)) A)
        atTop
        (𝓝 L) := by
  have hmono :
      Monotone
        (fun n : Nat => ((nstep n e).comap (Subtype.val : Val τ → TExpr τ)) A) :=
    monotone_nat_of_le_succ (nstep_value_succ_le e hAm)
  exact ⟨semAt e A, by
    simpa [semAt] using tendsto_atTop_iSup hmono⟩

end TExpr

end Determinize
