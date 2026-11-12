/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Completion
public import TauCeti.Probability.Martingale.CountableStopping
public import TauCeti.Probability.Martingale.Local.Dominated
public import TauCeti.Probability.Process.CountableLevelLocalizer

/-!
# Descent of continuous local martingales to smaller filtrations

An almost surely continuous process adapted to a smaller filtration remains a native local
martingale there if it is a native local martingale in a larger filtration on the same measure
space. Neither filtration needs completeness or right continuity. The conclusion supplies
actual stopping times of the smaller filtration, not just martingale versions of stopped paths.
This allows constructions made with extra information to be used on the original filtration.

Countable-range level localizers are constructed from the process in the smaller filtration.
Initial-value cutoffs make their native stopped stages bounded, without any initial moment
assumption. Countable-range stopping preserves native local martingales; boundedness then
makes these stages true martingales in the larger filtration, and their adaptedness gives the
smaller-filtration martingale identities. A second theorem allows the larger filtration to
live on the completed ambient space, using `ProbabilityTheory.Locally.martingale_completion_iff`
to transfer the resulting raw localizers back unchanged.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ 𝒢 : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → E}

/-- An almost surely continuous process adapted to a smaller filtration is a native local
martingale there whenever it is one in a larger filtration on the same finite measure space.
No usual conditions or integrability of the initial value are assumed. -/
theorem StronglyAdapted.locally_martingale_of_le (hX : StronglyAdapted ℱ X)
    (hc : ∀ᵐ ω ∂P, Continuous (X · ω)) (hFG : ∀ t, ℱ t ≤ 𝒢 t)
    (hlocal : Locally (fun Y ↦ Martingale Y 𝒢 P) 𝒢 X P) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P := by
  classical
  -- Construct countable-range level localizers using only the smaller filtration.
  obtain ⟨η, hη, hcount, hmono, hbound⟩ :=
    hX.exists_isLocalizingSequence_countable_range_level hc
  -- Cutting off at time zero controls the full stages, even for nonintegrable initial data.
  let A (n : ℕ) : Set Ω := {ω | ‖X 0 ω‖ ≤ (n : ℝ)}
  have hA (n : ℕ) : MeasurableSet[ℱ 0] (A n) :=
    (hX 0).norm.measurable measurableSet_Iic
  let ρ (n : ℕ) : Ω → WithTop ℝ≥0 := (A n).piecewise (η n) (fun _ ↦ 0)
  have hρ (n : ℕ) : IsStoppingTime ℱ (ρ n) :=
    (hη.isStoppingTime n).piecewise_of_le (isStoppingTime_const ℱ 0)
      (fun _ ↦ bot_le) (fun _ ↦ le_rfl) (hA n)
  have hρcount (n : ℕ) : (range (ρ n)).Countable := by
    apply ((hcount n).insert 0).mono
    rintro _ ⟨ω, rfl⟩
    by_cases hω : ω ∈ A n <;> simp [ρ, hω]
  have hρmono (ω : Ω) : Monotone (ρ · ω) := by
    intro i j hij
    by_cases hi : ω ∈ A i
    · have hj : ω ∈ A j :=
        (hi : ‖X 0 ω‖ ≤ (i : ℝ)).trans (Nat.cast_le.mpr hij : (i : ℝ) ≤ (j : ℝ))
      simpa only [ρ, piecewise_eq_of_mem _ _ _ hi, piecewise_eq_of_mem _ _ _ hj] using
        hmono ω hij
    · simp only [ρ, piecewise_eq_of_notMem _ _ _ hi]
      exact bot_le
  have hρlim : ∀ᵐ ω ∂P, Tendsto (ρ · ω) atTop (𝓝 ⊤) := by
    filter_upwards [hη.tendsto_top] with ω hω
    obtain ⟨N, hN⟩ := exists_nat_ge ‖X 0 ω‖
    apply hω.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (piecewise_eq_of_mem _ _ _ (hN.trans (Nat.cast_le.mpr hn))).symm
  -- Countable ranges give literal raw adaptation; centered bounds give bounded full stages.
  let Z (n : ℕ) := MeasureTheory.stoppedProcess
    (fun t ↦ {ω | 0 < ρ n ω}.indicator (X t)) (ρ n)
  have hZF (n : ℕ) : StronglyAdapted ℱ (Z n) := by
    simp only [Z, stoppedProcess_indicator_comm']
    intro t
    exact ((hX.stoppedProcess_of_countable_range (hρ n) (hρcount n)) t).indicator
      (ℱ.mono bot_le _ ((hρ n).measurableSet_gt 0))
  have hZbound (n : ℕ) : ∀ᵐ ω ∂P, ∀ t, ‖Z n t ω‖ ≤ 2 * (n : ℝ) + 1 := by
    filter_upwards [hbound] with ω hω t
    simp only [Z, stoppedProcess_indicator_comm']
    by_cases hn : ω ∈ A n
    · rw [Set.indicator_apply]
      split_ifs with hpos
      · have heq : ρ n ω = η n ω := piecewise_eq_of_mem _ _ _ hn
        have hs : MeasureTheory.stoppedProcess X (ρ n) t ω =
            MeasureTheory.stoppedProcess X (η n) t ω := by
          simp only [MeasureTheory.stoppedProcess, heq]
        rw [hs]
        calc
          ‖MeasureTheory.stoppedProcess X (η n) t ω‖ ≤
              ‖MeasureTheory.stoppedProcess X (η n) t ω - X 0 ω‖ + ‖X 0 ω‖ :=
                norm_le_norm_sub_add _ _
          _ ≤ ((n : ℝ) + 1) + (n : ℝ) := add_le_add ((hω n).2 t) hn
          _ = 2 * (n : ℝ) + 1 := by ring
      · simp only [norm_zero]
        positivity
    · have heq : ρ n ω = 0 := piecewise_eq_of_notMem _ _ _ hn
      rw [Set.indicator_of_notMem (by
        simp only [mem_ofPred_eq, heq, lt_self_iff_false, not_false_eq_true])]
      simp only [norm_zero]
      positivity
  refine ⟨ρ, ⟨⟨hρ, hρlim⟩, Eventually.of_forall hρmono⟩, fun n ↦ ?_⟩
  -- Upgrade in the larger filtration, then restrict the martingale test events.
  have hρG : IsStoppingTime 𝒢 (ρ n) := fun t ↦ hFG t _ (hρ n t)
  have hZG : StronglyAdapted 𝒢 (Z n) := fun t ↦ (hZF n t).mono (hFG t)
  have hm : Martingale (Z n) 𝒢 P :=
    hZG.martingale_of_locally_martingale_of_bounded
      (hlocal.martingale_stoppedProcess_indicator_of_countable_range hρG (hρcount n))
      (fun _ ↦ ⟨2 * (n : ℝ) + 1, (hZbound n).mono fun ω hω t _ ↦ hω t⟩)
  exact ((hZF n).martingale_iff_setIntegral_eq (fun t ↦ hm.integrable t)).2
    (fun s t hst B hB ↦ hm.setIntegral_eq hst (hFG s _ hB))

/-- Descent from a larger filtration on the completed ambient space to the original raw
filtration and measure. The resulting localizing times are raw stopping times; neither
adaptation nor localizers are inferred merely from equality modulo completion. -/
theorem StronglyAdapted.locally_martingale_of_le_completion (hX : StronglyAdapted ℱ X)
    (hc : ∀ᵐ ω ∂P, Continuous (X · ω))
    {𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P))}
    (hFG : ∀ t, ℱ t ≤ 𝒢 t)
    (hlocal : @Locally ℝ≥0 (NullMeasurableSpace Ω P) E _ _ _ _ _ _
      (fun Y ↦ Martingale Y 𝒢 P.completion) 𝒢 X P.completion) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P := by
  have : @IsFiniteMeasure (NullMeasurableSpace Ω P) _ P.completion :=
    ⟨lt_of_eq_of_lt (Measure.completion_apply P univ) (measure_lt_top P univ)⟩
  apply ProbabilityTheory.Locally.martingale_completion_iff.mp
  exact @StronglyAdapted.locally_martingale_of_le (NullMeasurableSpace Ω P) E _
    P.completion this _ _ _ (ℱ.monoAmbient le_eventuallyMeasurableSpace) 𝒢 X
    ((stronglyAdapted_monoAmbient_iff _).mpr hX)
    (hc.filter_mono P.ae_completion.le) hFG hlocal

end MeasureTheory
