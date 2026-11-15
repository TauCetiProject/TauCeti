/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Count
import TauCeti.Probability.Independence.Process.HasIndepIncrements
import TauCeti.Probability.PointProcess.Poisson.Construction
import TauCeti.Probability.RandomMeasure.Cumulative
import Mathlib.MeasureTheory.Function.Floor

/-!
# Recognizing temporal Poisson random measures from their counts

A measurable random measure on the half-line is Poisson if and only if its natural-valued
cumulative count process has independent Poisson increments. The increment parameters are the
masses of the corresponding intervals under a locally finite intensity. The intensity must
give zero mass to `{0}`, but may have atoms at positive times and need not be homogeneous.
Simultaneous occurrences and zero intensity are allowed. No topology on the sample space is
required. A specialization gives the homogeneous parameter `r * (t - s)`.

The count representation is required on one event of full measure for all times. It implies
local finiteness of the realizations. The initial count is zero almost surely, excluding
realization mass at the origin; separately, the intensity must satisfy `Λ {0} = 0`.
The conclusion concerns counts on arbitrary Borel sets, not just temporal intervals.

This supplies the converse to the count-increment properties in
`TauCeti.Probability.PointProcess.Poisson.Count`, allowing random measures represented by
counting processes or arrival times to be recognized as Poisson random measures.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 3 and 7.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- A cumulative count process with independent Poisson increments makes its underlying
random measure Poisson. The cumulative identity includes the origin, while increments count
`(s,t]`. Both `N 0 = 0` almost surely and `Λ {0} = 0` are required: they exclude realization
mass and intensity mass at the origin respectively. The cumulative identity need hold only
almost surely, simultaneously at every time. Atoms at positive times and zero intensity are
allowed; measurability of the given count process is not required. -/
theorem isPoissonRandomMeasure_of_count_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → Measure ℝ≥0} {N : ℝ≥0 → Ω → ℕ} {Λ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure Λ] (hΛ : Λ {0} = 0) (hM : Measurable M)
    (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞))
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0) (hind : HasIndepIncrements N P)
    (hlaw : ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
      (poissonMeasure (Λ (Ioc s t)).toNNReal) P) :
    IsPoissonRandomMeasure P M Λ := by
  -- Recover a measurable version without changing any whole path off a null set.
  let N' : ℝ≥0 → Ω → ℕ := fun t ω ↦ ⌊(M ω (Iic t)).toNNReal⌋₊
  have hN' (t) : Measurable (N' t) :=
    ((Measure.measurable_coe measurableSet_Iic).comp hM).ennreal_toNNReal.nat_floor
  have heq : ∀ᵐ ω ∂P, ∀ t, N' t ω = N t ω := by
    filter_upwards [hcount] with ω hω t using by simp [N', hω t]
  have hcount' : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N' t ω : ℝ≥0∞) := by
    filter_upwards [hcount, heq] with ω hω he t using by rw [he t, hω t]
  have h0' : ∀ᵐ ω ∂P, N' 0 ω = 0 := by
    filter_upwards [h0, heq] with ω hω he using (he 0).trans hω
  have hind' : HasIndepIncrements N' P := by
    intro n t ht
    exact (hind n t ht).congr fun i ↦ heq.mono fun ω hω ↦ by simp [hω]
  have hlaw' s t (hst : s ≤ t) : HasLaw (fun ω ↦ N' t ω - N' s ω)
      (poissonMeasure (Λ (Ioc s t)).toNNReal) P :=
    (hlaw s t hst).congr (heq.mono fun ω hω ↦ by simp [hω])
  have hmono : ∀ᵐ ω ∂P, Monotone (fun t ↦ N' t ω) := by
    filter_upwards [hcount'] with ω hω s t hst
    exact_mod_cast (hω s).symm.trans_le
      ((measure_mono (Iic_subset_Iic.mpr hst)).trans_eq (hω t))
  have hfinite : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) ≠ ∞ := by
    filter_upwards [hcount'] with ω hω t
    rw [hω t]
    exact ENNReal.natCast_ne_top _
  -- Compare the full natural-valued path law with the constructed Poisson random measure.
  let Q := Λ.poissonLaw
  have hQ : IsPoissonRandomMeasure Q id Λ := Λ.isPoissonRandomMeasure_poissonLaw
  let C : ℝ≥0 → Measure ℝ≥0 → ℕ := fun t μ ↦ ⌊(μ (Ioc 0 t)).toNNReal⌋₊
  have hCcount : ∀ᵐ μ ∂Q, ∀ t, μ (Iic t) = (C t μ : ℝ≥0∞) :=
    hQ.ae_forall_measure_Iic_eq_natCast_nat_count hΛ
  have hQfinite : ∀ᵐ μ ∂Q, ∀ t, μ (Iic t) ≠ ∞ := by
    filter_upwards [hCcount] with μ hμ t
    rw [hμ t]
    exact ENNReal.natCast_ne_top _
  have hpaths := hind'.identDistrib_nat hQ.hasIndepIncrements_nat_count
    hN' hQ.measurable_nat_count h0' (by simp) hmono hQ.ae_monotone_nat_count
    (fun s t hst ↦ (hlaw' s t hst).identDistrib (hQ.hasLaw_nat_count_sub hst))
  -- Cumulative evaluations determine the law of a locally finite random measure.
  have hcum := hpaths.comp (measurable_pi_iff.mpr fun t ↦
    (measurable_of_countable (Nat.cast : ℕ → ℝ≥0∞)).comp (measurable_pi_apply t))
  have heqM : (fun ω t ↦ (N' t ω : ℝ≥0∞)) =ᵐ[P] (fun ω t ↦ M ω (Iic t)) :=
    hcount'.mono fun _ hω ↦ funext fun t ↦ (hω t).symm
  have heqQ : (fun μ t ↦ (C t μ : ℝ≥0∞)) =ᵐ[Q] (fun μ t ↦ μ (Iic t)) :=
    hCcount.mono fun _ hμ ↦ funext fun t ↦ (hμ t).symm
  have hcum' := (IdentDistrib.of_ae_eq hcum.aemeasurable_fst heqM).symm.trans
    (hcum.trans (IdentDistrib.of_ae_eq hcum.aemeasurable_snd heqQ))
  exact hQ.of_identDistrib hM
    ((identDistrib_measure_iff_Iic hM.aemeasurable measurable_id.aemeasurable
      hfinite hQfinite).mpr hcum').symm

/-- For a cumulative natural-valued representation, the Poisson property is equivalent to
starting at zero almost surely and having independent Poisson increments. The intensity is
locally finite and has no mass at the origin; atoms at positive times are allowed. -/
theorem isPoissonRandomMeasure_iff_count_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → Measure ℝ≥0} {N : ℝ≥0 → Ω → ℕ} {Λ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure Λ] (hΛ : Λ {0} = 0) (hM : Measurable M)
    (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞)) :
    IsPoissonRandomMeasure P M Λ ↔ (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
        (poissonMeasure (Λ (Ioc s t)).toNNReal) P := by
  refine ⟨fun h ↦ ?_, fun ⟨h0, hind, hlaw⟩ ↦
    isPoissonRandomMeasure_of_count_increments hΛ hM hcount h0 hind hlaw⟩
  have heq : ∀ᵐ ω ∂P, ∀ t, ⌊(M ω (Ioc 0 t)).toNNReal⌋₊ = N t ω := by
    filter_upwards [h.ae_forall_measure_Iic_eq_natCast_nat_count hΛ, hcount] with ω hc hn t
    exact_mod_cast (hc t).symm.trans (hn t)
  refine ⟨heq.mono (fun ω hω ↦ by simpa using (hω 0).symm), ?_, ?_⟩
  · intro n t ht
    exact (h.hasIndepIncrements_nat_count n t ht).congr fun i ↦
      heq.mono fun ω hω ↦ by simp [hω]
  · intro s t hst
    exact (h.hasLaw_nat_count_sub hst).congr (heq.mono fun ω hω ↦ by simp [hω])

/-- Homogeneous temporal Poisson random measures are characterized by a zero initial count
almost surely and independent increments with parameter rate times elapsed time. This includes
rate zero and equal increment endpoints. -/
theorem isPoissonRandomMeasure_smul_nnvolume_iff_count_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → Measure ℝ≥0} {N : ℝ≥0 → Ω → ℕ} {r : ℝ≥0}
    (hM : Measurable M)
    (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞)) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
        (poissonMeasure (r * (t - s))) P := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  simpa only [smul_nnvolume_Ioc, ENNReal.toNNReal_coe] using
    isPoissonRandomMeasure_iff_count_increments (Λ := (r : ℝ≥0∞) • nnvolume)
      (by simp) hM hcount

end TauCeti.Probability
