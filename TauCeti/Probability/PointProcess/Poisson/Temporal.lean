/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Count
import TauCeti.Probability.Independence.Process.HasIndepIncrements
import TauCeti.Probability.PointProcess.Poisson.Construction
import TauCeti.Probability.PointProcess.Poisson.LaplaceCharacterization
import TauCeti.Probability.RandomMeasure.Cumulative

/-!
# Recognizing temporal Poisson random measures from their counts

A measurable random measure on the half-line is Poisson if its cumulative masses are
represented by a natural-valued process starting at zero with independent Poisson increments.
The increment parameters are the masses of the corresponding intervals under a locally finite
intensity. The intensity need not be homogeneous or atomless; simultaneous occurrences and
zero intensity are allowed. No topology on the sample space is required.

The count representation is required on one event of full measure for all times. It implies
local finiteness of the realizations, and the initial value excludes an unobserved atom at zero.
The conclusion concerns counts on arbitrary Borel sets, not just temporal intervals.

The proof compares with the sigma-finite sampling law `Measure.poissonLaw`, using
`HasIndepIncrements.identDistrib` and `identDistrib_measure_iff_Iic` to recover the full
random-measure law from the count process.

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
`(s,t]`. Starting at zero therefore rules out an atom at the origin. Both the cumulative identity
and the initial condition need hold only almost surely. Atomic and zero intensities are allowed. -/
theorem isPoissonRandomMeasure_of_count_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → Measure ℝ≥0} {N : ℝ≥0 → Ω → ℕ} {Λ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure Λ] (hΛ : Λ {0} = 0)
    (hM : Measurable M) (hN : ∀ t, Measurable (N t))
    (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞))
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0) (hind : HasIndepIncrements N P)
    (hlaw : ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
      (poissonMeasure (Λ (Ioc s t)).toNNReal) P) :
    IsPoissonRandomMeasure P M Λ := by
  have hmono : ∀ᵐ ω ∂P, Monotone (fun t ↦ N t ω) := by
    filter_upwards [hcount] with ω hω s t hst
    exact_mod_cast (hω s).symm.trans_le
      ((measure_mono (Iic_subset_Iic.mpr hst)).trans_eq (hω t))
  have hfinite : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) ≠ ∞ := by
    filter_upwards [hcount] with ω hω t
    rw [hω t]
    exact ENNReal.natCast_ne_top _
  -- Compare with the already constructed Poisson random measure.
  let Q := Λ.poissonLaw
  have hQ : IsPoissonRandomMeasure Q id Λ :=
    isPoissonRandomMeasure_of_laplaceFunctional measurable_id
      (fun f hf ↦ Measure.laplaceFunctional_poissonLaw Λ hf)
  let C : ℝ≥0 → Measure ℝ≥0 → ℕ := fun t μ ↦ ⌊(μ (Ioc 0 t)).toNNReal⌋₊
  have hC : ∀ t, Measurable (C t) := hQ.measurable_nat_count
  have hCmono : ∀ᵐ μ ∂Q, Monotone (fun t ↦ C t μ) := hQ.ae_monotone_nat_count
  have hCcount : ∀ᵐ μ ∂Q, ∀ t, μ (Iic t) = (C t μ : ℝ≥0∞) :=
    hQ.ae_forall_natCast_nat_count_Iic hΛ
  have hQfinite : ∀ᵐ μ ∂Q, ∀ t, μ (Iic t) ≠ ∞ := by
    filter_upwards [hCcount] with μ hμ t
    rw [hμ t]
    exact ENNReal.natCast_ne_top _
  -- Integer casts turn truncated natural subtraction into group subtraction on monotone paths.
  have hNZ (t : ℝ≥0) : Measurable (fun ω ↦ (N t ω : ℤ)) := by fun_prop
  have hCZ (t : ℝ≥0) : Measurable (fun μ ↦ (C t μ : ℤ)) := by fun_prop
  have h0Z : ∀ᵐ ω ∂P, (N 0 ω : ℤ) = 0 := by
    filter_upwards [h0] with ω hω using by simp [hω]
  have hC0Z : ∀ᵐ μ ∂Q, (C 0 μ : ℤ) = 0 := by simp [C]
  have hinc : ∀ s t, s ≤ t → IdentDistrib
      (fun ω ↦ (N t ω : ℤ) - (N s ω : ℤ))
      (fun μ ↦ (C t μ : ℤ) - (C s μ : ℤ)) P Q := by
    intro s t hst
    have h := ((hlaw s t hst).identDistrib
      (hQ.hasLaw_nat_count_sub hst)).comp (measurable_of_countable (Nat.cast : ℕ → ℤ))
    have heqN : (fun ω ↦ ((N t ω - N s ω : ℕ) : ℤ)) =ᵐ[P]
        (fun ω ↦ (N t ω : ℤ) - (N s ω : ℤ)) := by
      filter_upwards [hmono] with ω hω using Int.ofNat_sub (hω hst)
    have heqC : (fun μ ↦ ((C t μ - C s μ : ℕ) : ℤ)) =ᵐ[Q]
        (fun μ ↦ (C t μ : ℤ) - (C s μ : ℤ)) := by
      filter_upwards [hCmono] with μ hμ using Int.ofNat_sub (hμ hst)
    exact (IdentDistrib.of_ae_eq h.aemeasurable_fst heqN).symm.trans
      (h.trans (IdentDistrib.of_ae_eq h.aemeasurable_snd heqC))
  have hpaths := (hind.natCast hmono).identDistrib
    (hQ.hasIndepIncrements_nat_count.natCast hCmono) hNZ hCZ h0Z hC0Z hinc
  have hcum := hpaths.comp (measurable_pi_iff.mpr fun t ↦
    (measurable_of_countable (fun z : ℤ ↦ (z.toNat : ℝ≥0∞))).comp
      (measurable_pi_apply t))
  have hcum' : IdentDistrib (fun ω t ↦ M ω (Iic t))
      (fun μ t ↦ μ (Iic t)) P Q := by
    have heqM : (fun ω t ↦ ((N t ω : ℤ).toNat : ℝ≥0∞)) =ᵐ[P]
        (fun ω t ↦ M ω (Iic t)) := by
      filter_upwards [hcount] with ω hω
      funext t
      simpa using (hω t).symm
    have heqQ : (fun μ t ↦ ((C t μ : ℤ).toNat : ℝ≥0∞)) =ᵐ[Q]
        (fun μ t ↦ μ (Iic t)) := by
      filter_upwards [hCcount] with μ hμ
      funext t
      simpa using (hμ t).symm
    exact (IdentDistrib.of_ae_eq hcum.aemeasurable_fst heqM).symm.trans
      (hcum.trans (IdentDistrib.of_ae_eq hcum.aemeasurable_snd heqQ))
  exact hQ.of_identDistrib hM
    ((identDistrib_measure_iff_Iic hM.aemeasurable measurable_id.aemeasurable
      hfinite hQfinite).mpr hcum').symm

end TauCeti.Probability
