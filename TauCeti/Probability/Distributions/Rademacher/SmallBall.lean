/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SetFamily.LittlewoodOfford
public import TauCeti.Probability.Distributions.Rademacher.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Littlewood–Offord anti-concentration for Rademacher sums

For independent Rademacher signs and real coefficients of absolute value at least `r > 0`,
the probability of any half-open interval of length `2r` is at most
`n.choose (n / 2) / 2^n`. Consequently the same estimate holds for open balls of radius `r`
and for point masses when all coefficients are nonzero. No measurability beyond the
almost-everywhere measurability provided by `HasLaw` is required. Nonpositive radii are
allowed as well, since the corresponding intervals and balls are empty.

This supplies the small-ball input for studying invertibility of random matrices. The
combinatorial step is Erdős's antichain proof, formalized in
`TauCeti.Combinatorics.SetFamily.LittlewoodOfford`.

## References

* P. Erdős, *On a lemma of Littlewood and Offord*, Bull. Amer. Math. Soc. 51 (1945), 898–902.
-/

public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory.iIndepFun

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {P : Measure Ω} {ε : ι → Ω → ℝ}

/-- Every prescribed sign pattern of independent Rademacher variables has probability `2⁻ⁿ`.
This includes the empty pattern, whose probability is one. -/
theorem measure_forall_eq_rademacher [DecidableEq ι] (hind : iIndepFun ε P)
    (hε : ∀ i, HasLaw (ε i) TauCeti.Probability.rademacherMeasure P) (s : Finset ι) :
    P {ω | ∀ i, ε i ω = if i ∈ s then 1 else -1} =
      (1 / 2 : ℝ≥0∞) ^ Fintype.card ι := by
  have h := hind.measure_inter_preimage_eq_mul univ
    (sets := fun i ↦ {if i ∈ s then (1 : ℝ) else -1}) (by intro i _; measurability)
  have hatom (i : ι) :
      P ((ε i) ⁻¹' {if i ∈ s then (1 : ℝ) else -1}) = (1 / 2 : ℝ≥0∞) := by
    rw [← Measure.map_apply_of_aemeasurable (hε i).aemeasurable (measurableSet_singleton _),
      (hε i).map_eq]
    split_ifs <;> simp
  simpa [hatom, ← Set.ofPred_forall] using h

/-- **Littlewood–Offord inequality.** A weighted sum of independent Rademacher signs, with
coefficient magnitudes at least `r > 0`, belongs to any half-open interval of length `2r` with
probability at most the central binomial coefficient divided by `2ⁿ`. -/
theorem measure_sum_mem_Ico_le_of_rademacher (hind : iIndepFun ε P)
    (hε : ∀ i, HasLaw (ε i) TauCeti.Probability.rademacherMeasure P)
    {a : ι → ℝ} {r : ℝ} (ha : ∀ i, r ≤ |a i|) (x : ℝ) :
    P {ω | (∑ i, a i * ε i ω) ∈ Set.Ico x (x + 2 * r)} ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) / (2 : ℝ≥0∞) ^ Fintype.card ι := by
  classical
  let A : Finset (Finset ι) := univ.filter fun s ↦
    (∑ i, if i ∈ s then a i else -a i) ∈ Set.Ico x (x + 2 * r)
  have hsign : ∀ᵐ ω ∂P, ∀ i, ε i ω = 1 ∨ ε i ω = -1 :=
    ae_all_iff.2 fun i ↦
      TauCeti.Probability.ae_eq_one_or_eq_neg_one_of_map_eq_rademacherMeasure (hε i).map_eq
  have hcover :
      {ω | (∑ i, a i * ε i ω) ∈ Set.Ico x (x + 2 * r)} ≤ᵐ[P]
        ⋃ s ∈ A, {ω | ∀ i, ε i ω = if i ∈ s then 1 else -1} := by
    filter_upwards [hsign] with ω hω hevent
    let s := univ.filter fun i ↦ ε i ω = 1
    have hs (i : ι) : ε i ω = if i ∈ s then 1 else -1 := by
      by_cases hi : ε i ω = 1
      · simp [s, hi]
      · simp [s, (hω i).resolve_left hi]
    have hsum : (∑ i, if i ∈ s then a i else -a i) = ∑ i, a i * ε i ω := by
      apply sum_congr rfl
      intro i _
      rw [hs i]
      split_ifs <;> simp
    exact Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨by simpa [A, hsum], hs⟩⟩
  calc
    _ ≤ P (⋃ s ∈ A, {ω | ∀ i, ε i ω = if i ∈ s then 1 else -1}) := measure_mono_ae hcover
    _ ≤ ∑ s ∈ A, P {ω | ∀ i, ε i ω = if i ∈ s then 1 else -1} :=
      measure_biUnion_finset_le _ _
    _ = (A.card : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ Fintype.card ι := by
      simp only [hind.measure_forall_eq_rademacher hε, sum_const, nsmul_eq_mul]
    _ ≤ ((Fintype.card ι).choose (Fintype.card ι / 2) : ℝ≥0∞) *
        (1 / 2 : ℝ≥0∞) ^ Fintype.card ι := by
      gcongr
      exact TauCeti.card_filter_signedSum_mem_Ico_le ha x
    _ = _ := by simp only [div_eq_mul_inv, one_mul, ← ENNReal.inv_pow]

/-- The sharp Littlewood–Offord bound for an open ball of radius `r`. A closed ball would
be false at the endpoint: one coefficient equal to `r` puts both signs in `[-r, r]`. -/
theorem measure_abs_sum_sub_lt_le_of_rademacher (hind : iIndepFun ε P)
    (hε : ∀ i, HasLaw (ε i) TauCeti.Probability.rademacherMeasure P)
    {a : ι → ℝ} {r : ℝ} (ha : ∀ i, r ≤ |a i|) (x : ℝ) :
    P {ω | |(∑ i, a i * ε i ω) - x| < r} ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) / (2 : ℝ≥0∞) ^ Fintype.card ι := by
  refine (measure_mono fun ω hω ↦ ?_).trans
    (hind.measure_sum_mem_Ico_le_of_rademacher hε ha (x - r))
  obtain ⟨hl, hu⟩ := abs_lt.1 (Set.mem_ofPred_eq.mp hω)
  exact ⟨by linarith, by linarith⟩

/-- **Littlewood–Offord point-mass bound.** No atom of a weighted sum of independent
Rademacher signs with nonzero real coefficients has mass greater than `n.choose (n / 2) / 2ⁿ`.
The coefficients need not have a specified uniform lower bound. -/
theorem measure_sum_eq_le_of_rademacher (hind : iIndepFun ε P)
    (hε : ∀ i, HasLaw (ε i) TauCeti.Probability.rademacherMeasure P)
    {a : ι → ℝ} (ha : ∀ i, a i ≠ 0) (x : ℝ) :
    P {ω | (∑ i, a i * ε i ω) = x} ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) / (2 : ℝ≥0∞) ^ Fintype.card ι := by
  classical
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  cases isEmpty_or_nonempty ι with
  | inl h => exact (measure_mono (Set.subset_univ _)).trans_eq (by simp)
  | inr h =>
    let r := univ.inf' univ_nonempty fun i ↦ |a i|
    have hr : 0 < r := (lt_inf'_iff _).2 fun i _ ↦ abs_pos.2 (ha i)
    refine (measure_mono fun ω hω ↦ ?_).trans
      (hind.measure_abs_sum_sub_lt_le_of_rademacher hε
        (r := r) (a := a) (fun i ↦ inf'_le _ (mem_univ i)) x)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    simpa only [hω, sub_self, abs_zero] using hr

end ProbabilityTheory.iIndepFun
