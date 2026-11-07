/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MarchenkoPastur.Moments

/-!
# Free Poisson probability measures

The free Poisson law `freePoisson r c` has rate `r ≥ 0` and real jump size `c`. For positive
rate it is the dilation of the Marchenko–Pastur law of aspect ratio `r⁻¹` by `c * r`.
At rate zero it is the Dirac mass at zero. Negative jumps are allowed.

Its moments are `c ^ n * ∑ π ∈ NC(n), r ^ |π|`; thus each block of size `k` has cumulant
weight `r * c ^ k`. This connects the positive, compactly supported measure to the algebraic
free Poisson cumulants and the rare-event limit. The construction reuses the Marchenko–Pastur
measure, including its atom, rather than normalizing a new density.

## Main results

* `integral_pow_freePoisson`: the noncrossing-partition moment formula.
* `map_mul_freePoisson`: rescaling changes the jump size, including zero and negative scales.
* `isCompact_support_freePoisson`: compact support for every rate and jump size.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 12.
-/

public section

noncomputable section

open MeasureTheory Finset Set
open scoped NNReal

namespace TauCeti.Probability

/-- The free Poisson probability measure of rate `r` and jump size `c`. For `r ≠ 0` it is
`MP_(1/r)` dilated by `c * r`; for `r = 0` it is the Dirac mass at zero. -/
def freePoisson (r : ℝ≥0) (c : ℝ) : Measure ℝ :=
  if r = 0 then Measure.dirac 0 else
    (marchenkoPastur r⁻¹).map (fun x => c * (r : ℝ) * x)

/-- The positive-rate comparison with the native Marchenko–Pastur measure. -/
theorem freePoisson_of_ne_zero {r : ℝ≥0} (hr : r ≠ 0) (c : ℝ) :
    freePoisson r c = (marchenkoPastur r⁻¹).map (fun x => c * (r : ℝ) * x) := by
  simp [freePoisson, hr]

@[simp]
theorem freePoisson_zero_rate (c : ℝ) : freePoisson 0 c = Measure.dirac 0 := by
  simp [freePoisson]

/-- The free Poisson law has total mass one, also at rate or jump size zero. -/
instance isProbabilityMeasure_freePoisson (r : ℝ≥0) (c : ℝ) :
    IsProbabilityMeasure (freePoisson r c) := by
  by_cases hr : r = 0
  · subst r
    rw [freePoisson_zero_rate]
    infer_instance
  · rw [freePoisson_of_ne_zero hr]
    infer_instance

@[simp]
theorem freePoisson_zero_jump (r : ℝ≥0) : freePoisson r 0 = Measure.dirac 0 := by
  by_cases hr : r = 0
  · simp [hr]
  · simp [freePoisson_of_ne_zero hr]

/-- Changing scale multiplies the jump size. No sign or nonzero assumption on either is needed. -/
theorem map_mul_freePoisson (r : ℝ≥0) (c d : ℝ) :
    (freePoisson r c).map (fun x => d * x) = freePoisson r (d * c) := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [freePoisson_of_ne_zero hr, freePoisson_of_ne_zero hr,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp [mul_assoc]

/-- At rate one and jump one the free Poisson law is `MP_1`. -/
@[simp]
theorem freePoisson_one_one : freePoisson 1 1 = marchenkoPastur 1 := by
  simp [freePoisson]

/-- For a nonzero jump, the atom at zero has mass `max (1 - r) 0`. A zero jump puts the
entire law at zero. The rate-zero case is included. -/
@[simp]
theorem freePoisson_singleton_zero (r : ℝ≥0) (c : ℝ) :
    freePoisson r c {0} = if c = 0 then 1 else ENNReal.ofReal (1 - (r : ℝ)) := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hr : r = 0
  · simp [hr, hc]
  have hr' : (r : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hr
  have hpre : (fun x : ℝ => c * (r : ℝ) * x) ⁻¹' {0} = {0} := by
    ext x
    simp [mul_eq_zero, hc, hr']
  rw [freePoisson_of_ne_zero hr, Measure.map_apply (by fun_prop) (measurableSet_singleton 0),
    hpre, marchenkoPastur_singleton_zero, ite_eq_right hc, NNReal.coe_inv]
  congr 1
  field_simp

/-- A compact carrying set obtained by dilating the nonnegative carrying interval of `MP_(1/r)`.
The image formulation also handles negative jump sizes without reversing endpoints by hand. -/
theorem ae_mem_image_Icc_freePoisson (r : ℝ≥0) (c : ℝ) :
    ∀ᵐ x ∂freePoisson r c,
      x ∈ (fun y => c * (r : ℝ) * y) '' Icc 0 ((1 + Real.sqrt (r⁻¹ : ℝ≥0)) ^ 2) := by
  by_cases hr : r = 0
  · subst r
    simp
  · rw [freePoisson_of_ne_zero hr]
    apply (ae_map_iff (by fun_prop)
      ((isCompact_Icc.image (f := fun y : ℝ => c * (r : ℝ) * y)
        (by fun_prop)).measurableSet)).2
    filter_upwards [ae_mem_Icc_zero_marchenkoPastur r⁻¹] with x hx
    exact mem_image_of_mem _ hx

/-- Every free Poisson law has compact support, including its possible atom at zero. -/
theorem isCompact_support_freePoisson (r : ℝ≥0) (c : ℝ) :
    IsCompact (freePoisson r c).support := by
  have hK := (isCompact_Icc (a := (0 : ℝ))
    (b := (1 + Real.sqrt (r⁻¹ : ℝ≥0)) ^ 2)).image
      (f := fun y : ℝ => c * (r : ℝ) * y) (by fun_prop)
  exact hK.of_isClosed_subset Measure.isClosed_support
    (Measure.support_subset_of_isClosed hK.isClosed (ae_mem_image_Icc_freePoisson r c))

/-- All natural moments of a free Poisson law are integrable. -/
theorem integrable_pow_freePoisson (r : ℝ≥0) (c : ℝ) (n : ℕ) :
    Integrable (fun x => x ^ n) (freePoisson r c) := by
  by_cases hr : r = 0
  · simp only [hr, freePoisson_zero_rate]
    exact integrable_dirac (by simp)
  · rw [freePoisson_of_ne_zero hr]
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
    simpa only [Function.comp_def, mul_pow] using
      (integrable_pow_marchenkoPastur r⁻¹ n).const_mul ((c * (r : ℝ)) ^ n)

/-- The `n`-th moment of the free Poisson law: the Narayana polynomial in the rate, multiplied
by the `n`-th power of the jump size. The empty-word moment is one, including at rate zero. -/
theorem integral_pow_freePoisson (r : ℝ≥0) (c : ℝ) (n : ℕ) :
    ∫ x, x ^ n ∂freePoisson r c =
      c ^ n * ∑ π : NoncrossingPartition (univ : Finset (Fin n)), (r : ℝ) ^ #π.1.parts := by
  by_cases hr : r = 0
  · subst r
    cases n with
    | zero =>
      rw [NoncrossingPartition.sum_comp_card_parts_of_card_eq_zero (by simp)]
      simp
    | succ n =>
      have hparts (π : NoncrossingPartition (univ : Finset (Fin (n + 1)))) :
          #π.1.parts ≠ 0 := by
        exact (π.1.parts_nonempty (Finset.bot_eq_empty ▸ univ_nonempty.ne_empty)).card_pos.ne'
      simp [hparts]
  · have hr' : (r : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hr
    rw [freePoisson_of_ne_zero hr, integral_map (by fun_prop) (by fun_prop)]
    simp_rw [mul_pow]
    rw [integral_const_mul, integral_pow_marchenkoPastur, mul_sum, mul_sum]
    refine sum_congr rfl fun π _ => ?_
    rw [NNReal.coe_inv]
    have hk := π.1.card_parts_le_card
    simp only [card_univ, Fintype.card_fin] at hk
    rw [inv_pow, mul_assoc, ← pow_sub₀ _ hr' (Nat.sub_le _ _), Nat.sub_sub_self hk]

end TauCeti.Probability
