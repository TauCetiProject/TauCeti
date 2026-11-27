/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.RingTheory.ClassGroup.HeightOneSpectrum
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting

/-!
# The Minkowski bound for the class group

The Minkowski constant `minkowskiConstant` is positive and at most one. This gives
`minkowskiClassBound_le_sqrt_abs_discr`, which bounds the exact ideal-class cutoff by the
square root of the absolute discriminant. The proof splits the factorial using Mathlib's
`Nat.factorial_mul_descFactorial`. The lower bound `one_le_minkowskiClassBound` uses
Mathlib's `NumberField.exists_ideal_in_class_of_norm_le` for the trivial class.

Every ideal class of a number field contains a nonzero integral ideal of norm at most the
Minkowski bound, so the class number is at most the number of such ideals
(`TauCeti.NumberField.classNumber_le_card_idealsLE`).

The classes of prime ideals of norm at most the Minkowski bound generate the class group of
any number field. The bound may be replaced by a larger real number, allowing a numerical
upper bound to supply the generators for a class-group presentation.

The proof uses Mathlib's `NumberField.exists_ideal_in_class_of_norm_le` and the prime-support
criterion `ClassGroup.mk0_mem_closure_of_count_eq`: every prime factor of a small integral
ideal has norm at most that of the ideal.

## References

* W. Stein, *Algebraic Number Theory, a Computational Approach*, §7.3, Lemma 7.3.1.
* K. Conrad, *Class group calculations by Minkowski bound*, §1.
-/

public section

open IsDedekindDomain Module NumberField.InfinitePlace
open scoped NumberField nonZeroDivisors Real

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The Minkowski constant `(4 / π) ^ r₂ * (n ! / n ^ n)` for a number field of degree
`n` with `r₂` complex places. -/
noncomputable def minkowskiConstant : ℝ :=
  (4 / Real.pi) ^ nrComplexPlaces K * ((finrank ℚ K).factorial / (finrank ℚ K : ℝ) ^ finrank ℚ K)

/-- The defining formula for the Minkowski constant in terms of the degree and complex places. -/
theorem minkowskiConstant_def :
    minkowskiConstant K =
      (4 / Real.pi) ^ nrComplexPlaces K *
        ((finrank ℚ K).factorial / (finrank ℚ K : ℝ) ^ finrank ℚ K) := (rfl)

/-- The Minkowski constant of a number field is positive. -/
theorem minkowskiConstant_pos : 0 < minkowskiConstant K := by
  rw [minkowskiConstant_def]
  have hn : 0 < (finrank ℚ K : ℝ) := Nat.cast_pos.mpr finrank_pos
  positivity

/-- The Minkowski constant of any number field is at most one. -/
theorem minkowskiConstant_le_one : minkowskiConstant K ≤ 1 := by
  rw [minkowskiConstant_def]
  set n := finrank ℚ K
  set r := nrComplexPlaces K
  have hsig : 2 * r ≤ n := by
    have h := card_add_two_mul_card_eq_rank K
    omega
  have hr : r ≤ n := by omega
  -- Bound the first `r` factors by `r` and the remaining factors by `n`.
  have hfactorial : 2 ^ r * n.factorial ≤ n ^ n := by
    rw [← Nat.factorial_mul_descFactorial (Nat.sub_le n r), Nat.sub_sub_self hr]
    calc
      2 ^ r * (r.factorial * n.descFactorial (n - r)) ≤ 2 ^ r * (r ^ r * n ^ (n - r)) := by
        gcongr
        · exact Nat.factorial_le_pow r
        · exact n.descFactorial_le_pow _
      _ = (2 * r) ^ r * n ^ (n - r) := by rw [mul_pow, mul_assoc]
      _ ≤ n ^ r * n ^ (n - r) := by gcongr
      _ = n ^ n := by rw [← pow_add, Nat.add_sub_of_le hr]
  have hπ : (4 : ℝ) / Real.pi ≤ 2 :=
    (div_le_iff₀ Real.pi_pos).2 (by linarith [Real.pi_gt_three])
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr finrank_pos
  rw [← mul_div_assoc, div_le_one (by positivity)]
  calc
    (4 / Real.pi) ^ r * (n.factorial : ℝ) ≤ 2 ^ r * (n.factorial : ℝ) := by gcongr
    _ ≤ (n : ℝ) ^ n := by exact_mod_cast hfactorial

/-- The Minkowski constant of the rational field is one. -/
@[simp]
theorem minkowskiConstant_rat : minkowskiConstant ℚ = 1 := by
  simp [minkowskiConstant_def, nrComplexPlaces_eq_zero_of_finrank_eq_one (finrank_self ℚ)]

/-- The real Minkowski bound for an integral ideal representative of an ideal class of `K`.
This is the Minkowski constant times the square root of the absolute discriminant. -/
noncomputable def minkowskiClassBound : ℝ :=
  minkowskiConstant K * Real.sqrt |(NumberField.discr K : ℝ)|

/-- The formula for the class representative bound in terms of the Minkowski constant. -/
theorem minkowskiClassBound_def :
    minkowskiClassBound K = minkowskiConstant K * Real.sqrt |(NumberField.discr K : ℝ)| := (rfl)

/-- The real Minkowski bound of the rational field is one. -/
@[simp]
theorem minkowskiClassBound_rat : minkowskiClassBound ℚ = 1 := by
  simp [minkowskiClassBound_def]

/-- The real Minkowski bound is at most the square root of the absolute discriminant. -/
theorem minkowskiClassBound_le_sqrt_abs_discr :
    minkowskiClassBound K ≤ Real.sqrt |(NumberField.discr K : ℝ)| := by
  rw [minkowskiClassBound_def]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (minkowskiConstant_le_one K)

/-- Every ideal class contains a nonzero integral ideal of norm at most
`minkowskiClassBound K`. This is Mathlib's `NumberField.exists_ideal_in_class_of_norm_le`
with the cutoff expressed in terms of the Minkowski constant. -/
theorem _root_.ClassGroup.exists_ideal_of_absNorm_le_minkowskiClassBound {K : Type*} [Field K]
    [NumberField K] (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ minkowskiClassBound K := by
  simpa only [minkowskiClassBound_def, minkowskiConstant_def, mul_assoc] using
    NumberField.exists_ideal_in_class_of_norm_le C

/-- The real Minkowski bound is at least one. -/
theorem one_le_minkowskiClassBound : 1 ≤ minkowskiClassBound K := by
  obtain ⟨I, -, hI⟩ := (1 : ClassGroup (𝓞 K)).exists_ideal_of_absNorm_le_minkowskiClassBound
  have hnorm : 1 ≤ Ideal.absNorm (I : Ideal (𝓞 K)) :=
    Ideal.absNorm_pos_of_nonZeroDivisors I
  exact (Nat.one_le_cast.mpr hnorm).trans hI

/-- **Minkowski's bound as an ideal count.** The class number of `K` is at most the number of
nonzero integral ideals of `𝓞 K` of norm at most `x`, whenever `x` is at least the Minkowski
bound.

In particular, the exact Minkowski bound can be used by taking `hx := le_rfl`. -/
theorem classNumber_le_card_idealsLE {x : ℝ}
    (hx : minkowskiClassBound K ≤ x) :
    NumberField.classNumber K ≤ (TauCeti.idealsLE K x).card := by
  classical
  -- Each ideal class is the class of a nonzero integral ideal of norm at most `x`.
  have hM : Set.SurjOn ClassGroup.mk0 (TauCeti.idealsLE K x : Set (Ideal (𝓞 K))⁰)
      (Finset.univ : Finset (ClassGroup (𝓞 K))) := by
    intro C _
    obtain ⟨I, hI, hle⟩ := C.exists_ideal_of_absNorm_le_minkowskiClassBound
    exact ⟨I, (TauCeti.mem_normLE _).mpr (hle.trans hx), hI⟩
  have hcard := Finset.card_le_card_of_surjOn _ hM
  rwa [Finset.card_univ, ← NumberField.classNumber] at hcard

/-- **Minkowski's class-group generation bound.** The classes of nonzero prime ideals of norm
at most `B` generate the class group whenever `B` is at least the Minkowski bound.

In particular, the exact Minkowski bound can be used by taking `hB := le_rfl`. -/
theorem closure_classGroupMk_image_absNorm_le_eq_top {B : ℝ}
    (hB : minkowskiClassBound K ≤ B) :
    Subgroup.closure (HeightOneSpectrum.classGroupMk ''
      {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ B}) = ⊤ := by
  refine top_unique fun C _ ↦ ?_
  obtain ⟨I, rfl, hI⟩ := C.exists_ideal_of_absNorm_le_minkowskiClassBound
  have hI0 := nonZeroDivisors.coe_ne_zero I
  refine ClassGroup.mk0_mem_closure_of_count_eq K 1 fun v hv ↦ ?_
  rw [Units.val_one, map_one, FractionalIdeal.count_one,
    FractionalIdeal.count_coeIdeal_eq_zero_iff hI0]
  intro hd
  have hn : Ideal.absNorm v.asIdeal ≤ Ideal.absNorm (I : Ideal (𝓞 K)) :=
    Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors I)
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hd))
  exact hv ((Nat.cast_le.mpr hn).trans (hI.trans hB))

end TauCeti.NumberField
