/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import TauCeti.NumberTheory.NumberField.Discriminant.RootDiscr

/-!
# Root discriminants in towers

The absolute norm of the relative different measures the growth of the root discriminant in an
extension of number fields. In particular, if the different contains a positive integer `n`,
the root discriminant can grow by at most a factor of `n`.

The formulas use the discriminant tower formula
`NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow` from Mathlib.
-/

public section

open Module NumberField

namespace TauCeti.NumberField

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The relative different's absolute norm, raised to the reciprocal of the absolute degree of
`L`, is the factor by which the root discriminant grows from `K` to `L`. -/
theorem rootDiscr_eq_mul_rpow_absNorm_differentIdeal :
    rootDiscr L = rootDiscr K *
      ((differentIdeal (𝓞 K) (𝓞 L)).absNorm : ℝ) ^ (finrank ℚ L : ℝ)⁻¹ := by
  have hd : (finrank K L : ℝ) ≠ 0 := by exact_mod_cast (finrank_pos (R := K) (M := L)).ne'
  have hd' : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℚ) (M := K)).ne'
  have hdegree : (finrank ℚ L : ℝ) = (finrank ℚ K : ℝ) * (finrank K L : ℝ) := by
    exact_mod_cast (finrank_mul_finrank ℚ K L).symm
  have hexp : (finrank K L : ℝ) * (finrank ℚ L : ℝ)⁻¹ = (finrank ℚ K : ℝ)⁻¹ := by
    rw [hdegree]
    field_simp
  simp only [rootDiscr_def, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)]
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by positivity),
    hexp, mul_comm]

/-- If the relative different contains the positive integer `n`, the root discriminant of the
extension is between the root discriminant of the base and `n` times that root discriminant. -/
theorem rootDiscr_mem_Icc_of_natCast_mem_differentIdeal {n : ℕ} (hn : 0 < n)
    (h : (n : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L)) :
    rootDiscr L ∈ Set.Icc (rootDiscr K) (rootDiscr K * n) := by
  let I := differentIdeal (𝓞 K) (𝓞 L)
  have hI₀ : 1 ≤ I.absNorm := by
    exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr differentIdeal_ne_bot)
  have hI₁ : I.absNorm ≤ n ^ finrank ℚ L := by
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem I).2 h)
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank] at hdvd
    exact Nat.le_of_dvd (pow_pos hn _) hdvd
  have hd := (finrank_pos (R := ℚ) (M := L)).ne'
  have hlow : 1 ≤ (I.absNorm : ℝ) ^ (finrank ℚ L : ℝ)⁻¹ :=
    Real.one_le_rpow (by exact_mod_cast hI₀) (by positivity)
  have hhigh : (I.absNorm : ℝ) ^ (finrank ℚ L : ℝ)⁻¹ ≤ (n : ℝ) := by
    rw [← Real.pow_rpow_inv_natCast (Nat.cast_nonneg n) hd]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hI₁) (by positivity)
  have hk : 0 ≤ rootDiscr K := zero_le_one.trans (one_le_rootDiscr K)
  rw [rootDiscr_eq_mul_rpow_absNorm_differentIdeal K L]
  exact ⟨by simpa only [mul_one] using mul_le_mul_of_nonneg_left hlow hk,
    mul_le_mul_of_nonneg_left hhigh hk⟩

end TauCeti.NumberField
