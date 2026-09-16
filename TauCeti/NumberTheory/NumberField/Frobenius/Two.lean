/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.RingTheory.Ideal.LiesOver

/-!
# Frobenius on square roots at 2

For `d ≡ 1 (mod 4)`, an arithmetic Frobenius at a prime above `2` fixes a square root of
`d` exactly when `d ≡ 1 (mod 8)`, and negates it when `d ≡ 5 (mod 8)`. The ambient field
need not be quadratic, so the result applies to each generator of a multiquadratic field.

The two roots have identical reductions in characteristic two. Instead one uses the algebraic
integer `(1 + √d) / 2`, whose conjugate is `1 - (1 + √d) / 2`; their difference has odd square
and hence is nonzero modulo the prime. This is the dyadic counterpart of the Legendre-symbol
formula for Frobenius at odd primes, and supplies its missing local input at an odd discriminant.

The classical quadratic splitting criterion is described in D. A. Cox,
*Primes of the Form x² + ny²*, §5.A.
-/

public section

open NumberField Ideal
open scoped NumberField

namespace TauCeti

/-- At a prime above `2`, Frobenius fixes `√d` exactly when `d ≡ 1 (mod 8)`, provided
`d ≡ 1 (mod 4)`. This works in any characteristic-zero field containing the chosen square root. -/
theorem isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight
    {K : Type*} [Field K] [CharZero K] {d : ℤ} {x : K}
    (hx : x ^ 2 = algebraMap ℤ K d) (hd : d % 4 = 1)
    (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(2 : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ x = x ↔ d % 8 = 1 := by
  -- Pass to the integral half-generator before reducing modulo 2.
  let w : 𝓞 K := ⟨(1 + x) / 2, isIntegral_one_add_div_two_of_sq_eq hx hd⟩
  have he : d = 4 * (d / 4) + 1 := by omega
  have heK : (d : K) = 4 * ((d / 4 : ℤ) : K) + 1 := by exact_mod_cast he
  have hwsq : w ^ 2 - w = algebraMap ℤ (𝓞 K) (d / 4) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    simp only [map_sub, map_pow, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
    -- The structure map on the explicit integral-closure element is its first component.
    change ((1 + x) / 2) ^ 2 - (1 + x) / 2 = (d / 4 : ℤ)
    field_simp
    linear_combination hx + heK
  have hcong : σ • w - w ^ 2 ∈ Q := by
    have h := hσ w
    rwa [natCard_quotient_under_of_liesOver (p := 2) Q,
      MulSemiringAction.toAlgHom_apply] at h
  have hfix : σ • w = w ↔ σ x = x := by
    rw [← (FaithfulSMul.algebraMap_injective (𝓞 K) K).eq_iff,
      algebraMap_smul_eq_apply]
    -- The structure map on this explicit integral-closure element is its first component.
    change σ ((1 + x) / 2) = (1 + x) / 2 ↔ σ x = x
    simp only [map_div₀, map_add, map_one, map_ofNat]
    constructor
    · intro h
      linear_combination 2 * h
    · intro h
      rw [h]
  -- Its conjugates are `w` and `1 - w`, even when the ambient field is larger.
  have hpm : σ • w = w ∨ σ • w = 1 - w := by
    have hxsq : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, hx]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxsq with h | h
    · exact Or.inl (hfix.mpr h)
    · right
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_sub, map_one, algebraMap_smul_eq_apply]
      -- As above, expose the explicitly packaged half-integral generator.
      change σ ((1 + x) / 2) = 1 - (1 + x) / 2
      simp only [map_div₀, map_add, map_one, map_ofNat, h]
      ring
  -- The Frobenius congruence distinguishes these conjugates by the parity of `(d - 1) / 4`.
  have heven : σ • w = w ↔ (2 : ℤ) ∣ d / 4 := by
    constructor
    · intro h
      rw [h] at hcong
      have hmem := Q.neg_mem hcong
      rw [neg_sub, hwsq] at hmem
      exact (algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp hmem
    · intro h
      rcases hpm with hfix | hneg
      · exact hfix
      · have hemem := (algebraMap_int_mem_iff_dvd_of_liesOver Q (d / 4)).mpr h
        have htwo : (2 : 𝓞 K) ∈ Q := by
          simpa using (algebraMap_int_mem_iff_dvd_of_liesOver Q 2).mpr (dvd_refl 2)
        have hone : (1 : 𝓞 K) ∈ Q := by
          have hsum := Q.add_mem (Q.add_mem hcong hemem) (Q.mul_mem_right w htwo)
          rw [hneg] at hsum
          convert hsum using 1
          linear_combination hwsq
        have hbad : (2 : ℤ) ∣ 1 :=
          (algebraMap_int_mem_iff_dvd_of_liesOver Q 1).mp (by simpa using hone)
        norm_num at hbad
  rw [← hfix, heven, Int.dvd_iff_emod_eq_zero]
  omega

/-- At a prime above `2`, Frobenius fixes square roots of integers congruent to `1` modulo `8`
and negates square roots of integers congruent to `5` modulo `8`. -/
theorem isArithFrobAt_apply_sqrt_two
    {K : Type*} [Field K] [CharZero K] {d : ℤ} {x : K}
    (hx : x ^ 2 = algebraMap ℤ K d) (hd : d % 4 = 1)
    (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(2 : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ x = if d % 8 = 1 then x else -x := by
  have hfix := isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight hx hd Q hσ
  split_ifs with h
  · exact hfix.mpr h
  · have hsq : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, hx]; simp
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_left (fun h' ↦ h (hfix.mp h'))

end TauCeti
