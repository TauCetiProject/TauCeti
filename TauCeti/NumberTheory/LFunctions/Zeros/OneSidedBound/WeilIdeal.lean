/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Data.Nat.Factorization.Basic
import TauCeti.RingTheory.Ideal.ConjugateFactor

/-!
# The fractional ideal of the Weil lattice

A relative different supported at the cyclotomic level splits into conjugate factors. The
inverse of the factor supported at the primes containing the trace-one integer `β` is the
fractional ideal used for the Weil lattice. It lies between the integer ring and its dilation
by the inverse level; the product with its conjugate, scaled by the inverse base different
generator, is the inverse absolute different.

The choice of support and normalization follow `New.Parameters.α` and
`New.Parameters.v_weilData_j_mul_alpha_mul_star` in `grh/src/New/Derivatives/Field/WeilData.lean`
of lsernau/grh-lean at `72fead102f663d5c7a407964a13dc0cf9d977207`. Here the construction uses
ideals and comaximality rather than ideles and valuations.
-/

public section

open NumberField IsCMField Ideal
open scoped nonZeroDivisors

namespace TauCeti.OneSidedBound

/-- Every cyclotomic-level prime divides the norm of the trace-one integer of `ℚ(√−d)`.
Consequently the level divides a power of that norm. -/
theorem Parameters.q₁_dvd_norm_pow (P : Parameters) (s : ℕ) :
    P.q₁ s ∣ ((P.d + 1) / 4) ^ P.q₁ s := by
  have hd : (P.d + 1) / 4 ≠ 0 := by have := P.sixty_four_lt_d; omega
  refine (Nat.dvd_pow_self_iff (P.q₁_pos s).ne' hd).mpr fun p hp ↦ ?_
  obtain ⟨hp, hq, _⟩ := Nat.mem_primeFactors.mp hp
  exact hp.mem_primeFactors (P.dvd_d_add_one_div_four hp hq) hd

/-- Split a conjugation-invariant ideal containing the cyclotomic level by a `β` of norm
`(d+1)/4` coprime to its conjugate (in particular, the trace-one integer of `ℚ(√−d)`). The
factor `I` has precisely the primes of `J` containing `β`. The
fractional ideal `I⁻¹` contains the integers, and multiplication by the level makes it integral.
If the absolute different is `(δ)J`, multiplication of `I⁻¹` and its conjugate by `δ⁻¹` gives
its inverse. -/
theorem Parameters.exists_weilIdeal (P : Parameters) (s : ℕ) {E : Type*}
    [Field E] [NumberField E] [IsCMField E] (J : Ideal (𝓞 E)) {β δ : 𝓞 E}
    (hJ : J.map (ringOfIntegersComplexConj E).toRingHom = J) (hq : (P.q₁ s : 𝓞 E) ∈ J)
    (hβ : IsCoprime β (ringOfIntegersComplexConj E β))
    (hnorm : β * ringOfIntegersComplexConj E β = (((P.d + 1) / 4 : ℕ) : 𝓞 E))
    (hD : differentIdeal ℤ (𝓞 E) = span {δ} * J) :
    ∃ I : Ideal (𝓞 E),
      (∀ M : Ideal (𝓞 E), M.IsPrime → (I ≤ M ↔ J ≤ M ∧ β ∈ M)) ∧
      1 ≤ (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ∧
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (P.q₁ s : E) *
        (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ≤ 1 ∧
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (δ : E)⁻¹ *
        (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ *
        (↑(I.map (ringOfIntegersComplexConj E).toRingHom) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ =
        (↑(differentIdeal ℤ (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
  have hm : β * ringOfIntegersComplexConj E β ∈ J.radical := by
    rw [mem_radical_iff]
    refine ⟨P.q₁ s, ?_⟩
    obtain ⟨a, ha⟩ := P.q₁_dvd_norm_pow s
    rw [hnorm, ← Nat.cast_pow, ha, Nat.cast_mul]
    exact J.mul_mem_right _ hq
  obtain ⟨I, ⟨hI, hsupport⟩, _⟩ :=
    J.existsUnique_conjugate_factor (ringOfIntegersComplexConj E).toRingHom hJ hβ hm
  have hqI : (P.q₁ s : 𝓞 E) ∈ I := (hI ▸ Ideal.mul_le_left) hq
  have hI0 : (I : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.mpr fun h ↦ ?_
    rw [h, Ideal.mem_bot] at hqI
    exact (Nat.cast_ne_zero.mpr (P.q₁_pos s).ne') hqI
  refine ⟨I, hsupport, ?_, ?_, ?_⟩
  · rw [← inv_one, FractionalIdeal.inv_le_inv_iff (by simp) hI0]
    exact FractionalIdeal.coeIdeal_le_one
  · rw [mul_inv_le_iff₀ (bot_lt_iff_ne_bot.mpr hI0), one_mul, ← map_natCast
      (algebraMap (𝓞 E) E), ← FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_le_coeIdeal, span_singleton_le_iff_mem]
    exact hqI
  · have h := congrArg (fun L : Ideal (𝓞 E) ↦ (L : FractionalIdeal (𝓞 E)⁰ E)) hI
    rw [FractionalIdeal.coeIdeal_mul] at h
    rw [hD, FractionalIdeal.coeIdeal_mul, ← h, FractionalIdeal.coeIdeal_span_singleton,
      mul_inv, mul_inv, FractionalIdeal.spanSingleton_inv, mul_assoc]

end TauCeti.OneSidedBound
