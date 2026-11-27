/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel.Index
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# The index of the upper-triangular congruence subgroup over a Dedekind domain

For a nonzero ideal `I` of finite index in a Dedekind domain, the index of `GL2K0 I` is
`N(I) ∏_{P ∣ I} (1 + 1/N(P))`, where the product runs over the distinct prime divisors.
In particular it computes the Bianchi level index in `GL₂(𝓞 K)` for an imaginary quadratic
field `K`.

The bottom-row description of cosets gives multiplicativity under the Chinese remainder theorem.
Unimodular rows and units both split over the factors of the quotient ring. Localization at
each prime preserves its prime-power quotient. Mathlib supplies these equivalences via
`IsDedekindDomain.quotientEquivPiFactors` and `IsLocalization.AtPrime.equivQuotMaximalIdealPow`.
The local factors are then given by
`GL2K0.index_maximalIdeal_pow`, the discrete valuation ring count of Voight, *Quaternion
Algebras*, §26.4.
-/

public section

open UniqueFactorizationMonoid

namespace TauCeti.GL2K0

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (I : Ideal A) [Finite (A ⧸ I)]

open Classical in
/-- Integral form of the level index. A prime power `Pᵉ` exactly dividing the level contributes
`N(P)^(e-1) (N(P)+1)`. At the unit ideal the product is empty. -/
theorem index_eq_prod_absNorm_pow_mul (hI : I ≠ 0) :
    (GL2K0 I).index = ∏ P ∈ (factors I).toFinset,
      Ideal.absNorm P ^ ((factors I).count P - 1) * (Ideal.absNorm P + 1) := by
  let S := (factors I).toFinset
  have hp (P : S) : Prime (P : Ideal A) := prime_of_factor _ (Multiset.mem_toFinset.mp P.property)
  have (P : S) : (P : Ideal A).IsMaximal := (Ideal.isPrime_of_prime (hp P)).isMaximal (hp P).ne_zero
  let B (P : S) := Localization.AtPrime (P : Ideal A)
  let m (P : S) := IsLocalRing.maximalIdeal (B P)
  let k (P : S) := (factors I).count (P : Ideal A)
  let e : A ⧸ I ≃+* ∀ P : S, B P ⧸ m P ^ k P :=
    (IsDedekindDomain.quotientEquivPiFactors hI).trans (RingEquiv.piCongrRight fun P : S ↦
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow (P : Ideal A) (B P) (k P)).toRingEquiv)
  rw [index_eq_prod_of_quotientEquivPi I (fun P : S ↦ m P ^ k P) e]
  conv_rhs => rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  have hP : Finite (A ⧸ (P : Ideal A)) := Finite.of_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.le_of_dvd
      (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.property))))
  let eP : (A ⧸ (P : Ideal A)) ≃ IsLocalRing.ResidueField (B P) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal (P : Ideal A) (B P)).toEquiv
  have : Finite (IsLocalRing.ResidueField (B P)) := Finite.of_equiv _ eP
  have : IsDiscreteValuationRing (B P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A (hp P).ne_zero _
  have hk : k P ≠ 0 := (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property)).ne'
  rw [index_maximalIdeal_pow hk, Ideal.absNorm_of_ne_bot (by simpa using (hp P).ne_zero),
    Submodule.cardQuot_apply, Nat.card_congr eP]

open Classical in
/-- The index of `Γ₀(I)` is the norm of its level times `∏_{P ∣ I} (1 + 1/N(P))`, where the
product runs over the distinct prime ideal divisors of `I`. -/
theorem index_eq_absNorm_mul_prod {F : Type*} [Semifield F] [CharZero F] (hI : I ≠ 0) :
    ((GL2K0 I).index : F) =
      Ideal.absNorm I * ∏ P ∈ (factors I).toFinset, (1 + (Ideal.absNorm P : F)⁻¹) := by
  have hprod : ∏ P ∈ (factors I).toFinset, P ^ (factors I).count P = I := by
    rw [← Finset.prod_multiset_count, associated_iff_eq.mp (factors_prod hI)]
  have hN : (Ideal.absNorm I : F) =
      ∏ P ∈ (factors I).toFinset, (Ideal.absNorm P : F) ^ (factors I).count P := by
    simpa only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun J : Ideal A ↦ (Ideal.absNorm J : F)) hprod.symm
  have hNI : Ideal.absNorm I ≠ 0 := by
    rw [Ideal.absNorm_of_ne_bot (by simpa using hI), Submodule.cardQuot_apply]
    exact Nat.card_pos.ne'
  rw [index_eq_prod_absNorm_pow_mul I hI, Nat.cast_prod, hN, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P hP ↦ ?_
  have hm := Multiset.mem_toFinset.mp hP
  have hk := (Multiset.count_pos.mpr hm).ne'
  have hq : (Ideal.absNorm P : F) ≠ 0 := Nat.cast_ne_zero.mpr <|
    ne_zero_of_dvd_ne_zero hNI
      (map_dvd Ideal.absNorm (dvd_of_mem_factors hm))
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [← pow_sub_one_mul hk (Ideal.absNorm P : F), mul_assoc]
  congr 1
  rw [mul_add, mul_one, mul_inv_cancel₀ hq]

end TauCeti.GL2K0
