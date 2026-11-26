/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.DedekindDomain.Dvr
import TauCeti.LinearAlgebra.Unimodular.Card
import TauCeti.RingTheory.StableRange.Commutative

/-!
# The index of the upper-triangular congruence subgroup

For an ideal `I` of finite index in an infinite Dedekind domain, the index of `GL2K0 I` is
`N(I) ∏_{P ∣ I} (1 + 1/N(P))`, where the product runs over the distinct prime divisors.
In particular it computes the Bianchi level index in `GL₂(𝓞 K)` for an imaginary quadratic
field `K`.

The bottom-row description of cosets gives multiplicativity under the Chinese remainder theorem.
Unimodular rows and units both split over the factors of the quotient ring. Localization at
each prime preserves its prime-power quotient, so the local factors are given by
`GL2K0.index_maximalIdeal_pow`, the discrete valuation ring count of Voight, *Quaternion
Algebras*, §26.4.
-/

public section

open UniqueFactorizationMonoid

namespace TauCeti.GL2K0

variable {A : Type*} [CommRing A] (I : Ideal A) [Finite (A ⧸ I)]

/-- A product decomposition of the finite quotient ring makes the level index the product
of the indices for its factors. The ambient rings of the factors may differ from `A`. -/
theorem index_eq_prod_of_quotientEquivPi {ι : Type*} [Fintype ι] {B : ι → Type*}
    [∀ i, CommRing (B i)] (J : ∀ i, Ideal (B i)) (e : A ⧸ I ≃+* ∀ i, B i ⧸ J i) :
    (GL2K0 I).index = ∏ i, (GL2K0 (J i)).index := by
  have hfin (i : ι) : Finite (B i ⧸ J i) :=
    Finite.of_surjective _ ((Function.surjective_eval i).comp e.surjective)
  have hu : Nat.card (A ⧸ I)ˣ = ∏ i, Nat.card (B i ⧸ J i)ˣ := by
    rw [Nat.card_congr ((Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits).toEquiv, Nat.card_pi]
  have hrows : (GL2K1 I).index = ∏ i, (GL2K1 (J i)).index := by
    rw [GL2K1.index_eq_card I (hasStableRangeLE_one_of_finite_maximalSpectrum _),
      ← TauCeti.Module.card_isUnimodular_congr (Fin 2) e, TauCeti.Module.card_isUnimodular_pi]
    exact Finset.prod_congr rfl fun i _ ↦
      (GL2K1.index_eq_card (J i) (hasStableRangeLE_one_of_finite_maximalSpectrum _)).symm
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (A ⧸ I)ˣ))
  calc
    Nat.card (A ⧸ I)ˣ * (GL2K0 I).index = (GL2K1 I).index := by
      rw [← GL2K1.relIndex_GL2K0_eq_card_units, Subgroup.relIndex_mul_index (GL2K1.le_GL2K0 I)]
    _ = ∏ i, (GL2K1 (J i)).index := hrows
    _ = Nat.card (A ⧸ I)ˣ * ∏ i, (GL2K0 (J i)).index := by
      simp only [hu, ← Finset.prod_mul_distrib, ← GL2K1.relIndex_GL2K0_eq_card_units,
        Subgroup.relIndex_mul_index (GL2K1.le_GL2K0 _)]

variable [IsDedekindDomain A] [Infinite A]

open Classical in
/-- Integral form of the level index. A prime power `Pᵉ` exactly dividing the level contributes
`N(P)^(e-1) (N(P)+1)`. At the unit ideal the product is empty. -/
theorem index_eq_prod_absNorm_pow_mul :
    (GL2K0 I).index = ∏ P ∈ (factors I).toFinset,
      Ideal.absNorm P ^ ((factors I).count P - 1) * (Ideal.absNorm P + 1) := by
  have hI : I ≠ 0 := fun h ↦ (Ideal.absNorm_ne_zero_iff I).mpr ‹_› (by rw [h, map_zero])
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
  rw [index_maximalIdeal_pow hk, Ideal.absNorm_eq_natCard, Nat.card_congr eP]

open Classical in
/-- The index of `Γ₀(I)` is the norm of its level times `∏_{P ∣ I} (1 + 1/N(P))`. -/
theorem index_eq_absNorm_mul_prod {F : Type*} [Semifield F] [CharZero F] :
    ((GL2K0 I).index : F) =
      Ideal.absNorm I * ∏ P ∈ (factors I).toFinset, (1 + (Ideal.absNorm P : F)⁻¹) := by
  have hI : I ≠ 0 := fun h ↦ (Ideal.absNorm_ne_zero_iff I).mpr ‹_› (by rw [h, map_zero])
  have hprod : ∏ P ∈ (factors I).toFinset, P ^ (factors I).count P = I := by
    rw [← Finset.prod_multiset_count, associated_iff_eq.mp (factors_prod hI)]
  have hN : (Ideal.absNorm I : F) =
      ∏ P ∈ (factors I).toFinset, (Ideal.absNorm P : F) ^ (factors I).count P := by
    simpa only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun J : Ideal A ↦ (Ideal.absNorm J : F)) hprod.symm
  rw [index_eq_prod_absNorm_pow_mul, Nat.cast_prod, hN, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P hP ↦ ?_
  have hm := Multiset.mem_toFinset.mp hP
  have hk := (Multiset.count_pos.mpr hm).ne'
  have hq : (Ideal.absNorm P : F) ≠ 0 := Nat.cast_ne_zero.mpr <|
    ne_zero_of_dvd_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr ‹_›)
      (map_dvd Ideal.absNorm (dvd_of_mem_factors hm))
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [← pow_sub_one_mul hk (Ideal.absNorm P : F), mul_assoc]
  congr 1
  rw [mul_add, mul_one, mul_inv_cancel₀ hq]

end TauCeti.GL2K0
