/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Unit
public import TauCeti.NumberTheory.NumberField.Cyclotomic.EisensteinPrimary
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootsOfUnity

/-!
# Stickelberger's relation for primary cyclotomic integers

For an odd prime `p` and a primary integer `α` of `ℚ(ζ_p)`, the root-of-unity factor
in Stickelberger's relation is a sign: `Φ((α)) = ±α ^ γ`.

Both the Stickelberger product and the Gauss sum power are primary. The former follows
from Galois invariance and multiplicativity of the primary normalization, and the latter
from `Φ(A) ≡ ±1 (mod p)`. Uniqueness of the primary multiple by a power of `ζ_p` then
removes that power from the root-of-unity factor. This is the normalization needed to
compare the power residue symbols of a primary integer and a rational integer.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4,
  Proposition 4.6 and (24).
* N. Xu, *Reciprocity Laws*, §6, Lemma 6.18 and Proposition 6.19.
-/

public section

open NumberField Ideal UniqueFactorizationMonoid
open TauCeti

namespace IsPrimitiveRoot

variable {p : ℕ} {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- The Stickelberger product of a primary cyclotomic integer is primary. -/
theorem isEisensteinPrimary_stickelbergerProduct [NeZero p] {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) :
    TauCeti.IsEisensteinPrimary hζ.toInteger (TauCeti.stickelbergerProduct p α) := by
  classical
  rw [TauCeti.stickelbergerProduct_def]
  exact TauCeti.IsEisensteinPrimary.prod fun σ _ ↦
    ((hζ.isEisensteinPrimary_smul_iff σ⁻¹).mpr hα).pow _

variable [Fact p.Prime]

/-- The Gauss sum power of an ideal prime to `p` is primary when `p` is odd. -/
theorem isEisensteinPrimary_stickelbergerPhi (hp2 : p ≠ 2) {A : Ideal (𝓞 K)}
    (hA : (absNorm A).Coprime p) :
    TauCeti.IsEisensteinPrimary hζ.toInteger (stickelbergerPhi A p) := by
  have h := stickelbergerPhi_modEq_neg_one_pow hA
  rw [SModEq.sub_mem, mem_span_singleton] at h
  have hd : (hζ.toInteger - 1) ^ 2 ∣
      stickelbergerPhi A p - (-1) ^ (normalizedFactors A).card :=
    ((hζ.toInteger_sub_one_sq_dvd_intCast_iff hp2).mpr (dvd_refl (p : ℤ))).trans
      (by simpa using h)
  apply isEisensteinPrimary_iff.mpr
  refine ⟨?_, (-1 : ℤ) ^ (normalizedFactors A).card, by simpa using hd⟩
  rw [hζ.isCoprime_toInteger_sub_one_iff]
  intro hdiv
  have hsign : hζ.toInteger - 1 ∣ (-1 : 𝓞 K) ^ (normalizedFactors A).card :=
    (dvd_sub_right hdiv).mp ((dvd_pow_self _ two_ne_zero).trans hd)
  exact hζ.zeta_sub_one_prime'.not_isUnit
    (isUnit_of_dvd_unit hsign (isUnit_neg_one.pow _))

/-- **Stickelberger's relation for a primary cyclotomic integer.** The root-of-unity
factor is a sign, rather than an arbitrary power of the primitive root. -/
theorem stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) :
    stickelbergerPhi (span {α}) p = TauCeti.stickelbergerProduct p α ∨
      stickelbergerPhi (span {α}) p = -TauCeti.stickelbergerProduct p α := by
  have hz : algebraMap (𝓞 K) K hζ.toInteger = ζ := hζ.coe_toInteger
  have hN := hζ.absNorm_span_singleton_coprime_of_isEisensteinPrimary hα
  have hΦ := hζ.isEisensteinPrimary_stickelbergerPhi hp2 hN
  have hprod := hζ.isEisensteinPrimary_stickelbergerProduct hα
  obtain ⟨i, hi, he | he⟩ := hζ.exists_stickelbergerPhi_eq_pow_mul_or_neg_pow_mul
    (Fact.out : p.Prime).two_le hN
  · have he' : stickelbergerPhi (span {α}) p = hζ.toInteger ^ i *
        TauCeti.stickelbergerProduct p α := by
      apply RingOfIntegers.coe_injective
      simpa only [map_mul, map_pow, hz] using he
    rw [he'] at hΦ
    have hi0 := (hζ.isEisensteinPrimary_toInteger_pow_mul_iff_eq_zero hp2 hprod hi).mp hΦ
    exact Or.inl (by simpa [hi0] using he')
  · have he' : -stickelbergerPhi (span {α}) p = hζ.toInteger ^ i *
        TauCeti.stickelbergerProduct p α := by
      apply RingOfIntegers.coe_injective
      simpa only [map_neg, map_mul, map_pow, hz, neg_mul, neg_neg] using congrArg Neg.neg he
    have hneg := hΦ.neg
    rw [he'] at hneg
    have hi0 := (hζ.isEisensteinPrimary_toInteger_pow_mul_iff_eq_zero hp2 hprod hi).mp hneg
    exact Or.inr (by simpa [hi0] using congrArg Neg.neg he')

end IsPrimitiveRoot
