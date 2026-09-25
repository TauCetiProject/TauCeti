/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Binary.Operations
public import TauCeti.InformationTheory.Coding.Binary.WeightEnumerator
public import TauCeti.InformationTheory.Coding.Duality
public import TauCeti.InformationTheory.Coding.TwoPowTypeII

import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Type II binary codes

A Type II binary code is a doubly-even Euclidean self-dual code. Its length is divisible
by eight. The two weight-enumerator symmetries underlying this restriction are the
MacWilliams substitution and invariance under multiplying the second variable by `I`.
The latter symmetry is stated for any fourth root of unity in a commutative ring, so it
applies both to evaluation at complex numbers and to polynomials with complex coefficients.

A direct sum of binary codes is Type II exactly when both summands are, and the Type II
property is invariant under coordinate permutations. Over the binary field monomial and
semilinear equivalences are coordinate permutations, so it is invariant under these as well.

The argument follows the classical weight-enumerator proof of the length restriction;
see Huffman and Pless, *Fundamentals of Error-Correcting Codes*, Chapter 9.
-/

public section

namespace TauCeti.BinaryCode

open MvPolynomial Complex

variable {ι : Type*} [Fintype ι] {C : LinearCode (ZMod 2) ι}

/-- A Type II binary code is doubly even and Euclidean self-dual. -/
def IsTypeII (C : LinearCode (ZMod 2) ι) : Prop :=
  IsDoublyEven C ∧ C = C.euclideanDual

/-- A doubly-even Euclidean self-dual binary code is Type II. -/
theorem IsDoublyEven.isTypeII (hC : IsDoublyEven C) (hdual : C = C.euclideanDual) :
    IsTypeII C :=
  ⟨hC, hdual⟩

/-- Every Type II code is doubly even. -/
theorem IsTypeII.isDoublyEven (hC : IsTypeII C) : IsDoublyEven C :=
  hC.1

/-- Every Type II code is Euclidean self-dual. -/
theorem IsTypeII.eq_euclideanDual (hC : IsTypeII C) : C = C.euclideanDual :=
  hC.2

/-- Over `ℤ/2 = ℤ/2^1`, the Type II condition for codes over `ℤ/2^r` is the binary Type II
condition: binary Euclidean weights are Hamming weights. -/
theorem _root_.TauCeti.TwoPowCode.isTypeII_one_iff :
    TwoPowCode.IsTypeII 1 C.toAddSubgroup ↔ IsTypeII C := by
  rw [TwoPowCode.isTypeII_iff, IsTypeII, isDoublyEven_iff, and_comm]
  simp

/-! ### Direct sums and equivalences -/

section Operations

variable {κ : Type*} [Fintype κ] {D : LinearCode (ZMod 2) κ}

/-- A direct sum of binary codes is Type II exactly when both summands are Type II. -/
@[simp]
theorem isTypeII_directSum_iff : IsTypeII (C.directSum D) ↔ IsTypeII C ∧ IsTypeII D := by
  simp only [IsTypeII, isDoublyEven_directSum_iff, Submodule.euclideanDual_directSum,
    Submodule.directSum_inj]
  tauto

/-- The direct sum of two Type II binary codes is Type II. -/
theorem IsTypeII.directSum (hC : IsTypeII C) (hD : IsTypeII D) : IsTypeII (C.directSum D) :=
  isTypeII_directSum_iff.mpr ⟨hC, hD⟩

/-- The Type II property of binary codes is invariant under permutation equivalence. -/
theorem isTypeII_iff_of_isPermutationEquivalent (h : IsPermutationEquivalent C D) :
    IsTypeII C ↔ IsTypeII D :=
  and_congr (isDoublyEven_iff_of_isPermutationEquivalent h) h.eq_euclideanDual_iff

/-- Permutation equivalence preserves the Type II property of binary codes. -/
theorem IsTypeII.of_isPermutationEquivalent (hC : IsTypeII C) (h : IsPermutationEquivalent C D) :
    IsTypeII D :=
  (isTypeII_iff_of_isPermutationEquivalent h).mp hC

/-- The Type II property of binary codes is invariant under semilinear, hence also under
monomial, equivalence: over the binary field these are coordinate permutations. -/
theorem isTypeII_iff_of_isSemilinearEquivalent (h : IsSemilinearEquivalent C D) :
    IsTypeII C ↔ IsTypeII D :=
  isTypeII_iff_of_isPermutationEquivalent <| isMonomialEquivalent_iff_isPermutationEquivalent.mp <|
    isSemilinearEquivalent_iff_isMonomialEquivalent.mp h

/-- Semilinear equivalence preserves the Type II property of binary codes. -/
theorem IsTypeII.of_isSemilinearEquivalent (hC : IsTypeII C) (h : IsSemilinearEquivalent C D) :
    IsTypeII D :=
  (isTypeII_iff_of_isSemilinearEquivalent h).mp hC

end Operations

/-- A Type II binary code has length divisible by eight. -/
theorem IsTypeII.eight_dvd_card (hC : IsTypeII C) : 8 ∣ Fintype.card ι := by
  classical
  have hdim := Submodule.two_mul_finrank_eq_card_of_eq_euclideanDual hC.eq_euclideanDual
  have hn : Fintype.card ι = 2 * (Fintype.card ι / 2) := by omega
  have hcard : (Nat.card C : ℂ) = 2 ^ (Fintype.card ι / 2) := by
    rw [Submodule.natCard_of_eq_euclideanDual hC.eq_euclideanDual, Nat.card_zmod, Nat.cast_pow,
      Nat.cast_ofNat]
  have hI : aeval ![1, I] (C : Set (ι → ZMod 2)).weightEnumerator = (Nat.card C : ℂ) := by
    have h := hC.isDoublyEven.aeval_weightEnumerator_mul_second I_pow_four (1 : ℂ) 1
    simpa [aeval_weightEnumerator_diag _ (Set.toFinite _)] using h
  have htransform : aeval ![1 + I, 1 - I] (C : Set (ι → ZMod 2)).weightEnumerator =
      (Nat.card C : ℂ) * (1 + I) ^ Fintype.card ι := by
    have h := hC.isDoublyEven.aeval_weightEnumerator_mul_second
      isPrimitiveRoot_neg_I.pow_eq_one (1 + I) (1 + I)
    have heq : -I * (1 + I) = 1 - I := by linear_combination -I_sq
    simpa only [heq, aeval_weightEnumerator_diag _ (Set.toFinite _),
      SetLike.coe_sort_coe] using h
  -- Evaluate MacWilliams at (1, I), then cancel the nonzero cardinality.
  have hmac := congrArg (aeval ![1, I] : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] ℂ)
    (aeval_weightEnumerator_add_sub_of_eq_euclideanDual hC.eq_euclideanDual)
  rw [comp_aeval_apply] at hmac
  have heval : (fun i ↦ (aeval ![1, I] : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] ℂ)
      (![X 0 + X 1, X 0 - X 1] i)) = ![1 + I, 1 - I] := by
    ext i
    fin_cases i <;> simp
  rw [heval, htransform, map_mul, map_pow, map_ofNat, hI] at hmac
  have hpow : (1 + I) ^ Fintype.card ι = 2 ^ (Fintype.card ι / 2) := by
    have hc0 : (Nat.card C : ℂ) ≠ 0 := by rw [hcard]; exact pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ hc0
    simpa only [mul_comm] using hmac
  -- Since n is even, (1 + I)^n = 2^(n/2) forces I^(n/2) = 1.
  have hsquare : (1 + I) ^ 2 = 2 * I := by linear_combination I_sq
  have hroot : I ^ (Fintype.card ι / 2) = 1 := by
    rw [hn, pow_mul, hsquare, mul_pow] at hpow
    rw [← hn] at hpow
    exact (mul_left_cancel₀ (pow_ne_zero (Fintype.card ι / 2) (by norm_num : (2 : ℂ) ≠ 0)))
      (by simpa using hpow)
  have hfour := isPrimitiveRoot_I.dvd_of_pow_eq_one _ hroot
  omega

end TauCeti.BinaryCode
