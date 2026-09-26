/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Binary.Basic
public import TauCeti.InformationTheory.Coding.MacWilliams

/-!
# Weight-enumerator symmetries of binary codes

The weight enumerator of a doubly-even code is invariant under multiplying its second argument
by a fourth root of unity. For a self-dual binary code, the MacWilliams substitution gives
`W_C(X + Y, X - Y) = 2^(n/2) W_C(X, Y)` in `ℤ[X, Y]`. Together these symmetries give the
length restriction for Type II codes.

## Main statements

* `IsDoublyEven.aeval_weightEnumerator_mul_second`: the fourth-root symmetry over any
  commutative ring.
* `aeval_weightEnumerator_add_sub_of_eq_euclideanDual`: the integral self-dual MacWilliams
  symmetry.

See Huffman and Pless, *Fundamentals of Error-Correcting Codes*, Chapters 7 and 9.
-/

public section

namespace TauCeti.BinaryCode

open MvPolynomial

variable {ι : Type*} [Fintype ι] {C : LinearCode (ZMod 2) ι}

/-- The weight enumerator of a doubly-even code is unchanged when its second argument is
multiplied by a fourth root of unity. Taking `R = ℂ[X,Y]` gives the polynomial symmetry. -/
@[simp]
theorem IsDoublyEven.aeval_weightEnumerator_mul_second {R : Type*} [CommRing R]
    (hC : IsDoublyEven C) {ζ : R} (hζ : ζ ^ 4 = 1) (x y : R) :
    aeval ![x, ζ * y] (C : Set (ι → ZMod 2)).weightEnumerator =
      aeval ![x, y] (C : Set (ι → ZMod 2)).weightEnumerator := by
  classical
  rw [Set.weightEnumerator_eq_sum (Set.toFinite _)]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨k, hk⟩ := isDoublyEven_iff.mp hC c (by simpa using hc)
  simp [hk, mul_pow, pow_mul, hζ]

/-- The integral MacWilliams symmetry of a self-dual binary code. -/
theorem aeval_weightEnumerator_add_sub_of_eq_euclideanDual (hC : C = C.euclideanDual) :
    aeval ![X 0 + X 1, X 0 - X 1] (C : Set (ι → ZMod 2)).weightEnumerator =
      (2 : MvPolynomial (Fin 2) ℤ) ^ (Fintype.card ι / 2) *
        (C : Set (ι → ZMod 2)).weightEnumerator := by
  have h := Submodule.aeval_weightEnumerator_of_eq_euclideanDual hC
  norm_num [Nat.card_eq_fintype_card] at h
  exact h

end TauCeti.BinaryCode
