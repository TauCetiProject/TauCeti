/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Binary.Basic
public import TauCeti.InformationTheory.Coding.CharacterSum
public import TauCeti.InformationTheory.Hamming

/-!
# The MacWilliams identity

For a linear code `C` of length `n` over a finite field `F` with `q` elements, the MacWilliams
identity expresses the homogeneous weight enumerator of the Euclidean dual through that of `C`:

  `#C · W_{C⊥}(X, Y) = W_C(X + (q - 1) Y, X - Y)`.

It is stated here in this division-free form, as an identity in `ℤ[X, Y]`.

The proof is the classical character-sum argument. Fix a primitive additive character `ψ` of
the alphabet with values in a domain of characteristic zero. The finite Fourier transform of
the weight monomial `X^(n - wt y) Y^(wt y)` factors over the coordinates, and each factor is
`X + (q - 1) Y` or `X - Y` according as the coordinate vanishes, so the transform is
`(X + (q - 1) Y)^(n - wt x) (X - Y)^(wt x)`. Summing over `C` and applying the Poisson
summation formula `Submodule.sum_sum_addChar_dotProduct_smul` gives the identity with
coefficients in the target of `ψ`, which descends to `ℤ`.

The argument only uses the primitive character, so the identity is proved for linear codes over
any finite commutative ring carrying a primitive additive character with values in a
characteristic zero domain, such as `ZMod m`; the finite-field statement is the specialization
to `AddChar.FiniteField.primitiveChar`.

## Main statements

* `Submodule.sum_addChar_dotProduct_smul_weightMonomial`: the Fourier transform of the weight
  monomial.
* `Submodule.natCard_mul_weightEnumerator_euclideanDual_of_isPrimitive`: the MacWilliams
  identity over a finite commutative ring with a primitive additive character.
* `Submodule.natCard_mul_weightEnumerator_euclideanDual`: the MacWilliams identity over a finite
  field.
* `TauCeti.BinaryCode.aeval_weightEnumerator_of_eq_euclideanDual`: the self-dual binary
  specialization `W_C(X + Y, X - Y) = 2^(n/2) W_C(X, Y)` in `ℤ[X, Y]`.

## References

F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*, North-Holland
(1977), Chapter 5, §2, Theorem 1; W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting
Codes*, Cambridge University Press (2003), §7.2, Theorem 7.2.3.
-/

public section

open MvPolynomial Finset

namespace Submodule

variable {ι R S : Type*} [Fintype ι] [CommRing R] [DecidableEq R] [CommRing S] [IsDomain S]
  {ψ : AddChar R S}

/-- The finite Fourier transform of the weight monomial `X^(n - wt y) Y^(wt y)` with respect to
a primitive additive character `ψ` is `(X + (q - 1) Y)^(n - wt x) (X - Y)^(wt x)`, where `q` is
the size of the alphabet. -/
theorem sum_addChar_dotProduct_smul_weightMonomial [DecidableEq ι] [Fintype R]
    (hψ : ψ.IsPrimitive) (x : ι → R) :
    ∑ y : ι → R, ψ (x ⬝ᵥ y) •
        (X 0 ^ (Fintype.card ι - hammingNorm y) * X 1 ^ hammingNorm y : MvPolynomial (Fin 2) S) =
      (X 0 + (Fintype.card R - 1 : MvPolynomial (Fin 2) S) * X 1) ^
          (Fintype.card ι - hammingNorm x) * (X 0 - X 1) ^ hammingNorm x := by
  -- Each coordinate contributes `X + (q - 1) Y` or `X - Y` according as it vanishes.
  have hcoord (b : R) : ∑ a : R, C (ψ (b * a)) * (if a = 0 then X 0 else X 1) =
      if b = 0 then X 0 + (Fintype.card R - 1 : MvPolynomial (Fin 2) S) * X 1
      else X 0 - X 1 := by
    have hsplit (a : R) : C (ψ (b * a)) * (if a = 0 then X 0 else X 1) =
        C (ψ (a * b)) * (X 1 : MvPolynomial (Fin 2) S) + if a = 0 then X 0 - X 1 else 0 := by
      split_ifs with ha <;> simp [ha, mul_comm]
    rw [sum_congr rfl fun a _ ↦ hsplit a, sum_add_distrib, ← sum_mul, ← map_sum,
      AddChar.sum_mulShift b hψ]
    split_ifs <;> simp [map_natCast]; ring
  -- A character turns the dot product into a product over the coordinates.
  have hdot (y : ι → R) : ψ (x ⬝ᵥ y) = ∏ i, ψ (x i * y i) :=
    map_prod ψ.toMonoidHom (fun i ↦ Multiplicative.ofAdd (x i * y i)) univ
  simp_rw [smul_eq_C_mul, ← TauCeti.prod_ite_eq_zero_eq_pow_mul_pow_hammingNorm, hdot, map_prod,
    ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a ↦ C (ψ (x i * a)) * if a = 0 then X 0 else X 1)]
  simp_rw [hcoord]

/-- **The MacWilliams identity** over a finite commutative ring `R` with `q` elements which
carries a primitive additive character with values in a domain of characteristic zero: for a
linear code `C`, `#C · W_{C⊥}(X, Y) = W_C(X + (q - 1) Y, X - Y)` in `ℤ[X, Y]`. -/
theorem natCard_mul_weightEnumerator_euclideanDual_of_isPrimitive [Finite R] [CharZero S]
    (hψ : ψ.IsPrimitive) (C : Submodule R (ι → R)) :
    (Nat.card C : MvPolynomial (Fin 2) ℤ) * (euclideanDual C : Set (ι → R)).weightEnumerator =
      aeval ![X 0 + (Nat.card R - 1 : MvPolynomial (Fin 2) ℤ) * X 1, X 0 - X 1]
        (C : Set (ι → R)).weightEnumerator := by
  classical
  let _ : Fintype R := .ofFinite R
  let _ : Fintype C := .ofFinite C
  let _ : Fintype (euclideanDual C) := .ofFinite _
  apply map_injective (Int.castRingHom S) Int.cast_injective
  rw [Set.weightEnumerator_eq_sum (euclideanDual C : Set (ι → R)).toFinite,
    Set.weightEnumerator_eq_sum (C : Set (ι → R)).toFinite,
    sum_subtype (F := ‹Fintype (euclideanDual C)›) _ fun _ ↦ Set.Finite.mem_toFinset _,
    sum_subtype (F := ‹Fintype C›) _ fun _ ↦ Set.Finite.mem_toFinset _]
  simp only [map_mul, map_natCast, map_sum, map_pow, map_add, map_sub, aeval_X, map_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_one]
  simp_rw [Nat.card_eq_fintype_card, ← sum_addChar_dotProduct_smul_weightMonomial hψ]
  rw [sum_sum_addChar_dotProduct_smul hψ, nsmul_eq_mul]

/-- **The MacWilliams identity**: for a linear code `C` over a finite field `F` with `q`
elements, `#C · W_{C⊥}(X, Y) = W_C(X + (q - 1) Y, X - Y)` in `ℤ[X, Y]`. -/
theorem natCard_mul_weightEnumerator_euclideanDual {F : Type*} [Field F] [Finite F]
    [DecidableEq F] (C : Submodule F (ι → F)) :
    (Nat.card C : MvPolynomial (Fin 2) ℤ) * (euclideanDual C : Set (ι → F)).weightEnumerator =
      aeval ![X 0 + (Nat.card F - 1 : MvPolynomial (Fin 2) ℤ) * X 1, X 0 - X 1]
        (C : Set (ι → F)).weightEnumerator :=
  natCard_mul_weightEnumerator_euclideanDual_of_isPrimitive
    (AddChar.FiniteField.primitiveChar F ℚ
      (by simpa [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm)).prim C

end Submodule

namespace TauCeti.BinaryCode

variable {ι : Type*} [Fintype ι] {C : LinearCode (ZMod 2) ι}

/-- The integral MacWilliams symmetry of a self-dual binary code. -/
theorem aeval_weightEnumerator_of_eq_euclideanDual (hC : C = C.euclideanDual) :
    aeval ![X 0 + X 1, X 0 - X 1] (C : Set (ι → ZMod 2)).weightEnumerator =
      (2 : MvPolynomial (Fin 2) ℤ) ^ (Fintype.card ι / 2) *
        (C : Set (ι → ZMod 2)).weightEnumerator := by
  have h := Submodule.natCard_mul_weightEnumerator_euclideanDual C
  rw [← hC, natCard_of_eq_euclideanDual hC] at h
  norm_num [Nat.card_eq_fintype_card] at h ⊢
  exact h.symm

end TauCeti.BinaryCode
