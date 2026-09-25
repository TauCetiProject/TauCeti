/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.CharacterSum
public import TauCeti.InformationTheory.Coding.Weight.Enumerator
public import TauCeti.InformationTheory.Hamming
public import TauCeti.RingTheory.MvPolynomial.Homogeneous

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

Over a field of characteristic zero the identity can be divided by `#C`, giving the normalized
form `W_{C⊥}(X, Y) = (#C)⁻¹ W_C(X + (q - 1) Y, X - Y)`. For a self-dual code of length `n`,
`#C = q^(n/2)`, so the MacWilliams substitution multiplies `W_C` by `q^(n/2)`. Since `W_C` is
homogeneous of degree `n`, this says that `W_C` is invariant under the normalized transform
`(X, Y) ↦ ((X + (q - 1) Y) / √q, (X - Y) / √q)`.

## Main statements

* `Submodule.sum_addChar_dotProduct_smul_weightMonomial`: the Fourier transform of the weight
  monomial.
* `Submodule.natCard_mul_weightEnumerator_euclideanDual_of_isPrimitive`: the MacWilliams
  identity over a finite commutative ring with a primitive additive character.
* `Submodule.natCard_mul_weightEnumerator_euclideanDual`: the MacWilliams identity over a finite
  field.
* `Submodule.map_weightEnumerator_euclideanDual`: the normalized MacWilliams identity, with
  coefficients in a field of characteristic zero.
* `Submodule.aeval_weightEnumerator_of_eq_euclideanDual`: the integral MacWilliams symmetry
  `W_C(X + (q - 1) Y, X - Y) = q^(n/2) W_C(X, Y)` of a self-dual code.
* `Submodule.aeval_inv_smul_weightEnumerator_of_eq_euclideanDual`: the weight enumerator of a
  self-dual code is invariant under the normalized MacWilliams transform.

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

section Normalized

variable {F : Type*} [Field F] [Finite F] [DecidableEq F]

/-- The MacWilliams substitution commutes with changing the coefficients from `ℤ` to `K`. -/
private theorem aeval_macWilliams_eq_map_aeval (K : Type*) [CommRing K] (q : ℕ)
    (W : MvPolynomial (Fin 2) ℤ) :
    aeval ![X 0 + (q - 1 : MvPolynomial (Fin 2) K) * X 1, X 0 - X 1] W =
      MvPolynomial.map (Int.castRingHom K)
        (aeval ![X 0 + (q - 1 : MvPolynomial (Fin 2) ℤ) * X 1, X 0 - X 1] W) := by
  rw [map_aeval, aeval_eq_eval₂Hom]
  congr 1
  refine ringHom_ext (fun r ↦ by simp) fun i ↦ ?_
  fin_cases i <;> simp

/-- **The normalized MacWilliams identity**: for a linear code `C` over a finite field with `q`
elements, `W_{C⊥}(X, Y) = (#C)⁻¹ W_C(X + (q - 1) Y, X - Y)`, with coefficients in any field `K` of
characteristic zero. -/
theorem map_weightEnumerator_euclideanDual (K : Type*) [Field K] [CharZero K]
    (C : Submodule F (ι → F)) :
    MvPolynomial.map (Int.castRingHom K) (euclideanDual C : Set (ι → F)).weightEnumerator =
      (Nat.card C : K)⁻¹ • aeval ![X 0 + (Nat.card F - 1 : MvPolynomial (Fin 2) K) * X 1, X 0 - X 1]
        (C : Set (ι → F)).weightEnumerator := by
  rw [eq_inv_smul_iff₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), aeval_macWilliams_eq_map_aeval,
    ← natCard_mul_weightEnumerator_euclideanDual, map_mul, map_natCast, smul_eq_C_mul,
    map_natCast]

/-- The weight enumerator of a Euclidean self-dual code over a field with `q` elements is fixed by
the MacWilliams substitution up to the factor `q^(n/2)`, where `n` is the length:
`W_C(X + (q - 1) Y, X - Y) = q^(n/2) W_C(X, Y)` in `ℤ[X, Y]`. -/
theorem aeval_weightEnumerator_of_eq_euclideanDual {C : Submodule F (ι → F)}
    (hC : C = euclideanDual C) :
    aeval ![X 0 + (Nat.card F - 1 : MvPolynomial (Fin 2) ℤ) * X 1, X 0 - X 1]
        (C : Set (ι → F)).weightEnumerator =
      (Nat.card F : MvPolynomial (Fin 2) ℤ) ^ (Fintype.card ι / 2) *
        (C : Set (ι → F)).weightEnumerator := by
  have h := natCard_mul_weightEnumerator_euclideanDual C
  rw [← hC, natCard_of_eq_euclideanDual hC, Nat.cast_pow] at h
  exact h.symm

/-- The weight enumerator of a Euclidean self-dual code over a field with `q` elements is invariant
under the normalized MacWilliams transform `(X, Y) ↦ ((X + (q - 1) Y) / s, (X - Y) / s)`, where
`s` is a square root of `q` in a field `K` of characteristic zero. -/
theorem aeval_inv_smul_weightEnumerator_of_eq_euclideanDual {K : Type*} [Field K] [CharZero K]
    {s : K} (hs : s ^ 2 = Nat.card F) {C : Submodule F (ι → F)} (hC : C = euclideanDual C) :
    aeval ![s⁻¹ • (X 0 + (Nat.card F - 1 : MvPolynomial (Fin 2) K) * X 1), s⁻¹ • (X 0 - X 1)]
        (C : Set (ι → F)).weightEnumerator =
      MvPolynomial.map (Int.castRingHom K) (C : Set (ι → F)).weightEnumerator := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp [eq_comm, Nat.card_pos.ne'] at hs
  -- Since `n = 2k` is even, `s⁻¹ ^ n * q ^ (n / 2) = (s⁻¹ * s) ^ n = 1`.
  have hscalar : s⁻¹ ^ Fintype.card ι * (Nat.card F : K) ^ (Fintype.card ι / 2) = 1 := by
    rw [← two_mul_finrank_eq_card_of_eq_euclideanDual hC, Nat.mul_div_cancel_left _ two_pos, ← hs,
      ← pow_mul, ← mul_pow, inv_mul_cancel₀ hs0, one_pow]
  have hsmul : ![s⁻¹ • (X 0 + (Nat.card F - 1 : MvPolynomial (Fin 2) K) * X 1), s⁻¹ • (X 0 - X 1)] =
      (MvPolynomial.C s⁻¹ : MvPolynomial (Fin 2) K) •
        ![X 0 + (Nat.card F - 1 : MvPolynomial (Fin 2) K) * X 1, X 0 - X 1] := by
    ext1 i
    fin_cases i <;> simp [smul_eq_C_mul, mul_add]
  rw [hsmul, (Set.isHomogeneous_weightEnumerator _).aeval_smul, aeval_macWilliams_eq_map_aeval,
    aeval_weightEnumerator_of_eq_euclideanDual hC, map_mul, map_pow, map_natCast, ← mul_assoc,
    ← map_natCast MvPolynomial.C, ← map_pow, ← map_pow, ← map_mul, hscalar, map_one, one_mul]

end Normalized

end Submodule
