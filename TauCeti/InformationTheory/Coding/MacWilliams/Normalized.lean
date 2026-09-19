/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.MacWilliams.Basic
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Real.Sqrt

/-!
# Normalized MacWilliams identities

The weight enumerator of a dual code is the MacWilliams substitution divided by the
cardinality of the code. For a self-dual code over a field of size `q`, homogeneity absorbs
this factor into the variables: the enumerator is fixed by
`(X, Y) ↦ ((X + (q - 1) Y) / √q, (X - Y) / √q)`.

The statements allow values in arbitrary algebras, so they apply to polynomial variables
as well as numerical evaluations. The coefficient normalization is over `ℚ`, whereas
the variable normalization uses `ℝ` to provide the positive square root of `q`.

## References

F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*, North-Holland
(1977), Chapter 5, §2; W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*,
Cambridge University Press (2003), §7.2.
-/

public section

namespace TauCeti

open MvPolynomial

variable {ι F : Type*} [Fintype ι] [Field F] [Finite F] [DecidableEq F]
  {C : Submodule F (ι → F)}

/-- The rational normalized MacWilliams identity, evaluated in any commutative
`ℚ`-algebra. Taking `x` and `y` to be polynomial variables gives the homogeneous
polynomial identity over `ℚ`. -/
theorem aeval_weightEnumerator_euclideanDual {A : Type*} [CommRing A] [Algebra ℚ A]
    (x y : A) :
    aeval ![x, y] (Submodule.euclideanDual C : Set (ι → F)).weightEnumerator =
      (Nat.card C : ℚ)⁻¹ •
        aeval ![x + (Nat.card F - 1 : A) * y, x - y] (C : Set (ι → F)).weightEnumerator := by
  have hcard : (Nat.card C : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [eq_inv_smul_iff₀ hcard]
  have h := congrArg (aeval ![x, y]) (C.natCard_mul_weightEnumerator_euclideanDual)
  simp only [aeval_eq_bind₁, aeval_bind₁, map_mul, map_natCast] at h
  convert h using 1
  · simp [Algebra.smul_def]
  · congr 1
    ext i
    fin_cases i <;> simp

/-- A self-dual code's weight enumerator is fixed by the normalized MacWilliams
substitution. The variables may lie in any commutative real algebra; in particular
this is an identity in `ℝ[X, Y]`. -/
theorem aeval_weightEnumerator_normalized_of_eq_euclideanDual
    {A : Type*} [CommRing A] [Algebra ℝ A] (hC : C = Submodule.euclideanDual C)
    (x y : A) :
    aeval ![(Real.sqrt (Nat.card F))⁻¹ • (x + (Nat.card F - 1 : A) * y),
        (Real.sqrt (Nat.card F))⁻¹ • (x - y)] (C : Set (ι → F)).weightEnumerator =
      aeval ![x, y] (C : Set (ι → F)).weightEnumerator := by
  have hcard : (Nat.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hpow : Real.sqrt (Nat.card F) ^ Fintype.card ι = (Nat.card C : ℝ) := by
    rw [← Submodule.two_mul_finrank_eq_card_of_eq_euclideanDual hC, pow_mul,
      Real.sq_sqrt (Nat.cast_nonneg _),
      Module.natCard_eq_pow_finrank (K := F) (V := C), Nat.cast_pow]
  have h := congrArg (aeval ![x, y]) (C.natCard_mul_weightEnumerator_euclideanDual)
  rw [← hC] at h
  have hmac : aeval ![x + (Nat.card F - 1 : A) * y, x - y]
      (C : Set (ι → F)).weightEnumerator =
        (Nat.card C : ℝ) • aeval ![x, y] (C : Set (ι → F)).weightEnumerator := by
    simp only [aeval_eq_bind₁, aeval_bind₁, map_mul, map_natCast] at h
    convert h.symm using 1
    · congr 1
      ext i
      fin_cases i <;> simp
    · simp [Algebra.smul_def]
  have hscale := eval₂_mul_of_isHomogeneous
    (C : Set (ι → F)).isHomogeneous_weightEnumerator (algebraMap ℤ A)
    ![x + (Nat.card F - 1 : A) * y, x - y]
    (algebraMap ℝ A ((Real.sqrt (Nat.card F))⁻¹))
  simp only [← aeval_def, ← map_pow, inv_pow, hpow, ← Algebra.smul_def] at hscale
  rw [hmac, inv_smul_smul₀ hcard] at hscale
  convert hscale using 1
  congr 1
  ext i
  fin_cases i <;> simp

end TauCeti
