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
the variable normalization only requires an invertible square root of `q`. The real-algebra
corollary uses the positive square root.
The rational identity also holds over a finite commutative ring carrying a primitive
additive character with values in a characteristic zero domain.

## References

F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*, North-Holland
(1977), Chapter 5, §2; W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*,
Cambridge University Press (2003), §7.2.
-/

public section

namespace TauCeti

open _root_.MvPolynomial

variable {ι : Type*} [Fintype ι]

private theorem aeval_macWilliams_identity
    {p p' : MvPolynomial (Fin 2) ℤ} {m q : ℕ}
    (h : (m : MvPolynomial (Fin 2) ℤ) * p' =
      aeval ![X 0 + (q - 1 : MvPolynomial (Fin 2) ℤ) * X 1, X 0 - X 1] p)
    {A : Type*} [CommRing A] (x y : A) :
    (m : A) * aeval ![x, y] p' = aeval ![x + (q - 1 : A) * y, x - y] p := by
  have hvec : (fun i ↦ aeval ![x, y]
      (![X 0 + (q - 1 : MvPolynomial (Fin 2) ℤ) * X 1, X 0 - X 1] i)) =
      ![x + (q - 1 : A) * y, x - y] := by
    ext i
    fin_cases i <;> simp
  have heval := congrArg (aeval ![x, y]) h
  simpa only [map_mul, map_natCast, aeval_eq_bind₁, aeval_bind₁, hvec] using heval

/-- The rational normalized MacWilliams identity over a finite commutative ring
carrying a primitive additive character into a characteristic zero domain, evaluated
in any commutative `ℚ`-algebra. -/
theorem aeval_weightEnumerator_euclideanDual_of_isPrimitive
    {R S : Type*} [CommRing R] [Finite R] [DecidableEq R]
    [CommRing S] [IsDomain S] [CharZero S] {ψ : AddChar R S}
    (C : Submodule R (ι → R)) (hψ : ψ.IsPrimitive)
    {A : Type*} [CommRing A] [Algebra ℚ A] (x y : A) :
    aeval ![x, y] (Submodule.euclideanDual C : Set (ι → R)).weightEnumerator =
      (Nat.card C : ℚ)⁻¹ •
        aeval ![x + (Nat.card R - 1 : A) * y, x - y] (C : Set (ι → R)).weightEnumerator := by
  rw [eq_inv_smul_iff₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne' : (Nat.card C : ℚ) ≠ 0)]
  simpa only [Algebra.smul_def, map_natCast] using aeval_macWilliams_identity
    (Submodule.natCard_mul_weightEnumerator_euclideanDual_of_isPrimitive hψ C) x y

variable {F : Type*} [Field F] [Finite F] [DecidableEq F]
  (C : Submodule F (ι → F))

/-- The rational normalized MacWilliams identity for a linear code over a finite
field `F` with `q` elements: `W_{C⊥}(x, y) = (1/#C) · W_C(x + (q-1)y, x - y)`.
The variables may lie in any commutative `ℚ`-algebra, including `ℚ[X, Y]`. -/
theorem aeval_weightEnumerator_euclideanDual {A : Type*} [CommRing A] [Algebra ℚ A]
    (x y : A) :
    aeval ![x, y] (Submodule.euclideanDual C : Set (ι → F)).weightEnumerator =
      (Nat.card C : ℚ)⁻¹ •
        aeval ![x + (Nat.card F - 1 : A) * y, x - y] (C : Set (ι → F)).weightEnumerator := by
  rw [eq_inv_smul_iff₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne' : (Nat.card C : ℚ) ≠ 0)]
  simpa only [Algebra.smul_def, map_natCast] using aeval_macWilliams_identity
    (Submodule.natCard_mul_weightEnumerator_euclideanDual C) x y

/-- A self-dual code's weight enumerator is fixed by the MacWilliams substitution
normalized by any invertible square root `s` of the alphabet size, with inverse `t`.
This holds over any commutative ring containing such a square root. -/
theorem aeval_weightEnumerator_normalized_of_eq_euclideanDual_of_mul_self
    {A : Type*} [CommRing A] (hC : C = Submodule.euclideanDual C)
    (s t : A) (hs : s * s = (Nat.card F : A)) (hst : t * s = 1) (x y : A) :
    aeval ![t * (x + (Nat.card F - 1 : A) * y), t * (x - y)]
        (C : Set (ι → F)).weightEnumerator =
      aeval ![x, y] (C : Set (ι → F)).weightEnumerator := by
  have hpow : s ^ Fintype.card ι = (Nat.card C : A) := by
    rw [← Submodule.two_mul_finrank_eq_card_of_eq_euclideanDual hC, pow_mul, pow_two, hs,
      Module.natCard_eq_pow_finrank (K := F) (V := C), Nat.cast_pow]
  have hmac := aeval_macWilliams_identity
    (natCard_mul_weightEnumerator_of_eq_euclideanDual C hC) x y
  rw [← smul_eq_mul t, ← smul_eq_mul t, ← Matrix.smul_vec2,
    aeval_smul_of_isHomogeneous (C : Set (ι → F)).isHomogeneous_weightEnumerator,
    ← hmac, smul_eq_mul, ← mul_assoc, ← hpow, ← mul_pow, hst, one_pow, one_mul]

/-- A self-dual code's weight enumerator is fixed by the normalized MacWilliams
substitution. The variables may lie in any commutative real algebra; in particular
this is an identity in `ℝ[X, Y]`. -/
theorem aeval_weightEnumerator_normalized_of_eq_euclideanDual
    {A : Type*} [CommRing A] [Algebra ℝ A] (hC : C = Submodule.euclideanDual C)
    (x y : A) :
    aeval ![(Real.sqrt (Nat.card F))⁻¹ • (x + (Nat.card F - 1 : A) * y),
        (Real.sqrt (Nat.card F))⁻¹ • (x - y)] (C : Set (ι → F)).weightEnumerator =
      aeval ![x, y] (C : Set (ι → F)).weightEnumerator := by
  have hsqrt : Real.sqrt (Nat.card F) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Nat.card_pos))
  simpa only [Algebra.smul_def] using
    aeval_weightEnumerator_normalized_of_eq_euclideanDual_of_mul_self C hC
      (algebraMap ℝ A (Real.sqrt (Nat.card F)))
      (algebraMap ℝ A ((Real.sqrt (Nat.card F))⁻¹))
      (by rw [← map_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), map_natCast])
      (by rw [← map_mul, inv_mul_cancel₀ hsqrt, map_one]) x y

end TauCeti
