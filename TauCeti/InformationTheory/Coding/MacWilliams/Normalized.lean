/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.MacWilliams.Basic
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

namespace Submodule

open _root_.MvPolynomial

variable {ι : Type*} [Fintype ι]

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
  simpa only [Algebra.smul_def, map_natCast] using TauCeti.aeval_macWilliams_identity
    (natCard_mul_weightEnumerator_euclideanDual_of_isPrimitive hψ C) x y

variable {F : Type*} [Field F] [Finite F] [DecidableEq F]
  (C : Submodule F (ι → F))

/-- The rational normalized MacWilliams identity for a linear code over a finite
field `F` with `q` elements: `W_{C⊥}(x, y) = (1/#C) · W_C(x + (q-1)y, x - y)`.
The variables may lie in any commutative `ℚ`-algebra, including `ℚ[X, Y]`. -/
theorem aeval_weightEnumerator_euclideanDual {A : Type*} [CommRing A] [Algebra ℚ A]
    (x y : A) :
    aeval ![x, y] (Submodule.euclideanDual C : Set (ι → F)).weightEnumerator =
      (Nat.card C : ℚ)⁻¹ •
        aeval ![x + (Nat.card F - 1 : A) * y, x - y] (C : Set (ι → F)).weightEnumerator :=
  aeval_weightEnumerator_euclideanDual_of_isPrimitive C
    (AddChar.FiniteField.primitiveChar F ℚ
      (by simpa [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm)).prim x y

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
    calc
      s ^ Fintype.card ι = (s * s) ^ Module.finrank F C := by
        rw [← Submodule.two_mul_finrank_eq_card_of_eq_euclideanDual hC, pow_mul, pow_two]
      _ = (Nat.card F : A) ^ Module.finrank F C := by rw [hs]
      _ = (Nat.card C : A) := by
        rw [Module.natCard_eq_pow_finrank (K := F) (V := C), Nat.cast_pow]
  have hscale :
      aeval ![t * (x + (Nat.card F - 1 : A) * y), t * (x - y)]
          (C : Set (ι → F)).weightEnumerator =
        t ^ Fintype.card ι *
          aeval ![x + (Nat.card F - 1 : A) * y, x - y]
            (C : Set (ι → F)).weightEnumerator := by
    simpa only [Matrix.smul_vec2, smul_eq_mul] using
      (C : Set (ι → F)).isHomogeneous_weightEnumerator.aeval_smul
        ![x + (Nat.card F - 1 : A) * y, x - y] t
  have hmac := TauCeti.aeval_macWilliams_identity
    (natCard_mul_weightEnumerator_of_eq_euclideanDual C hC) x y
  have hcancel : t ^ Fintype.card ι * (Nat.card C : A) = 1 := by
    calc
      t ^ Fintype.card ι * (Nat.card C : A) = (t * s) ^ Fintype.card ι := by
        rw [← hpow, mul_pow]
      _ = 1 := by simp [hst]
  calc
    _ = t ^ Fintype.card ι *
        aeval ![x + (Nat.card F - 1 : A) * y, x - y]
          (C : Set (ι → F)).weightEnumerator := hscale
    _ = (t ^ Fintype.card ι * (Nat.card C : A)) *
        aeval ![x, y] (C : Set (ι → F)).weightEnumerator := by rw [← hmac, mul_assoc]
    _ = _ := by rw [hcancel, one_mul]

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

end Submodule
