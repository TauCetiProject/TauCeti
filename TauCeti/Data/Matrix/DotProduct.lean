/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Dot product lemmas

A vector indexed by `n` can be transported along an injective map `f : n → m` by extending it by
zero off the range of `f`. Its dot product with any vector indexed by `m` then only sees the
coordinates in the range of `f`. This lets orthogonality on a subset of coordinates be read off
in the ambient coordinate space.

A nonnegative vector paired with strictly positive weights has dot product zero precisely when
the vector is zero.

A ring homomorphism carries the bilinear form `v ⬝ᵥ A *ᵥ w` of a (possibly rectangular) matrix
to the form of the image matrix at the image vectors.

## Main results

* `Function.Injective.dotProduct_extend_zero`: the dot product with a vector extended by zero
  along an injective map is the dot product of the pulled-back vectors.
* `RingHom.map_dotProduct_mulVec`: a ring homomorphism commutes with the bilinear form
  `v ⬝ᵥ A *ᵥ w`.
* `Matrix.intCast_dotProduct_mulVec`: the form of the cast of an integer matrix, at the casts of
  integer vectors, is the cast of the integer value of the form.
* `TauCeti.dotProduct_eq_zero_iff_of_pos`: a nonnegative vector is zero if and only if its pairing
  with strictly positive weights vanishes.
-/

public section

open scoped Matrix

namespace Function.Injective

variable {m n α : Type*} [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring α]

/-- The dot product with a vector extended by zero along an injective map only sees the
coordinates in the range of that map. -/
theorem dotProduct_extend_zero {f : n → m} (hf : f.Injective) (x : m → α) (y : n → α) :
    x ⬝ᵥ f.extend y 0 = (x ∘ f) ⬝ᵥ y := by
  classical
  rw [dotProduct, dotProduct, ← Finset.sum_extend_zero_of_injective _ hf fun _ ↦ Finset.mem_univ _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases em (∃ k, f k = i) with ⟨k, rfl⟩ | hi
  · simp [hf.extend_apply]
  · simp [extend_apply' _ _ _ hi]

end Function.Injective

namespace RingHom

variable {m n R S : Type*} [Fintype m] [Fintype n] [NonAssocSemiring R] [NonAssocSemiring S]

/-- A ring homomorphism `f` carries the bilinear form `v ⬝ᵥ A *ᵥ w` of a matrix `A` to the form of
`A.map f` at `f ∘ v` and `f ∘ w`. -/
theorem map_dotProduct_mulVec (f : R →+* S) (A : Matrix m n R) (v : m → R) (w : n → R) :
    f (v ⬝ᵥ A *ᵥ w) = (f ∘ v) ⬝ᵥ A.map f *ᵥ (f ∘ w) := by
  simp only [f.map_dotProduct, Function.comp_def, f.map_mulVec]

end RingHom

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The form of the cast of an integer matrix, at the casts of integer vectors, is the cast of the
integer value of the form. -/
theorem intCast_dotProduct_mulVec {R : Type*} [NonAssocRing R] (A : Matrix m n ℤ) (v : m → ℤ)
    (w : n → ℤ) :
    (fun i ↦ (v i : R)) ⬝ᵥ A.map (Int.cast : ℤ → R) *ᵥ (fun i ↦ (w i : R)) =
      ((v ⬝ᵥ A *ᵥ w : ℤ) : R) :=
  ((Int.castRingHom R).map_dotProduct_mulVec A v w).symm

end Matrix

namespace TauCeti

/-- For a vector `c` of strictly positive weights and a nonnegative vector `x`, the pairing
`c ⬝ᵥ x` vanishes only when `x` does. -/
@[simp]
theorem dotProduct_eq_zero_iff_of_pos {ι R : Type*} [Fintype ι] [NonUnitalNonAssocSemiring R]
    [PartialOrder R] [IsOrderedAddMonoid R] [PosMulMono R] [NoZeroDivisors R]
    {c x : ι → R} (hc : ∀ i, 0 < c i) (hx : 0 ≤ x) :
    c ⬝ᵥ x = 0 ↔ x = 0 := by
  simp [dotProduct, Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ mul_nonneg (hc j).le (hx j),
    (hc _).ne', funext_iff]

end TauCeti
