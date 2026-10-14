/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Orthogonal automorphisms in an orthogonal basis

In an orthogonal basis, polarization against a basis vector extracts its coordinate, and the
reflection in that vector negates just that coordinate. The entries of an orthogonal
automorphism and its inverse satisfy the weighted transpose identity. These formulas connect
the reflection calculus with integrality of matrices over local fields.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §43.
-/

public section

namespace QuadraticMap

open Module TauCeti.QuadraticMap

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  (Q : QuadraticForm R V) (b : Basis ι R V)

/-- Polarization against a vector of an orthogonal basis extracts the corresponding coordinate.
The factor two uses the unhalved polarization. -/
theorem polar_basis_left (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) (i : ι) (x : V) :
    polar Q (b i) x = (2 * Q (b i)) * b.repr x i := by
  classical
  have h : Q.polarBilin (b i) = (2 * Q (b i)) • b.coord i := by
    apply b.ext
    intro j
    by_cases hij : i = j
    · subst j
      simp [polar_self, two_mul]
    · simp [b.coord_apply, hb i j hij |>.polar_eq_zero, hij]
  exact LinearMap.congr_fun h x

/-- Reflection in a vector of an orthogonal basis subtracts twice its coordinate. -/
theorem reflection_basis_apply (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j))
    (i : ι) [Invertible (Q (b i))] (x : V) :
    reflection Q (b i) x = x - (2 * b.repr x i) • b i := by
  rw [TauCeti.QuadraticMap.reflection_apply, polar_basis_left Q b hb]
  congr 2
  calc
    ⅟(Q (b i)) * (2 * Q (b i) * b.repr x i) =
        (⅟(Q (b i)) * Q (b i)) * (2 * b.repr x i) := by ring
    _ = 2 * b.repr x i := by simp

/-- The entries of an orthogonal automorphism and its inverse are weighted transposes of one
another, with weights the quadratic values of the orthogonal basis vectors. -/
theorem basis_value_mul_repr_orthogonal_eq_basis_value_mul_repr_inv
    (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j))
    (g : orthogonalGroup Q) (i j : ι) :
    (2 * Q (b i)) * b.repr ((g : V ≃ₗ[R] V) (b j)) i =
      (2 * Q (b j)) * b.repr (((g⁻¹ : orthogonalGroup Q) : V ≃ₗ[R] V) (b i)) j := by
  rw [← polar_basis_left Q b hb, ← polar_basis_left Q b hb, polar_comm]
  have h := polar_apply_of_mem_orthogonalGroup g.2
    (((g⁻¹ : orthogonalGroup Q) : V ≃ₗ[R] V) (b i)) (b j)
  simpa [polar_comm] using h

end QuadraticMap
