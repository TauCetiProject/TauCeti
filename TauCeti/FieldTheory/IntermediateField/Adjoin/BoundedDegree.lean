/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Separable extensions with bounded element degrees

A separable field extension in which the degrees of all minimal polynomials have a uniform
finite bound is finite-dimensional, with extension degree at most that bound. The separability
hypothesis lets the primitive element theorem turn bounds for individual elements into bounds
for every finite intermediate extension.

The proof uses Mathlib's `IntermediateField.exists_lt_finrank_of_infinite_dimensional` and
`Field.exists_primitive_element`.
-/

public section

namespace Field

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Algebra.IsSeparable F E]

/-- A separable extension with uniformly bounded minimal-polynomial degrees is finite-dimensional.
The separability hypothesis is essential: purely inseparable extensions can have bounded element
degrees and infinite extension degree. -/
theorem finiteDimensional_of_natDegree_minpoly_le (n : ℕ)
    (h : ∀ x : E, (minpoly F x).natDegree ≤ n) : FiniteDimensional F E := by
  by_contra hinf
  obtain ⟨L, hL, hn⟩ :=
    IntermediateField.exists_lt_finrank_of_infinite_dimensional hinf n
  let := hL
  obtain ⟨x, hx⟩ := exists_primitive_element F L
  have hdeg := (primitive_element_iff_minpoly_natDegree_eq F x).mp hx
  have hbound := h (L.val x)
  rw [minpoly.algHom_eq L.val L.val.injective x, hdeg] at hbound
  exact hn.not_ge hbound

/-- In a separable extension, a uniform bound on minimal-polynomial degrees also bounds the
extension degree. -/
theorem finrank_le_of_natDegree_minpoly_le (n : ℕ)
    (h : ∀ x : E, (minpoly F x).natDegree ≤ n) : Module.finrank F E ≤ n := by
  let := finiteDimensional_of_natDegree_minpoly_le F E n h
  obtain ⟨x, hx⟩ := exists_primitive_element F E
  rw [← (primitive_element_iff_minpoly_natDegree_eq F x).mp hx]
  exact h x

end Field
