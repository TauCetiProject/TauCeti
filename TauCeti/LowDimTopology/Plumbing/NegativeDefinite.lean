/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Tactic.Linarith
public import TauCeti.LowDimTopology.Plumbing.IntersectionForm

/-!
# Negative-definiteness of the plumbing intersection form

This file records what the negative-definiteness hypothesis buys at the level of the integral
intersection form, rather than only at the level of its matrix. Lattice homology is built on a
*negative-definite* plumbing, and the property used throughout the theory is that the form is
strictly negative on every nonzero lattice vector — equivalently that it is nondegenerate, so
the plumbing lattice carries no isotropic directions and the lattice points it indexes are
separated by the form.

The matrix-level definition `PlumbingGraph.IsNegativeDefinite` says that the negated intersection
matrix is positive definite, i.e. `0 < xᵀ (-A) x` for every nonzero integer vector `x`. Here we
transport that statement through `Matrix.toBilin'` to the bilinear form
`PlumbingGraph.intersectionForm`, obtaining the self-pairing sign, the resulting vanishing
criterion, nondegeneracy, and the injectivity of multiplication by the intersection matrix. As a
self-validating example the `A₂` plumbing (two `-2`-framed spheres joined by an edge) is shown to
be negative definite.

## Main results

* `TauCeti.PlumbingGraph.intersectionForm_self_eq_dotProduct`: the self-pairing of the
  intersection form is `x ⬝ᵥ A *ᵥ x`, the bilinear-form reading of the intersection matrix.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.intersectionForm_self_neg`: the intersection form is
  strictly negative on every nonzero lattice vector.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.intersectionForm_self_nonpos`: the self-pairing is
  always nonpositive.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.intersectionForm_self_eq_zero_iff`: the self-pairing
  vanishes exactly at the origin.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.eq_zero_of_intersectionForm_left`: the form is
  nondegenerate — a vector pairing to zero with everything is zero.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.mulVec_injective`: multiplication by the intersection
  matrix is injective, so the lattice embeds along the form.
* `TauCeti.a2Plumbing_isNegativeDefinite`: the `A₂` plumbing is negative definite.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose standing hypothesis is a negative-definite plumbing: Némethi's
lattice homology `ℍ⁻`/`ℍ⁰` and its weight functions are defined on, and finite because of, the
negative-definite intersection lattice. See Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

open scoped Matrix

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {P : PlumbingGraph V}

/-- The self-pairing of the intersection form is the matrix self-pairing `x ⬝ᵥ A *ᵥ x`. This is
the `Matrix.toBilin'` reading of `intersectionMatrix`, the form through which the matrix-level
negative-definiteness hypothesis is transported. -/
theorem intersectionForm_self_eq_dotProduct (x : V → ℤ) :
    P.intersectionForm x x = x ⬝ᵥ P.intersectionMatrix *ᵥ x := by
  simp only [P.intersectionForm_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc]

/-- On a negative-definite plumbing the intersection form is strictly negative on every nonzero
lattice vector: the defining inequality `0 < xᵀ (-A) x` of the negated matrix is exactly
`P.intersectionForm x x < 0`. -/
theorem IsNegativeDefinite.intersectionForm_self_neg (h : P.IsNegativeDefinite) {x : V → ℤ}
    (hx : x ≠ 0) : P.intersectionForm x x < 0 := by
  have hpos := Matrix.PosDef.dotProduct_mulVec_pos h hx
  rw [Matrix.neg_mulVec, dotProduct_neg, star_trivial] at hpos
  rw [intersectionForm_self_eq_dotProduct]
  linarith

/-- On a negative-definite plumbing the intersection form self-pairing is always nonpositive: it
is strictly negative away from the origin and zero at it. -/
theorem IsNegativeDefinite.intersectionForm_self_nonpos (h : P.IsNegativeDefinite) (x : V → ℤ) :
    P.intersectionForm x x ≤ 0 := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (h.intersectionForm_self_neg hx).le

/-- On a negative-definite plumbing the intersection form self-pairing vanishes exactly at the
origin: negative-definiteness rules out nonzero isotropic vectors. -/
theorem IsNegativeDefinite.intersectionForm_self_eq_zero_iff (h : P.IsNegativeDefinite)
    (x : V → ℤ) : P.intersectionForm x x = 0 ↔ x = 0 := by
  refine ⟨fun hzero => ?_, ?_⟩
  · by_contra hx
    exact (h.intersectionForm_self_neg hx).ne hzero
  · rintro rfl
    simp

/-- The intersection form of a negative-definite plumbing is nondegenerate: a lattice vector that
pairs to zero with every vector — in particular with itself — is zero. -/
theorem IsNegativeDefinite.eq_zero_of_intersectionForm_left (h : P.IsNegativeDefinite) {x : V → ℤ}
    (hx : ∀ y, P.intersectionForm x y = 0) : x = 0 :=
  (h.intersectionForm_self_eq_zero_iff x).mp (hx x)

/-- On a negative-definite plumbing, multiplication by the intersection matrix is injective: the
lattice embeds along its intersection form, with no kernel. -/
theorem IsNegativeDefinite.mulVec_injective (h : P.IsNegativeDefinite) :
    Function.Injective (P.intersectionMatrix *ᵥ ·) := by
  intro x y hxy
  have hxy' : P.intersectionMatrix *ᵥ x = P.intersectionMatrix *ᵥ y := hxy
  have hz : P.intersectionMatrix *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy', sub_self]
  have hzero : P.intersectionForm (x - y) (x - y) = 0 := by
    rw [intersectionForm_self_eq_dotProduct, hz]
    simp
  exact sub_eq_zero.mp ((h.intersectionForm_self_eq_zero_iff (x - y)).mp hzero)

end PlumbingGraph

/-- The `A₂` plumbing is negative definite: its negated intersection matrix is the `A₂` Cartan
matrix `!![2, -1; -1, 2]`, whose quadratic form `2x₀² - 2x₀x₁ + 2x₁² = (x₀ - x₁)² + x₀² + x₁²` is
positive on every nonzero integer vector. A self-validating instance of the negative-definite
hypothesis used in Lane L. -/
theorem a2Plumbing_isNegativeDefinite : a2Plumbing.IsNegativeDefinite := by
  rw [show a2Plumbing.IsNegativeDefinite = (-a2Plumbing.intersectionMatrix).PosDef from rfl,
    Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨(Matrix.isHermitian_iff_isSymm.mpr a2Plumbing.intersectionMatrix_isSymm).neg,
    fun x hx => ?_⟩
  have hconv : star x ⬝ᵥ ((-a2Plumbing.intersectionMatrix) *ᵥ x)
      = -a2Plumbing.intersectionForm x x := by
    rw [Matrix.neg_mulVec, dotProduct_neg, star_trivial,
      ← PlumbingGraph.intersectionForm_self_eq_dotProduct]
  have hIF : a2Plumbing.intersectionForm x x
      = -2 * x 0 ^ 2 + 2 * (x 0 * x 1) - 2 * x 1 ^ 2 := by
    rw [a2Plumbing.intersectionForm_apply, a2Plumbing_intersectionMatrix]
    simp [Fin.sum_univ_two]
    ring
  rw [hconv, hIF]
  have hx2 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hx (funext_iff.mpr (Fin.forall_fin_two.mpr ⟨hcon.1, hcon.2⟩))
  have hsum : 0 < x 0 ^ 2 + x 1 ^ 2 := by
    rcases hx2 with hne | hne
    · have := (sq_nonneg (x 0)).lt_of_ne (Ne.symm (pow_ne_zero 2 hne))
      nlinarith [sq_nonneg (x 1)]
    · have := (sq_nonneg (x 1)).lt_of_ne (Ne.symm (pow_ne_zero 2 hne))
      nlinarith [sq_nonneg (x 0)]
  nlinarith [sq_nonneg (x 0 - x 1), hsum]

end TauCeti
