/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.Algebra.Polynomial.Derivative
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
public import TauCeti.RingTheory.PowerSeries.Geometric

/-!
# The reciprocal characteristic polynomial of a symplectic matrix

Let `P` be a `2 g × 2 g` symplectic matrix over a commutative ring, and write
`p (t) = det (1 - t P)` (Mathlib's `Matrix.charpolyRev`). Since `P⁻¹ = J⁻¹ Pᵀ J` and `det P = 1`,
the inverse `P⁻¹` has the same characteristic polynomial as `P`, and `p` coincides with the
characteristic polynomial `det (t - P)`. Hence `p` is self-reciprocal:
`t ^ (2 g) p (1 / t) = p (t)`.

Differentiating this symmetry at `t = 1` gives the reciprocal-polynomial identity
`p' (1) = g det (1 - P)`. If `P` is the action of an orientation-preserving map `φ` of a closed
connected oriented genus-`g` surface on its first cohomology (which preserves the cup product
pairing, hence is symplectic in a symplectic basis), the Lefschetz zeta function of `φ` is
`p (t) / (1 - t) ^ 2`. Its coefficients in degrees `a ≥ 2 g - 1` are therefore
`det (1 - P) (a + 1 - g)`.

## Main results

* `SymplecticGroup.charpoly_inv`: `P⁻¹` and `P` have the same characteristic
  polynomial.
* `SymplecticGroup.charpolyRev_eq_charpoly`: `det (1 - t P) = det (t - P)`.
* `SymplecticGroup.reflect_charpolyRev`: `det (1 - t P)` is self-reciprocal.
* `SymplecticGroup.derivative_eval_one_charpolyRev`: `p' (1) = g det (1 - P)`.
* `SymplecticGroup.coeff_coe_charpolyRev_mul_mk_one_sq`: the coefficient of `t ^ a`
  in `det (1 - t P) / (1 - t) ^ 2` is `det (1 - P) (a + 1 - g)` for `a ≥ 2 g - 1`.
-/

public section

open Matrix Polynomial

namespace SymplecticGroup

variable {l R : Type*} [Fintype l] [DecidableEq l] [CommRing R]

/-- A symplectic matrix and its inverse have the same characteristic polynomial, since
`P⁻¹ = J⁻¹ Pᵀ J`. -/
theorem charpoly_inv {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hA : A ∈ symplecticGroup l R) : A⁻¹.charpoly = A.charpoly := by
  rw [SymplecticGroup.inv_eq_symplectic_inv A hA, charpoly_mul_comm, ← Matrix.mul_assoc,
    Matrix.mul_neg, J_squared, neg_neg, Matrix.one_mul, charpoly_transpose]

/-- For a symplectic matrix `P` the reversed characteristic polynomial `det (1 - t P)` equals the
characteristic polynomial `det (t - P)`. -/
theorem charpolyRev_eq_charpoly {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hA : A ∈ symplecticGroup l R) : A.charpolyRev = A.charpoly := by
  have h := Matrix.charpoly_inv A ((isUnit_iff_isUnit_det A).2 (SymplecticGroup.symplectic_det hA))
  rw [charpoly_inv hA, SymplecticGroup.det_eq_one hA, Ring.inverse_one,
    Fintype.card_sum, ← two_mul, pow_mul] at h
  simpa using h.symm

/-- **Self-reciprocity.** For a `2 g × 2 g` symplectic matrix `P` the polynomial
`p (t) = det (1 - t P)` satisfies `t ^ (2 g) p (1 / t) = p (t)`. -/
theorem reflect_charpolyRev {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hA : A ∈ symplecticGroup l R) :
    A.charpolyRev.reflect (2 * Fintype.card l) = A.charpolyRev := by
  conv_lhs => rw [charpolyRev_eq_charpoly hA]
  rw [charpolyRev_eq_reflect, Fintype.card_sum, two_mul]

/-- **Reciprocal-polynomial identity.** For a `2 g × 2 g` symplectic matrix `P` the polynomial
`p (t) = det (1 - t P)` satisfies `p' (1) = g p (1) = g det (1 - P)`. -/
theorem derivative_eval_one_charpolyRev {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hA : A ∈ symplecticGroup l R) :
    A.charpolyRev.derivative.eval 1 = Fintype.card l * (1 - A).det := by
  rw [← eval_one_charpolyRev]
  refine derivative_eval_one_of_reflect_eq ?_ (reflect_charpolyRev hA)
  simpa [two_mul] using natDegree_charpolyRev_le A

/-- **Coarse coefficients.** For a `2 g × 2 g` symplectic matrix `P`, the coefficient of `t ^ a`
in `det (1 - t P) / (1 - t) ^ 2 = det (1 - t P) (∑ tⁿ) ^ 2` is `det (1 - P) (a + 1 - g)` for every
`a ≥ 2 g - 1`. -/
theorem coeff_coe_charpolyRev_mul_mk_one_sq
    {A : Matrix (l ⊕ l) (l ⊕ l) R} (hA : A ∈ symplecticGroup l R) {a : ℕ}
    (ha : 2 * Fintype.card l ≤ a + 1) :
    PowerSeries.coeff a ((A.charpolyRev : PowerSeries R) * PowerSeries.mk 1 ^ 2) =
      (1 - A).det * (a + 1 - Fintype.card l) := by
  have hdeg : A.charpolyRev.natDegree ≤ a + 1 :=
    (natDegree_charpolyRev_le A).trans (by simpa [two_mul] using ha)
  rw [coeff_coe_mul_mk_one_sq _ hdeg, derivative_eval_one_charpolyRev hA,
    eval_one_charpolyRev]
  ring

end SymplecticGroup
