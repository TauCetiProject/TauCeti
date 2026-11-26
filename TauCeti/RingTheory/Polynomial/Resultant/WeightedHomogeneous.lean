/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.Polynomial.Resultant.Normalization

/-!
# Weighted homogeneity of the discriminant

Let `p` be a polynomial of degree `n` whose coefficients are polynomials in variables carrying
natural weights, such that the coefficient of `X ^ i` is weighted homogeneous of weight `n - i`.
This is the weighting of the generic polynomial `X ^ n + c₁ X ^ (n - 1) + ⋯ + cₙ` with `cᵢ` of
weight `i`, the weighting for which a root has weight `1`. Then the discriminant of `p` is
weighted homogeneous of weight `n (n - 1)`.

Substituting `cᵢ ↦ cᵢ T ^ i` turns `p` into `p.scaleRoots T`, whose discriminant is
`T ^ (n (n - 1))` times that of `p` (`Polynomial.discr_scaleRoots`); the coefficient of
`T ^ (n (n - 1))` in the substitution is the weighted homogeneous component of that weight.

## Main results

* `Polynomial.isWeightedHomogeneous_discr`: the discriminant of a polynomial whose coefficient of
  `X ^ i` has weight `natDegree - i` is weighted homogeneous of weight
  `natDegree * (natDegree - 1)`.
-/

public section

namespace Polynomial

variable {σ R : Type*} [CommRing R]

/-- **The discriminant is isobaric.** If the coefficient of `X ^ i` in `p` is weighted homogeneous
of weight `p.natDegree - i` for every `i`, then the discriminant of `p` is weighted homogeneous of
weight `p.natDegree * (p.natDegree - 1)`. -/
theorem isWeightedHomogeneous_discr {w : σ → ℕ} {p : (MvPolynomial σ R)[X]}
    (hp : ∀ i, (p.coeff i).IsWeightedHomogeneous w (p.natDegree - i)) :
    p.discr.IsWeightedHomogeneous w (p.natDegree * (p.natDegree - 1)) := by
  -- The substitution `X i ↦ T ^ w i * X i`, valued in polynomials in `T`.
  let ψ : MvPolynomial σ R →+* (MvPolynomial σ R)[X] :=
    (MvPolynomial.aeval fun i ↦ X ^ w i * C (MvPolynomial.X i)).toRingHom
  have hC : (p.map C).natDegree = p.natDegree := natDegree_map_eq_of_injective C_injective p
  -- It scales the roots of `p` by `T`.
  have hmap : p.map ψ = (p.map C).scaleRoots X := by
    ext i : 2
    rw [coeff_map, coeff_scaleRoots, coeff_map, hC, mul_comm]
    have hCφ : MvPolynomial.aeval (fun j ↦ C (MvPolynomial.X j)) (p.coeff i) = C (p.coeff i) := by
      conv_rhs => rw [← MvPolynomial.aeval_X_left_apply (p.coeff i)]
      exact (MvPolynomial.comp_aeval_apply _ ((Algebra.ofId _ _).restrictScalars R) _).symm
    rw [← hCφ]
    exact (hp i).aeval_pow_mul X _
  have hdeg : (p.map ψ).natDegree = p.natDegree := by rw [hmap, natDegree_scaleRoots, hC]
  have key : ψ p.discr = C p.discr * X ^ (p.natDegree * (p.natDegree - 1)) := by
    rw [← discr_map_of_natDegree_eq ψ hdeg, hmap, discr_scaleRoots, hC,
      discr_map_of_natDegree_eq C hC, mul_comm]
  -- Read off the coefficient of `T ^ (n (n - 1))`.
  have hcomp : (ψ p.discr).coeff (p.natDegree * (p.natDegree - 1)) =
      MvPolynomial.weightedHomogeneousComponent w (p.natDegree * (p.natDegree - 1)) p.discr := by
    simp_rw [ψ, mul_comm (X ^ _)]
    exact MvPolynomial.coeff_aeval_C_X_mul_X_pow w p.discr _
  rw [key, coeff_C_mul_X_pow, ite_eq_left rfl] at hcomp
  rw [hcomp]
  exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _

end Polynomial
