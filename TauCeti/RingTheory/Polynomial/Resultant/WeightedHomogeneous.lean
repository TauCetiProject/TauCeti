/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.Polynomial.Resultant.Normalization
public import TauCeti.RingTheory.Polynomial.UniversalFactorizationRing

/-!
# Weighted homogeneity of the discriminant

Let `p` be a polynomial of degree `n` whose coefficients are polynomials in variables carrying
weights in an additive commutative monoid `M`, such that the coefficient of `X ^ i` is weighted
homogeneous of weight `(n - i) • u` for a fixed `u : M`. This generalizes the weighting of the
generic polynomial `X ^ n + c₁ X ^ (n - 1) + ⋯ + cₙ` with `cᵢ` of weight `i`, the weighting for
which a root has weight `1`. Then the discriminant of `p` is weighted homogeneous of weight
`(n * (n - 1)) • u`.

In the natural-number case `u = 1`, substituting `cᵢ ↦ cᵢ T ^ i` turns `p` into
`p.scaleRoots T`, whose discriminant is `T ^ (n (n - 1))` times that of `p`
(`Polynomial.discr_scaleRoots`); the coefficient of `T ^ (n (n - 1))` in the substitution is the
weighted homogeneous component of that weight. Pushing the natural weights of the universal
degree-`n` polynomial `Polynomial.freePoly R n` along `multiplesHom M u` and evaluating at the
coefficients of `p` yields the general monoid statement.

## Main results

* `Polynomial.isWeightedHomogeneous_discr_freePoly`: the discriminant of `Polynomial.freePoly R n`
  is weighted homogeneous of weight `n * (n - 1)` when `X i` has weight `n - i`.
* `Polynomial.isWeightedHomogeneous_discr`: the discriminant of a polynomial whose coefficient of
  `X ^ i` has weight `(natDegree - i) • u` is weighted homogeneous of weight
  `(natDegree * (natDegree - 1)) • u`.
-/

public section

namespace Polynomial

variable {σ R : Type*} [CommRing R]

private theorem isWeightedHomogeneous_discr_nat {w : σ → ℕ} {p : (MvPolynomial σ R)[X]}
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

/-- The discriminant of `Polynomial.freePoly R n` is weighted homogeneous of weight `n * (n - 1)`
when the variable `X i` (the coefficient in degree `i`) is given weight `n - i`. -/
theorem isWeightedHomogeneous_discr_freePoly (R : Type*) [CommRing R] (n : ℕ) :
    (freePoly R n).discr.IsWeightedHomogeneous (fun i : Fin (n + 1) ↦ n - (i : ℕ))
      (n * (n - 1)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (freePoly R n).discr 0]
    exact MvPolynomial.isWeightedHomogeneous_zero R _ _
  let w : Fin (n + 1) → ℕ := fun i ↦ n - (i : ℕ)
  have hp : ∀ k, ((freePoly R n).coeff k).IsWeightedHomogeneous w
      ((freePoly R n).natDegree - k) := by
    intro k
    rw [natDegree_freePoly, coeff_freePoly]
    split_ifs with hk
    · exact MvPolynomial.isWeightedHomogeneous_X R w ⟨k, Nat.lt_succ_of_le hk⟩
    · exact MvPolynomial.isWeightedHomogeneous_zero R w (n - k)
  have h := isWeightedHomogeneous_discr_nat hp
  rwa [natDegree_freePoly] at h

/-- **The discriminant is isobaric.** If the coefficient of `X ^ i` in `p` is weighted homogeneous
of weight `(p.natDegree - i) • u` in an additive commutative monoid `M` for every `i`, then the
discriminant of `p` is weighted homogeneous of weight `(p.natDegree * (p.natDegree - 1)) • u`. -/
theorem isWeightedHomogeneous_discr {M : Type*} [AddCommMonoid M] {w : σ → M} (u : M)
    {p : (MvPolynomial σ R)[X]}
    (hp : ∀ i, (p.coeff i).IsWeightedHomogeneous w ((p.natDegree - i) • u)) :
    p.discr.IsWeightedHomogeneous w ((p.natDegree * (p.natDegree - 1)) • u) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim p.discr 0]
    exact MvPolynomial.isWeightedHomogeneous_zero R _ _
  let n := p.natDegree
  have hP_smul : (freePoly R n).discr.IsWeightedHomogeneous
      (fun i : Fin (n + 1) ↦ (n - (i : ℕ)) • u) ((n * (n - 1)) • u) := by
    simpa [Function.comp_def, multiplesHom_apply] using
      (isWeightedHomogeneous_discr_freePoly R n).comp_weight (multiplesHom M u)
  let φ : MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial σ R :=
    MvPolynomial.aeval fun i : Fin (n + 1) ↦ p.coeff i
  have hmap : (freePoly R n).map φ.toRingHom = p := map_aeval_coeff_freePoly le_rfl
  have hdiscr : p.discr = φ (freePoly R n).discr := by
    rw [← hmap, discr_map_of_natDegree_eq φ.toRingHom (by rw [hmap, natDegree_freePoly])]
    rfl
  rw [hdiscr]
  exact hP_smul.aeval fun i ↦ hp i

end Polynomial
