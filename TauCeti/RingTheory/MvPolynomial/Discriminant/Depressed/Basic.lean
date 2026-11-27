/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Monic.GenericDepressed
public import TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed.Basic
public import TauCeti.RingTheory.Polynomial.Resultant.WeightedHomogeneous

import Mathlib.Tactic.LinearCombination

/-!
# Additional properties of the generic depressed discriminant

This file complements `TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed.Basic` with algebra
specialization (`TauCeti.aeval_depressedDiscr`, `Polynomial.Monic.discr_eq_aeval_depressedDiscr`),
general monoid-valued weighted homogeneity (`TauCeti.depressedDiscr_mem_smul`), and explicit
formulas in degrees `0`, `1`, and `4` as well as reductions when `2 = 0` or `3 = 0`.

## Main results

* `TauCeti.aeval_depressedDiscr`, `Polynomial.Monic.discr_eq_aeval_depressedDiscr`: algebra
  evaluation of `depressedDiscr R m`.
* `TauCeti.depressedDiscr_mem_smul`: the discriminant is weighted homogeneous of weight
  `(m * (m - 1)) • u` in any additive commutative monoid.
* `TauCeti.depressedDiscr_zero`, `TauCeti.depressedDiscr_one`, `TauCeti.depressedDiscr_four`,
  `TauCeti.depressedDiscr_two_of_two_eq_zero`, `TauCeti.depressedDiscr_three_of_three_eq_zero`:
  explicit discriminants in degrees `0`, `1`, and `4` and reductions when `2 = 0` or `3 = 0`.
-/

public section

open Polynomial

namespace TauCeti

/-- Evaluating `TauCeti.depressedDiscr R m` at `a : Fin (m - 1) → S` computes the discriminant of
the specialized depressed polynomial `(genericDepressed R m).map (aeval a)`. -/
theorem aeval_depressedDiscr {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {m : ℕ}
    (a : Fin (m - 1) → S) :
    MvPolynomial.aeval a (depressedDiscr R m) =
      ((genericDepressed R m).map (MvPolynomial.aeval a).toRingHom).discr := by
  have h := (monic_genericDepressed (R := R) (m := m)).discr_map (MvPolynomial.aeval a).toRingHom
  rw [discr_genericDepressed] at h
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h.symm

end TauCeti

namespace Polynomial.Monic

/-- The discriminant of a monic polynomial `p` of degree `m` with vanishing subleading coefficient
over an `R`-algebra `S` is `TauCeti.depressedDiscr R m` evaluated at `aⱼ₊₂ = p.coeff (m - 2 - j)`.
-/
theorem discr_eq_aeval_depressedDiscr {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : S[X]} {m : ℕ} (hp : p.Monic) (hdeg : p.natDegree = m) (hnext : p.nextCoeff = 0) :
    p.discr =
      MvPolynomial.aeval (R := R) (fun j : Fin (m - 1) ↦ p.coeff (m - 2 - j))
        (TauCeti.depressedDiscr R m) := by
  have h := (TauCeti.monic_genericDepressed (R := R) (m := m)).discr_map
    (MvPolynomial.aeval (R := R) fun j : Fin (m - 1) ↦ p.coeff (m - 2 - j)).toRingHom
  rw [hp.map_aeval_genericDepressed hdeg hnext, TauCeti.discr_genericDepressed] at h
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h

end Polynomial.Monic

namespace TauCeti

variable (R : Type*) [CommRing R] (m : ℕ)

/-- **The generic depressed discriminant is isobaric (general monoid weights).** For any element
`u` of an additive commutative monoid `M`, the discriminant of `Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` is
weighted homogeneous of weight `(m * (m - 1)) • u` when `aⱼ` is given weight `j • u`. -/
theorem depressedDiscr_mem_smul {M : Type*} [AddCommMonoid M] (u : M) :
    depressedDiscr R m ∈
      MvPolynomial.weightedHomogeneousSubmodule R (fun j : Fin (m - 1) ↦ ((j : ℕ) + 2) • u)
        ((m * (m - 1)) • u) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (depressedDiscr R m) 0]
    exact zero_mem _
  rw [← discr_genericDepressed, MvPolynomial.mem_weightedHomogeneousSubmodule]
  have h := isWeightedHomogeneous_discr_smul u (p := genericDepressed R m) fun i ↦ by
    rw [natDegree_genericDepressed]
    have hi := (isWeightedHomogeneous_coeff_genericDepressed (R := R) (m := m) i).comp_weight
      (multiplesHom M u)
    simpa [Function.comp_def, multiplesHom_apply] using hi
  rwa [natDegree_genericDepressed] at h

/-- For `m = 0`, `TauCeti.depressedDiscr R 0` is `1`. -/
@[simp]
theorem depressedDiscr_zero (R : Type*) [CommRing R] :
    depressedDiscr R 0 = 1 := by
  rw [← discr_genericDepressed, genericDepressed_zero]
  simpa only [Polynomial.C_1] using Polynomial.discr_C (1 : MvPolynomial (Fin 0) R)

/-- For `m = 1`, `TauCeti.depressedDiscr R 1` is `1`. -/
@[simp]
theorem depressedDiscr_one (R : Type*) [CommRing R] :
    depressedDiscr R 1 = 1 := by
  rw [← discr_genericDepressed, genericDepressed_one, discr_X]

/-- For `m = 4`, the discriminant of `X ^ 4 + a₂ X ^ 2 + a₃ X + a₄`. -/
theorem depressedDiscr_four (R : Type*) [CommRing R] :
    depressedDiscr R 4 =
      256 * MvPolynomial.X 2 ^ 3 - 128 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 ^ 2 +
        144 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 -
        27 * MvPolynomial.X 1 ^ 4 + 16 * MvPolynomial.X 0 ^ 4 * MvPolynomial.X 2 -
        4 * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 2 := by
  rw [← discr_genericDepressed, genericDepressed_four, discr_depressedQuartic]

/-- When `(2 : R) = 0`, `depressedDiscr R 2` vanishes identically. -/
theorem depressedDiscr_two_of_two_eq_zero {R : Type*} [CommRing R] (h2 : (2 : R) = 0) :
    depressedDiscr R 2 = 0 := by
  rw [depressedDiscr_two]
  have h2' : (2 : MvPolynomial (Fin 1) R) = 0 := by
    rw [← map_ofNat MvPolynomial.C 2, h2, map_zero]
  linear_combination -2 * MvPolynomial.X 0 * h2'

/-- When `(3 : R) = 0`, `depressedDiscr R 3` collapses to `-X 0 ^ 3`. -/
theorem depressedDiscr_three_of_three_eq_zero {R : Type*} [CommRing R] (h3 : (3 : R) = 0) :
    depressedDiscr R 3 = -MvPolynomial.X 0 ^ 3 := by
  rw [depressedDiscr_three]
  have h3' : (3 : MvPolynomial (Fin 2) R) = 0 := by
    rw [← map_ofNat MvPolynomial.C 3, h3, map_zero]
  linear_combination (-MvPolynomial.X 0 ^ 3 - 9 * MvPolynomial.X 1 ^ 2) * h3'

end TauCeti
