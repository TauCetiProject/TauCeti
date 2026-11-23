/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Monic.GenericDepressed
public import TauCeti.RingTheory.Polynomial.Resultant.WeightedHomogeneous

import Mathlib.Tactic.LinearCombination

/-!
# The generic depressed discriminant

The discriminant of `TauCeti.genericDepressed R m = Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` over
`MvPolynomial (Fin (m - 1)) R` is `TauCeti.depressedDiscr R m`. Over every commutative ring `R`,
it commutes with base change (`TauCeti.map_depressedDiscr`), computes the discriminant of any
monic depressed polynomial of degree `m` by specializing the variables to its coefficients
(`Polynomial.Monic.discr_eq_aeval_depressedDiscr`), and is weighted homogeneous of weight
`m * (m - 1)` when `aⱼ` carries weight `j` (`TauCeti.depressedDiscr_mem`). For `m = 2` it is
`-4 a₂`, and for `m = 3` it is `-4 a₂³ - 27 a₃²`.

## Main definitions

* `TauCeti.depressedDiscr R m`: the discriminant of `TauCeti.genericDepressed R m`.

## Main results

* `TauCeti.discr_genericDepressed`, `TauCeti.map_depressedDiscr`, `TauCeti.aeval_depressedDiscr`,
  `Polynomial.Monic.discr_eq_aeval_depressedDiscr`: base change and evaluation of
  `depressedDiscr R m`.
* `TauCeti.depressedDiscr_mem_smul`, `TauCeti.depressedDiscr_mem`: the discriminant is weighted
  homogeneous of weight `(m * (m - 1)) • u` (and `m * (m - 1)` for `depressedWeight m`).
* `TauCeti.depressedDiscr_zero`, `TauCeti.depressedDiscr_one`, `TauCeti.depressedDiscr_two`,
  `TauCeti.depressedDiscr_three`, `TauCeti.depressedDiscr_four`,
  `TauCeti.depressedDiscr_two_of_charTwo`, `TauCeti.depressedDiscr_three_of_charThree`: explicit
  discriminants in degrees `0` through `4` and reductions in characteristics `2` and `3`.
-/

public section

open Polynomial

namespace TauCeti

variable (R : Type*) [CommRing R] (m : ℕ)

/-- The discriminant of the generic depressed polynomial `Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ`, a polynomial in
`a₂, …, aₘ`. -/
noncomputable def depressedDiscr : MvPolynomial (Fin (m - 1)) R :=
  (genericDepressed R m).discr

variable {R m}

/-- `depressedDiscr R m` is the discriminant of the generic depressed polynomial. -/
theorem discr_genericDepressed : (genericDepressed R m).discr = depressedDiscr R m := (rfl)

/-- Mapping the base ring commutes with forming `TauCeti.depressedDiscr`. -/
@[simp]
theorem map_depressedDiscr {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) :
    MvPolynomial.map φ (depressedDiscr R m) = depressedDiscr S m := by
  rw [← discr_genericDepressed, ← (monic_genericDepressed (R := R) (m := m)).discr_map
    (MvPolynomial.map φ), map_map_genericDepressed, discr_genericDepressed]

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
  have h := isWeightedHomogeneous_discr u (p := genericDepressed R m) fun i ↦ by
    rw [natDegree_genericDepressed]
    have hi := (isWeightedHomogeneous_coeff_genericDepressed (R := R) (m := m) i).comp_weight
      (multiplesHom M u)
    simpa [Function.comp_def, multiplesHom_apply] using hi
  rwa [natDegree_genericDepressed] at h

/-- **The generic depressed discriminant is isobaric.** The discriminant of
`Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` is weighted homogeneous of weight `m (m - 1)`, for the weights
`aⱼ ↦ j`. -/
theorem depressedDiscr_mem :
    depressedDiscr R m ∈
      MvPolynomial.weightedHomogeneousSubmodule R (depressedWeight m) (m * (m - 1)) := by
  have h := depressedDiscr_mem_smul R m (1 : ℤ)
  have hw : (fun j : Fin (m - 1) ↦ ((j : ℕ) + 2) • (1 : ℤ)) = depressedWeight m := by
    ext j
    simp
  have hm : ((m * (m - 1)) • (1 : ℤ)) = (m * (m - 1) : ℤ) := by
    rcases m with _ | m <;> simp
  rwa [hw, hm] at h

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

/-- For `m = 2`, the discriminant of `X² + a₂` is `-4 a₂`. -/
theorem depressedDiscr_two : depressedDiscr R 2 = -4 * MvPolynomial.X 0 := by
  nontriviality R
  rw [← discr_genericDepressed, discr_of_degree_eq_two (by rw [degree_genericDepressed,
    Nat.cast_ofNat]), genericDepressed_two]
  simp

/-- For `m = 3`, the discriminant of `X³ + a₂ X + a₃` is `-4 a₂³ - 27 a₃²`. -/
theorem depressedDiscr_three :
    depressedDiscr R 3 = -4 * MvPolynomial.X 0 ^ 3 - 27 * MvPolynomial.X 1 ^ 2 := by
  nontriviality R
  rw [← discr_genericDepressed, discr_of_degree_eq_three (by rw [degree_genericDepressed,
    Nat.cast_ofNat]), genericDepressed_three]
  simp [coeff_X]

/-- For `m = 4`, the discriminant of `X ^ 4 + a₂ X ^ 2 + a₃ X + a₄`. -/
theorem depressedDiscr_four (R : Type*) [CommRing R] :
    depressedDiscr R 4 =
      256 * MvPolynomial.X 2 ^ 3 - 128 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 ^ 2 +
        144 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 -
        27 * MvPolynomial.X 1 ^ 4 + 16 * MvPolynomial.X 0 ^ 4 * MvPolynomial.X 2 -
        4 * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 2 := by
  rw [← discr_genericDepressed, genericDepressed_four, discr_depressedQuartic]

/-- In characteristic `2`, `depressedDiscr R 2` vanishes identically. -/
theorem depressedDiscr_two_of_charTwo (R : Type*) [CommRing R] [CharP R 2] :
    depressedDiscr R 2 = 0 := by
  rw [depressedDiscr_two]
  have h2 : (2 : MvPolynomial (Fin 1) R) = 0 := CharP.ofNat_eq_zero (MvPolynomial (Fin 1) R) 2
  linear_combination -2 * MvPolynomial.X 0 * h2

/-- In characteristic `3`, `depressedDiscr R 3` collapses to `-X 0 ^ 3`. -/
theorem depressedDiscr_three_of_charThree (R : Type*) [CommRing R] [CharP R 3] :
    depressedDiscr R 3 = -MvPolynomial.X 0 ^ 3 := by
  rw [depressedDiscr_three]
  have h3 : (3 : MvPolynomial (Fin 2) R) = 0 := CharP.ofNat_eq_zero (MvPolynomial (Fin 2) R) 3
  linear_combination (-MvPolynomial.X 0 ^ 3 - 9 * MvPolynomial.X 1 ^ 2) * h3

end TauCeti
