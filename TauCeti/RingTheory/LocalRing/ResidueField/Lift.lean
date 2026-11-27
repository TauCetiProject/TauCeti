/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Lifting separable minimal polynomials from the residue field of a local ring

For a local ring `R` and a separable element `α` over `ResidueField R`, the minimal polynomial of
`α` lifts to a monic polynomial over `R` whose reduction has `α` as a simple root. When `S` is a
local `R`-algebra with separable residue extension, every element `a : S` is therefore a simple root
of a polynomial over `R` modulo `maximalIdeal S`.

## Main results

* `TauCeti.IsLocalRing.residue_comp_algebraMap`: reduction modulo the maximal ideals commutes with
  `algebraMap`.
* `TauCeti.IsLocalRing.exists_monic_lifts_minpoly_of_isSeparable`: lifting the minimal polynomial of
  a separable residue class to a monic polynomial over `R`.
* `TauCeti.IsLocalRing.exists_aeval_mem_maximalIdeal_isUnit_aeval_derivative`: a residue class
  separable over `R` is a simple root of a polynomial over `R` modulo the maximal ideal.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti.IsLocalRing

/-- Lifting the minimal polynomial of a separable element `α` over the residue field of a local
ring `R` gives a monic polynomial `p : R[X]` reducing to `minpoly (ResidueField R) α` whose
reduction has `α` as a simple root. -/
theorem exists_monic_lifts_minpoly_of_isSeparable {R Ω : Type*} [CommRing R] [IsLocalRing R]
    [Field Ω] [Algebra (ResidueField R) Ω] (α : Ω) (hsep : IsSeparable (ResidueField R) α) :
    ∃ p : R[X], p.Monic ∧ p.map (residue R) = minpoly (ResidueField R) α ∧
      aeval α (p.map (residue R)) = 0 ∧ aeval α ((derivative p).map (residue R)) ≠ 0 := by
  obtain ⟨p, hp, -, hmonic⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts (f := residue R)
      (minpoly (ResidueField R) α)).mpr fun _ ↦ Ideal.Quotient.mk_surjective _)
    (minpoly.monic hsep.isIntegral)
  have hroot : aeval α (p.map (residue R)) = 0 := by
    rw [hp, minpoly.aeval]
  have hderiv : aeval α ((derivative p).map (residue R)) ≠ 0 := by
    rw [← derivative_map, hp]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  exact ⟨p, hmonic, hp, hroot, hderiv⟩

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- Reduction modulo the maximal ideals commutes with `algebraMap`, as a square of ring
homomorphisms.  This is Mathlib's `IsLocalRing.ResidueField.algebraMap_residue` in the form
`Polynomial.map_aeval_eq_aeval_map` takes. -/
theorem residue_comp_algebraMap :
    (algebraMap (ResidueField R) (ResidueField S)).comp (residue R) =
      (residue S).comp (algebraMap R S) :=
  RingHom.ext fun x => ResidueField.algebraMap_residue x

/-- **A residue class separable over `R` is a simple root of a polynomial over `R`**: some
`g : R[X]` has `g(a) ∈ 𝓂(S)` and `g'(a)` a unit.
This is the input for Newton-style lifts and Taylor expansion at `a`. -/
theorem exists_aeval_mem_maximalIdeal_isUnit_aeval_derivative
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] (a : S) :
    ∃ g : R[X], aeval a g ∈ maximalIdeal S ∧ IsUnit (aeval a (derivative g)) := by
  obtain ⟨g, -, -, hroot, hderiv⟩ := exists_monic_lifts_minpoly_of_isSeparable
    (R := R) (residue S a) (Algebra.IsSeparable.isSeparable _ _)
  refine ⟨g, ?_, ?_⟩
  · rwa [← residue_eq_zero_iff, map_aeval_eq_aeval_map residue_comp_algebraMap]
  · rwa [← residue_ne_zero_iff_isUnit, map_aeval_eq_aeval_map residue_comp_algebraMap]

end TauCeti.IsLocalRing
