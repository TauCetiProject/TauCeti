/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
import TauCeti.Algebra.Algebra.Tower

/-!
# Residue degree and ramification index under a change of base ring

Let `R → S → T` be a tower of algebras. An ideal of `T` has the same residue degree over `R` as
over `S` when `algebraMap R S` is bijective, and the same ramification index when that map is
surjective. In particular, statements about two presentations of the same base ring, such as
`ℤ` and the ring of integers of `ℚ`, can be transported into each other.

## Main results

* `Ideal.inertiaDeg_eq_of_bijective`: `r.inertiaDeg S = r.inertiaDeg R`.
* `Ideal.ramificationIdx_eq_of_surjective`: `r.ramificationIdx S = r.ramificationIdx R`.
-/

public section

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T]

/-- An ideal has the same residue degree over `S` as over `R` when `algebraMap R S` is
bijective. -/
theorem inertiaDeg_eq_of_bijective (h : Function.Bijective (algebraMap R S)) (r : Ideal T) :
    r.inertiaDeg S = r.inertiaDeg R := by
  let e := RingEquiv.ofBijective (algebraMap R S) h
  let : Algebra S R := e.symm.toRingHom.toAlgebra
  have : IsScalarTower S R T := .of_algebraMap_rightInverse e.apply_symm_apply
  exact Nat.dvd_antisymm (inertiaDeg_above_dvd (r.under S) r) (inertiaDeg_above_dvd (r.under R) r)

/-- An ideal has the same ramification index over `S` as over `R` when `algebraMap R S` is
surjective. -/
theorem ramificationIdx_eq_of_surjective
    (h : Function.Surjective (algebraMap R S)) (r : Ideal T) :
    r.ramificationIdx S = r.ramificationIdx R := by
  have hm : (r.under R).map (algebraMap R S) = r.under S := by
    rw [← under_under (A := R) (B := S) r]
    exact map_comap_of_surjective _ h _
  by_cases hr : r.IsPrime
  · rw [ramificationIdx_def, ramificationIdx_def,
      IsScalarTower.algebraMap_eq R S (Localization.AtPrime r), ← map_map, hm]
  · rw [ramificationIdx_of_not_isPrime r S hr, ramificationIdx_of_not_isPrime r R hr]

end Ideal
