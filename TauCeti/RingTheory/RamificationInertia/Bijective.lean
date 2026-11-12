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
# Residue degree and ramification index under a change of rings

Let `R → S → T` be a tower of algebras. An ideal of `T` has the same residue degree over `R` as
over `S` when `algebraMap R S` is bijective, and the same ramification index when that map is
surjective. In particular, statements about two presentations of the same base ring, such as
`ℤ` and the ring of integers of `ℚ`, can be transported into each other. Dually, the
ramification index of an ideal over `R` is unchanged by an `R`-algebra isomorphism of the ring
containing it, so it does not depend on the chosen model of, say, an integral closure. Along a
flat integral extension `S → T`, each maximal ideal of `S` lies under a maximal ideal of `T`
whose ramification index it divides.

## Main results

* `Ideal.inertiaDeg_eq_of_bijective`: `r.inertiaDeg S = r.inertiaDeg R`.
* `Ideal.ramificationIdx_eq_of_surjective`: `r.ramificationIdx S = r.ramificationIdx R`.
* `Ideal.ramificationIdx_map_algEquiv`: `(P.map e).ramificationIdx R = P.ramificationIdx R` for
  an `R`-algebra isomorphism `e`.
* `Ideal.exists_isMaximal_liesOver_ramificationIdx_dvd`: a maximal ideal `Q` of `S` lies under a
  maximal ideal `P` of `T` with `Q.ramificationIdx R ∣ P.ramificationIdx R`.
-/

public section

namespace Ideal

section ChangeOfBase

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

end ChangeOfBase

/-- The ramification index over `R` is invariant under `R`-algebra isomorphisms: the image of an
ideal `P` under `e : S ≃ₐ[R] T` has the same ramification index over `R` as `P`. -/
theorem ramificationIdx_map_algEquiv {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T) (P : Ideal S) :
    (P.map e).ramificationIdx R = P.ramificationIdx R := by
  by_cases hP : P.IsPrime
  swap
  · rw [ramificationIdx_of_not_isPrime _ _ hP, ramificationIdx_of_not_isPrime]
    intro h
    have := comap_isPrime e (K := P.map e)
    exact hP (by rwa [comap_map_of_bijective _ e.bijective] at this)
  -- View `e` as a flat, bijective `S`-algebra structure on `T`, and apply the tower formula.
  let : Algebra S T := e.toRingHom.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq fun r ↦ (e.commutes r).symm
  have hbij : Function.Bijective (algebraMap S T) := e.bijective
  have : Module.Flat S T :=
    .of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap S T) hbij).symm
  have : (P.map e).LiesOver P := ⟨(comap_map_of_bijective _ hbij).symm⟩
  have : (P.map e).IsPrime := map_isPrime_of_equiv e
  rw [ramificationIdx_tower (q := P), ← ramificationIdx_eq_of_surjective hbij.2,
    ramificationIdx_eq_one (P.map e) T, mul_one]

/-- Going up along a flat integral extension `S → T` keeps track of ramification: every maximal
ideal `Q` of `S` lies under a maximal ideal `P` of `T` whose ramification index over `R` is
divisible by that of `Q`. -/
theorem exists_isMaximal_liesOver_ramificationIdx_dvd (R : Type*) {S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.IsIntegral S T] [FaithfulSMul S T] [Module.Flat S T] (Q : Ideal S) [Q.IsMaximal] :
    ∃ P : Ideal T, P.IsMaximal ∧ P.LiesOver Q ∧ Q.ramificationIdx R ∣ P.ramificationIdx R := by
  obtain ⟨P, _, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := T) Q
  exact ⟨P, ‹_›, ‹_›, ramificationIdx_below_dvd Q P⟩

end Ideal
