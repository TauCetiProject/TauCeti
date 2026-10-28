/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Algebra
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# The Jacobson radical of the henselization

The ideal extended to the henselization lies in its Jacobson radical. The key fact is
that an element of an étale neighbourhood which is invertible modulo the extended ideal
becomes invertible in the henselization: localizing that neighbourhood at the element is
another neighbourhood. This supplies the radical condition in the definition of a henselian
pair, without assuming that the original ideal lies in the Jacobson radical.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02), construction of
  the henselization of a pair.
-/

public section

open CategoryTheory

universe u

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R]

/-- An element of a neighbourhood which is a unit modulo the extended ideal becomes a unit
in the henselization. -/
theorem isUnit_stage_of_isUnit_quotient (I : Ideal R) (B : Neighbourhood.{u, u} I)
    {b : B.obj} (hb : IsUnit (Ideal.Quotient.mk (I.map (algebraMap R B.obj)) b)) :
    IsUnit (stage I B b) := by
  let C : Neighbourhood.{u, u} I :=
    ⟨CommAlgCat.of R (Localization.Away b),
      isNeighbourhood_localization_of_isNeighbourhood I B.obj B.property hb⟩
  let f : B ⟶ C := ObjectProperty.homMk
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom R B.obj (Localization.Away b)))
  rw [← stage_hom_apply I f b]
  exact (IsLocalization.Away.algebraMap_isUnit b).map (stage I C)

/-- The extension of the original ideal to its henselization is contained in the Jacobson
radical, with no assumption on the original ideal. -/
theorem extended_le_jacobson (I : Ideal R) :
    extended I ≤ Ideal.jacobson (⊥ : Ideal (algebra I)) := by
  rw [extended, Ideal.map_le_iff_le_comap]
  intro r hr
  apply Ideal.mem_jacobson_bot.mpr
  intro y
  obtain ⟨B, b, rfl⟩ := exists_stage_eq I y
  have hr' : Ideal.Quotient.mk (I.map (algebraMap R B.obj)) (algebraMap R B.obj r) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
  have hu : IsUnit (Ideal.Quotient.mk (I.map (algebraMap R B.obj))
      (algebraMap R B.obj r * b + 1)) := by
    simpa only [map_add, map_mul, map_one, hr', zero_mul, zero_add] using
      (isUnit_one : IsUnit (1 : B.obj ⧸ I.map (algebraMap R B.obj)))
  simpa only [map_add, map_mul, map_one, AlgHom.commutes] using
    isUnit_stage_of_isUnit_quotient I B hu

end TauCeti.Henselization
