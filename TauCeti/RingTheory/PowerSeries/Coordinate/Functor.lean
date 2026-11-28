/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic

/-!
# The group functor of formal coordinate changes

The formal coordinates `φ = a₁ X + a₂ X² + ⋯`, `a₁` a unit, over a commutative ring `R` form the
group `TauCeti.FormalCoordinate R` under composition, and base change of coefficients along a ring
homomorphism `f : R → S` is a group homomorphism `TauCeti.FormalCoordinate.map f`. This file
packages them as the group functor `Aut(O) : R ↦ FormalCoordinate R` on commutative rings,
nonreduced ones included: the automorphisms of the formal disc preserving its origin. Its
restriction to the commutative algebras over a commutative ring `k`, along
`forget₂ (CommAlgCat k) CommRingCat`, acts on the loop groups `LG(R)` and `L⁺G(R)` of an affine
group by coordinate changes, and the corresponding semidirect products are functors of `R` along
it.

## Main definitions

* `TauCeti.FormalCoordinate.groupFunctor`: the group functor `Aut(O)` on `CommRingCat`.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge University Press (2007),
  §§3.5.3–3.5.4.
-/

public section

open CategoryTheory

universe w

namespace TauCeti.FormalCoordinate

/-- The group functor `Aut(O) : R ↦ FormalCoordinate R` of formal coordinate changes on
commutative rings, acting on morphisms by base change of the coefficients. -/
noncomputable abbrev groupFunctor : CommRingCat.{w} ⥤ GrpCat.{w} where
  obj R := GrpCat.of (FormalCoordinate R)
  map f := GrpCat.ofHom (map f.hom)
  map_id R := GrpCat.ext fun φ ↦ by simp
  map_comp f g := GrpCat.ext fun φ ↦ by
    rw [CommRingCat.hom_comp]
    exact map_comp _ _ φ

/-- The group `Aut(O)(R)` is the group of formal coordinates over `R`. -/
lemma groupFunctor_obj (R : CommRingCat.{w}) :
    groupFunctor.obj R = GrpCat.of (FormalCoordinate R) :=
  (rfl)

/-- A morphism `f : R ⟶ S` acts on `Aut(O)` by applying `f` to the coefficients. -/
lemma groupFunctor_map_apply {R S : CommRingCat.{w}} (f : R ⟶ S) (φ : FormalCoordinate R) :
    groupFunctor.map f φ = map f.hom φ :=
  (rfl)

end TauCeti.FormalCoordinate
