/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic

/-!
# The group functor of formal coordinate changes

For a commutative ring `k`, the formal coordinates `φ = a₁ X + a₂ X² + ⋯`, `a₁` a unit, over a
commutative `k`-algebra `R` form the group `TauCeti.FormalCoordinate R` under composition, and
base change of coefficients along `f : R → S` is a group homomorphism
`TauCeti.FormalCoordinate.map f`. This file packages them as the group functor
`Aut(O) : R ↦ FormalCoordinate R` on commutative `k`-algebras, nonreduced ones included: the
automorphisms of the formal disc preserving its origin. It acts on the loop groups `LG(R)` and
`L⁺G(R)` of an affine group by coordinate changes, and the corresponding semidirect products are
functors of `R` along it.

## Main definitions

* `TauCeti.FormalCoordinate.groupFunctor k`: the group functor `Aut(O)` on `CommAlgCat k`.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge University Press (2007),
  §§3.5.3–3.5.4.
-/

public section

open CategoryTheory

universe u w

namespace TauCeti.FormalCoordinate

variable (k : Type u) [CommRing k]

/-- The group functor `Aut(O) : R ↦ FormalCoordinate R` of formal coordinate changes on
commutative `k`-algebras, acting on morphisms by base change of the coefficients. -/
noncomputable abbrev groupFunctor : CommAlgCat.{w} k ⥤ GrpCat.{w} where
  obj R := GrpCat.of (FormalCoordinate R)
  map f := GrpCat.ofHom (map (f.hom : _ →+* _))
  map_id R := GrpCat.ext fun φ ↦ by simp
  map_comp f g := GrpCat.ext fun φ ↦ FormalCoordinate.ext <| by
    simp [AlgHom.comp_toRingHom, PowerSeries.map_comp]

/-- The group `Aut(O)(R)` is the group of formal coordinates over `R`. -/
lemma groupFunctor_obj (R : CommAlgCat.{w} k) :
    (groupFunctor k).obj R = GrpCat.of (FormalCoordinate R) :=
  (rfl)

/-- A morphism `f : R ⟶ S` acts on `Aut(O)` by applying `f` to the coefficients. -/
lemma groupFunctor_map_apply {R S : CommAlgCat.{w} k} (f : R ⟶ S) (φ : FormalCoordinate R) :
    (groupFunctor k).map f φ = map (f.hom : R →+* S) φ :=
  (rfl)

end TauCeti.FormalCoordinate
