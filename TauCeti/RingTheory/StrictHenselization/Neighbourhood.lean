/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# Pointed étale neighbourhoods

Étale algebras with a map to a fixed commutative algebra form the indexing category for strict
henselization. Localizing a neighbourhood at an element whose point is a unit gives a
refinement in which that element is a unit. A monic polynomial with a simple root at the point
has a root with that same image in a further neighbourhood.

For `R : Type u` and `Ω : Type v`, source algebras live in `Type (max u v)`.
The target is lifted to this universe, so the base algebra and tensor-product refinements belong
to the same category even when the base and target have different universes.

## References

* Stacks Project, Tags 04GP and 04GW.
* Mathlib's `StandardEtalePair`, for adjoining a root and inverting its derivative.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`,
  `StrictHenselizationConstruction.lean`, `PointedEtaleNeighborhood`.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti.StrictHenselization

variable (R : Type u) (Ω : Type v) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- An étale algebra equipped with a point valued in the universe lift of `Ω`. -/
def IsPointedNeighbourhood : ObjectProperty (Over (CommAlgCat.of R (ULift.{u} Ω))) :=
  fun point ↦ Algebra.Etale R point.left

/-- The category of pointed étale neighbourhoods. -/
abbrev Neighbourhood := (IsPointedNeighbourhood R Ω).FullSubcategory

/-- The defining property of a pointed neighbourhood. -/
@[simp]
theorem isPointedNeighbourhood_iff (point : Over (CommAlgCat.of R (ULift.{u} Ω))) :
    IsPointedNeighbourhood R Ω point ↔ Algebra.Etale R point.left :=
  Iff.rfl

/-- Pointed neighbourhoods agree when their source algebras and point maps agree. -/
@[ext]
theorem Neighbourhood.ext (first second : Neighbourhood R Ω)
    (hleft : first.obj.left = second.obj.left)
    (hpoint : HEq first.obj.hom.hom second.obj.hom.hom) : first = second := by
  cases first with
  | mk firstObj firstProperty =>
    cases second with
    | mk secondObj secondProperty =>
      cases firstObj with
      | mk firstLeft firstRight firstHom =>
        cases secondObj with
        | mk secondLeft secondRight secondHom =>
          have hright : firstRight = secondRight := Subsingleton.elim _ _
          cases hright
          cases hleft
          have hmap : firstHom.hom = secondHom.hom := eq_of_heq hpoint
          have hhom : firstHom = secondHom := CommAlgCat.hom_ext hmap
          cases hhom
          rfl

/-- A stage element whose point is a unit becomes a unit in a further pointed étale
neighbourhood, obtained by localizing at that element. -/
theorem Neighbourhood.exists_refinement_isUnit (B : Neighbourhood R Ω) (b : B.obj.left)
    (hpoint : IsUnit (B.obj.hom.hom b)) :
    ∃ (target : Neighbourhood R Ω) (refinement : B ⟶ target),
      IsUnit (refinement.hom.left.hom b) := by
  have hetale : Algebra.Etale R B.obj.left := (isPointedNeighbourhood_iff R Ω _).mp B.property
  let localized := Localization.Away b
  let lifted : localized →ₐ[R] ULift.{u} Ω := IsLocalization.Away.liftAlgHom b hpoint
  let target : Neighbourhood R Ω :=
    ⟨Over.mk (CommAlgCat.ofHom lifted),
      (isPointedNeighbourhood_iff R Ω _).mpr (inferInstanceAs (Algebra.Etale R localized))⟩
  let refinementMap : B.obj.left →ₐ[R] localized :=
    IsScalarTower.toAlgHom R B.obj.left localized
  have hrefines : CommAlgCat.ofHom refinementMap ≫ CommAlgCat.ofHom lifted = B.obj.hom := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro element
    exact IsLocalization.Away.lift_eq (S := localized) b hpoint element
  exact ⟨target, ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom refinementMap) hrefines),
    IsLocalization.Away.algebraMap_isUnit (S := localized) b⟩

/-- A simple root at the point of a pointed étale neighbourhood lifts to a root in a further
pointed étale neighbourhood, with exactly the prescribed image under its point. -/
theorem Neighbourhood.exists_refinement_isRoot (B : Neighbourhood R Ω)
    (p : Polynomial B.obj.left) (hp : p.Monic) (a : ULift.{u} Ω)
    (ha : p.eval₂ B.obj.hom.hom.toRingHom a = 0)
    (hderiv : IsUnit (p.derivative.eval₂ B.obj.hom.hom.toRingHom a)) :
    ∃ (C : Neighbourhood R Ω) (f : B ⟶ C) (c : C.obj.left),
      (p.map f.hom.left.hom.toRingHom).IsRoot c ∧ C.obj.hom.hom c = a := by
  -- Adjoin a root and invert the derivative. Its prescribed image supplies the pointing.
  let _ : Algebra B.obj.left (ULift.{u} Ω) := B.obj.hom.hom.toRingHom.toAlgebra
  let P : StandardEtalePair B.obj.left :=
    { f := p, monic_f := hp, g := p.derivative, cond := ⟨1, 0, 1, by simp⟩ }
  have hpoint : P.HasMap a := ⟨ha, hderiv⟩
  let point := P.lift a hpoint
  let _ : Algebra R P.Ring :=
    ((algebraMap B.obj.left P.Ring).comp (algebraMap R B.obj.left)).toAlgebra
  have : IsScalarTower R B.obj.left P.Ring := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R B.obj.left := (isPointedNeighbourhood_iff R Ω _).mp B.property
  have : Algebra.Etale R P.Ring := Algebra.Etale.comp R B.obj.left P.Ring
  let C : Neighbourhood R Ω :=
    ⟨Over.mk (CommAlgCat.ofHom (point.restrictScalars R)),
      (isPointedNeighbourhood_iff R Ω _).mpr
        (inferInstanceAs (Algebra.Etale R P.Ring))⟩
  let inclusion : B.obj.left →ₐ[R] P.Ring := IsScalarTower.toAlgHom R B.obj.left P.Ring
  have hcomm : CommAlgCat.ofHom inclusion ≫ C.obj.hom = B.obj.hom := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro b
    exact point.commutes b
  refine ⟨C, ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom inclusion) hcomm),
    P.X, ?_, P.lift_X a hpoint⟩
  -- Normalize the underlying maps of the full-subcategory and over-category constructors.
  simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def,
    ObjectProperty.homMk, CommAlgCat.hom_ofHom, Over.homMk_left, inclusion,
    IsScalarTower.toAlgHom, P] using
    P.hasMap_X.1

end TauCeti.StrictHenselization
