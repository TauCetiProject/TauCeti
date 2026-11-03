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
henselization. For `R : Type u` and `Ω : Type v`, source algebras live in `Type (max u v)`. The
target is lifted to this universe, so the base algebra and tensor-product refinements belong to
the same category even when the base and target have different universes. The structure map of a
neighbourhood therefore lands in `ULift Ω`, and `Neighbourhood.point` is the corresponding
`R`-algebra map to `Ω`.

Localizing a neighbourhood at an element whose point is a unit gives a refinement in which that
element is a unit. A monic polynomial with a simple root at the point has a root with that same
image in a further neighbourhood.

This file records the underlying `R`-algebra map to `Ω` (`Neighbourhood.point`), constructors
`Neighbourhood.mk'` and `Neighbourhood.homMk'` from algebra maps compatible with the points, an
extensionality lemma for morphisms, and the refinement `Neighbourhood.away` of a neighbourhood by
inverting an element that is a unit at the point.

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

/-- The source algebra of a pointed neighbourhood is étale over the base. -/
instance Neighbourhood.etale (B : Neighbourhood R Ω) : Algebra.Etale R B.obj.left :=
  (isPointedNeighbourhood_iff R Ω B.obj).mp B.property

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

namespace Neighbourhood

variable {R Ω}

/-- The `R`-algebra map to `Ω` underlying the point of a pointed neighbourhood. -/
def point (B : Neighbourhood R Ω) : B.obj.left →ₐ[R] Ω :=
  ULift.algEquiv.toAlgHom.comp B.obj.hom.hom

/-- The point of a neighbourhood is the structure map followed by `ULift.down`. -/
theorem point_apply (B : Neighbourhood R Ω) (x : B.obj.left) :
    B.point x = (B.obj.hom.hom x).down :=
  (rfl)

/-- Morphisms of pointed neighbourhoods are determined by their underlying algebra maps. -/
@[ext]
theorem hom_ext {B C : Neighbourhood R Ω} {f g : B ⟶ C}
    (h : f.hom.left.hom = g.hom.left.hom) : f = g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact CommAlgCat.hom_ext h

/-- Morphisms of pointed neighbourhoods are compatible with the points. -/
@[simp]
theorem point_comp_hom {B C : Neighbourhood R Ω} (f : B ⟶ C) :
    C.point.comp f.hom.left.hom = B.point := by
  ext x
  exact congrArg ULift.down (DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom f.hom.w) x)

/-- The elementwise form of `point_comp_hom`. -/
@[simp]
theorem point_hom_apply {B C : Neighbourhood R Ω} (f : B ⟶ C) (x : B.obj.left) :
    C.point (f.hom.left.hom x) = B.point x :=
  DFunLike.congr_fun (point_comp_hom f) x

/-- The pointed neighbourhood given by an étale `R`-algebra `A` and an `R`-algebra map
`A → Ω`. -/
-- Exposed because the carrier of `mk' A pt` is `A` by definitional unfolding.
@[expose] def mk' (A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (pt : A →ₐ[R] Ω) : Neighbourhood R Ω :=
  ⟨Over.mk (CommAlgCat.ofHom (ULift.algEquiv.symm.toAlgHom.comp pt)),
    (isPointedNeighbourhood_iff R Ω _).2 (by simpa only [Over.mk_left] using ‹Algebra.Etale R A›)⟩

/-- The point of `mk' A pt` is `pt`. -/
@[simp]
theorem point_mk' (A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (pt : A →ₐ[R] Ω) : (mk' A pt).point = pt :=
  (rfl)

/-- A morphism of pointed neighbourhoods given by an algebra map compatible with the points. -/
def homMk' {B C : Neighbourhood R Ω} (f : B.obj.left →ₐ[R] C.obj.left)
    (h : C.point.comp f = B.point) : B ⟶ C :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom f)
    (CommAlgCat.hom_ext (by
      ext x
      exact DFunLike.congr_fun h x)))

/-- The underlying algebra map of `homMk' f h` is `f`. -/
@[simp]
theorem homMk'_hom_left_hom {B C : Neighbourhood R Ω} (f : B.obj.left →ₐ[R] C.obj.left)
    (h : C.point.comp f = B.point) : (homMk' f h).hom.left.hom = f :=
  (rfl)

/-- Inverting an element `y` of a pointed neighbourhood that is a unit at the point gives a
pointed neighbourhood, with the point extended to the localization. -/
-- Exposed because `point_away` and `awayHom` state the carrier is `Localization.Away y`.
@[expose] noncomputable def away (B : Neighbourhood R Ω) (y : B.obj.left)
    (hy : IsUnit (B.point y)) : Neighbourhood R Ω :=
  mk' (Localization.Away y) (IsLocalization.Away.liftAlgHom y (f := B.point) hy)

/-- The point of `away B y hy` extends the point of `B`. -/
@[simp]
theorem point_away (B : Neighbourhood R Ω) (y : B.obj.left) (hy : IsUnit (B.point y)) :
    (away B y hy).point =
      IsLocalization.Away.liftAlgHom (S := Localization.Away y) y (f := B.point) hy :=
  (rfl)

/-- The refinement from a pointed neighbourhood to its inversion at `y`. -/
noncomputable def awayHom (B : Neighbourhood R Ω) (y : B.obj.left)
    (hy : IsUnit (B.point y)) : B ⟶ away B y hy :=
  homMk' (IsScalarTower.toAlgHom R B.obj.left (Localization.Away y)) (by
    rw [point_away]
    ext x
    exact IsLocalization.Away.lift_eq (S := Localization.Away y) _ hy x)

/-- The refinement `awayHom` is the localization map. -/
@[simp]
theorem awayHom_hom_left_hom (B : Neighbourhood R Ω) (y : B.obj.left)
    (hy : IsUnit (B.point y)) :
    (awayHom B y hy).hom.left.hom = IsScalarTower.toAlgHom R B.obj.left (Localization.Away y) :=
  (rfl)

/-- The refinement `awayHom` sends `y` to a unit. -/
theorem isUnit_awayHom (B : Neighbourhood R Ω) (y : B.obj.left) (hy : IsUnit (B.point y)) :
    IsUnit ((awayHom B y hy).hom.left.hom y) := by
  rw [awayHom_hom_left_hom]
  exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away y) y

/-- The universal property of `away`: a morphism `f : B ⟶ C` that sends `y` to a unit factors
through `awayHom B y hy`. -/
noncomputable def awayLift {B C : Neighbourhood R Ω} (y : B.obj.left) (hy : IsUnit (B.point y))
    (f : B ⟶ C) (hf : IsUnit (f.hom.left.hom y)) : away B y hy ⟶ C :=
  homMk' (IsLocalization.Away.liftAlgHom y (f := f.hom.left.hom) hf :
      Localization.Away y →ₐ[R] C.obj.left) (by
    rw [point_away]
    refine Localization.algHom_ext (Submonoid.powers y) ?_
    ext x
    simp only [AlgHom.comp_apply, IsLocalization.Away.coe_liftAlgHom]
    -- `simp` leaves `Algebra.algHom R _ _ x` unreduced to `algebraMap _ _ x`, so `lift_eq` does
    -- not fire; the two forms agree by `rfl`, which the `exact` below uses.
    exact (congrArg C.point (IsLocalization.Away.lift_eq (S := Localization.Away y) y hf x)).trans
      ((point_hom_apply f x).trans
        (IsLocalization.Away.lift_eq (S := Localization.Away y) y hy x).symm))

/-- The underlying algebra map of `awayLift` is the localization lift of the underlying map of
`f`. -/
@[simp]
theorem awayLift_hom_left_hom {B C : Neighbourhood R Ω} (y : B.obj.left)
    (hy : IsUnit (B.point y)) (f : B ⟶ C) (hf : IsUnit (f.hom.left.hom y)) :
    (awayLift y hy f hf).hom.left.hom =
      IsLocalization.Away.liftAlgHom (S := Localization.Away y) y (f := f.hom.left.hom) hf :=
  (rfl)

/-- The factorization `awayLift` composed with `awayHom` is the original morphism. -/
@[simp]
theorem awayHom_comp_awayLift {B C : Neighbourhood R Ω} (y : B.obj.left)
    (hy : IsUnit (B.point y)) (f : B ⟶ C) (hf : IsUnit (f.hom.left.hom y)) :
    awayHom B y hy ≫ awayLift y hy f hf = f := by
  apply hom_ext
  ext x
  exact IsLocalization.Away.lift_eq (S := Localization.Away y) y hf x

/-- Morphisms out of `away B y hy` are determined by their composite with `awayHom`. -/
theorem away_hom_ext {B C : Neighbourhood R Ω} {y : B.obj.left} {hy : IsUnit (B.point y)}
    {g h : away B y hy ⟶ C} (H : awayHom B y hy ≫ g = awayHom B y hy ≫ h) : g = h :=
  hom_ext (Localization.algHom_ext (Submonoid.powers y) (congrArg (fun k => k.hom.left.hom) H))

/-- A stage element whose point is a unit becomes a unit in a further pointed étale
neighbourhood, obtained by localizing at that element. -/
theorem exists_refinement_isUnit (B : Neighbourhood R Ω) (b : B.obj.left)
    (hpoint : IsUnit (B.point b)) :
    ∃ (target : Neighbourhood R Ω) (refinement : B ⟶ target),
      IsUnit (refinement.hom.left.hom b) :=
  ⟨away B b hpoint, awayHom B b hpoint, isUnit_awayHom B b hpoint⟩

end Neighbourhood

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
