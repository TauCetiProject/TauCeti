/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Localization of bundled commutative algebras

For a submonoid `M` of a commutative ring `R`, invert the product of each finite subset of
`M`. Inclusion of finite subsets gives a filtered diagram of principal localizations, whose
colimit is any localization of `R` at `M`. This presentation lets properties stable under
filtered colimits pass from principal localizations to arbitrary localizations.

The construction uses the universal property of localization, through Mathlib's
`IsLocalization.liftAlgHom` and `IsLocalization.algHom_subsingleton`.

In addition, every commutative `R`-algebra `A` localizes at `Algebra.algebraMapSubmonoid A M` to a
commutative `Localization M`-algebra `Localization (Algebra.algebraMapSubmonoid A M)` via
Mathlib's `localizationAlgebra`. On `R`-algebra homomorphisms `f : A →ₐ[R] B`,
`IsLocalization.map` induces a `Localization M`-algebra homomorphism acting as `f` on canonical
numerators, assembling into `CommAlgCat.localizationFunctor M : CommAlgCat R ⥤ CommAlgCat
(Localization M)` and agreeing as an `R`-linear map with the localized module map of `f`
(`CommAlgCat.localizationFunctor_map_toLinearMap`).
-/

public section

open CategoryTheory Limits

universe u v

namespace Submonoid

open CommAlgCat

variable {R : Type u} [CommRing R] (M : Submonoid R)

/-- Morphisms from a localization are unique as morphisms of algebras over the base ring. -/
theorem isLocalization_hom_ext {A B : CommAlgCat.{u} R} [IsLocalization M A]
    (f g : A ⟶ B) : f = g :=
  hom_ext ((IsLocalization.algHom_subsingleton (S := A) (P := B) M).elim _ _)

/-- The diagram which inverts the product of a finite set of denominators. -/
noncomputable def localizationAwayDiagram : Finset M ⥤ CommAlgCat.{u} R where
  obj s := .of R (Localization.Away (∏ x ∈ s, (x : R)))
  map {s t} h := ofHom <| IsLocalization.Away.liftAlgHom (∏ x ∈ s, (x : R))
    (f := Algebra.ofId R (Localization.Away (∏ x ∈ t, (x : R))))
    (IsLocalization.Away.isUnit_of_dvd _
      (Finset.prod_dvd_prod_of_subset s t (fun x : M ↦ (x : R)) (leOfHom h)))
  map_id s := (Submonoid.powers (∏ x ∈ s, (x : R))).isLocalization_hom_ext _ _
  map_comp {s _ _} _ _ := (Submonoid.powers (∏ x ∈ s, (x : R))).isLocalization_hom_ext _ _

/-- Each stage of the principal-localization diagram is the expected localization algebra. -/
@[simp]
theorem localizationAwayDiagram_obj (s : Finset M) :
    (localizationAwayDiagram M).obj s = .of R (Localization.Away (∏ x ∈ s, (x : R))) := (rfl)

/-- A transition map lifts the base map to the larger principal localization. -/
@[simp]
theorem localizationAwayDiagram_map {s t : Finset M} (h : s ⟶ t) :
    eqToHom (localizationAwayDiagram_obj M s).symm ≫
        (localizationAwayDiagram M).map h ≫ eqToHom (localizationAwayDiagram_obj M t) = ofHom
      (IsLocalization.Away.liftAlgHom (∏ x ∈ s, (x : R))
        (f := Algebra.ofId R (Localization.Away (∏ x ∈ t, (x : R))))
        (IsLocalization.Away.isUnit_of_dvd _
          (Finset.prod_dvd_prod_of_subset s t (fun x : M ↦ (x : R)) (leOfHom h)))) := by
  unfold localizationAwayDiagram
  simp

variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The canonical cocone from principal localizations to a localization at all denominators. -/
noncomputable def localizationAwayCocone : Cocone (localizationAwayDiagram M) where
  pt := .of R S
  ι :=
    { app := fun s ↦ ofHom <| IsLocalization.Away.liftAlgHom (∏ x ∈ s, (x : R))
        (f := Algebra.ofId R S)
        (by
          rw [Algebra.ofId_apply, map_prod]
          exact IsUnit.prod_iff.mpr fun x _ ↦ IsLocalization.map_units S x)
      naturality := fun s t h ↦
        (Submonoid.powers (∏ x ∈ s, (x : R))).isLocalization_hom_ext
          (A := .of R (Localization.Away (∏ x ∈ s, (x : R)))) _ _ }

/-- The localization cocone has the specified localization algebra as its apex. -/
@[simp]
theorem localizationAwayCocone_pt : (localizationAwayCocone M S).pt = .of R S := (rfl)

/-- A leg of the localization cocone is the canonical lift to the full localization. -/
@[simp]
theorem localizationAwayCocone_ι_app (s : Finset M) :
    eqToHom (localizationAwayDiagram_obj M s).symm ≫
        (localizationAwayCocone M S).ι.app s ≫ eqToHom (localizationAwayCocone_pt M S) = ofHom
      (IsLocalization.Away.liftAlgHom (∏ x ∈ s, (x : R)) (f := Algebra.ofId R S)
        (by
          rw [Algebra.ofId_apply, map_prod]
          exact IsUnit.prod_iff.mpr fun x _ ↦ IsLocalization.map_units S x)) := by
  unfold localizationAwayCocone localizationAwayDiagram
  simp

/-- Every localization is the filtered colimit of principal localizations indexed by finite
sets of denominators. No finite generation, domain or Noetherian hypothesis is required. -/
noncomputable def localizationAwayCoconeIsColimit : IsColimit (localizationAwayCocone M S) := by
  classical
  refine
    { desc := fun c ↦ ofHom <| IsLocalization.liftAlgHom (M := M)
        (f := Algebra.ofId R c.pt) (fun x ↦ ?_)
      fac := fun c s ↦ ?_
      uniq := fun c m _ ↦ ?_ }
  · have hx : IsUnit (algebraMap R (Localization.Away (∏ y ∈ ({x} : Finset M), (y : R))) x) := by
      simpa using IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (∏ y ∈ ({x} : Finset M), (y : R)))
        (∏ y ∈ ({x} : Finset M), (y : R))
    let f : Localization.Away (∏ y ∈ ({x} : Finset M), (y : R)) →ₐ[R] c.pt :=
      (c.ι.app {x}).hom
    simpa only [Algebra.ofId_apply, AlgHom.commutes] using hx.map f
  · exact (Submonoid.powers (∏ x ∈ s, (x : R))).isLocalization_hom_ext
      (A := .of R (Localization.Away (∏ x ∈ s, (x : R)))) _ _
  · exact M.isLocalization_hom_ext (A := .of R S) _ _

end Submonoid

namespace CommAlgCat

variable {R : Type u} [CommRing R]

/-- The bundled `Localization M`-algebra `Localization (Algebra.algebraMapSubmonoid A M)`
associated with a commutative `R`-algebra `A`. -/
noncomputable abbrev localizationObj (M : Submonoid R) (A : CommAlgCat.{v} R) :
    CommAlgCat.{v} (Localization M) :=
  CommAlgCat.of (Localization M) (Localization (Algebra.algebraMapSubmonoid A M))

private theorem algebraMapSubmonoid_le_comap (M : Submonoid R) {A B : CommAlgCat.{v} R}
    (f : A ⟶ B) :
    Algebra.algebraMapSubmonoid A M ≤
      (Algebra.algebraMapSubmonoid B M).comap f.hom.toRingHom := by
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, hm, by simp⟩

/-- Two morphisms out of `localizationObj M A` in `CommAlgCat (Localization M)` agree once they
agree on canonical numerators from `A`. -/
theorem localizationObj_hom_ext {M : Submonoid R} {A : CommAlgCat.{v} R}
    {B : CommAlgCat.{v} (Localization M)} {f g : localizationObj M A ⟶ B}
    (h : ∀ a : A, f.hom (algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a) =
      g.hom (algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a)) :
    f = g := by
  apply hom_ext
  apply AlgHom.toRingHom_injective
  exact IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid A M) (RingHom.ext h)

/-- The `Localization M`-algebra homomorphism induced by `f : A ⟶ B` in `CommAlgCat R`. -/
noncomputable def localizationMap (M : Submonoid R) {A B : CommAlgCat.{v} R} (f : A ⟶ B) :
    localizationObj M A ⟶ localizationObj M B :=
  CommAlgCat.ofHom
    { toRingHom := IsLocalization.map (S := Localization (Algebra.algebraMapSubmonoid A M))
        (Localization (Algebra.algebraMapSubmonoid B M)) f.hom.toRingHom
        (algebraMapSubmonoid_le_comap M f)
      commutes' := by
        have h : (IsLocalization.map (S := Localization (Algebra.algebraMapSubmonoid A M))
            (Localization (Algebra.algebraMapSubmonoid B M)) f.hom.toRingHom
            (algebraMapSubmonoid_le_comap M f)).comp
              (algebraMap (Localization M) (Localization (Algebra.algebraMapSubmonoid A M))) =
            algebraMap (Localization M) (Localization (Algebra.algebraMapSubmonoid B M)) := by
          apply IsLocalization.ringHom_ext M
          ext x
          simp only [RingHom.comp_apply,
            ← IsScalarTower.algebraMap_apply R (Localization M)
                (Localization (Algebra.algebraMapSubmonoid A M)),
            ← IsScalarTower.algebraMap_apply R (Localization M)
                (Localization (Algebra.algebraMapSubmonoid B M)),
            IsScalarTower.algebraMap_apply R A (Localization (Algebra.algebraMapSubmonoid A M)),
            IsScalarTower.algebraMap_apply R B (Localization (Algebra.algebraMapSubmonoid B M))]
          rw [IsLocalization.map_eq]
          exact congrArg (algebraMap B (Localization (Algebra.algebraMapSubmonoid B M)))
            (f.hom.commutes x)
        exact fun z ↦ congr($h z) }

/-- `localizationMap M f` acts via `f` on canonical numerators `algebraMap A _ a`. -/
@[simp]
theorem localizationMap_hom_algebraMap (M : Submonoid R) {A B : CommAlgCat.{v} R}
    (f : A ⟶ B) (a : A) :
    (localizationMap M f).hom (algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a) =
      algebraMap B (Localization (Algebra.algebraMapSubmonoid B M)) (f.hom a) :=
  IsLocalization.map_eq (algebraMapSubmonoid_le_comap M f) a

private theorem localizationMap_hom_mk' (M : Submonoid R) {A B : CommAlgCat.{v} R}
    (f : A ⟶ B) (a : A) (m : M) :
    (localizationMap M f).hom
        (IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid A M)) a
          ⟨algebraMap R A m, Algebra.mem_algebraMapSubmonoid_of_mem m⟩) =
      IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid B M)) (f.hom a)
        ⟨algebraMap R B m, Algebra.mem_algebraMapSubmonoid_of_mem m⟩ := by
  refine (IsLocalization.map_mk' (S := Localization (Algebra.algebraMapSubmonoid A M))
    (algebraMapSubmonoid_le_comap M f) a
    ⟨algebraMap R A m, Algebra.mem_algebraMapSubmonoid_of_mem m⟩).trans ?_
  congr 1
  ext
  exact f.hom.commutes m

/-- The functor `CommAlgCat R ⥤ CommAlgCat (Localization M)` sending a commutative `R`-algebra `A`
to `Localization (Algebra.algebraMapSubmonoid A M)`. -/
noncomputable def localizationFunctor (M : Submonoid R) :
    CommAlgCat.{v} R ⥤ CommAlgCat.{v} (Localization M) where
  obj := localizationObj M
  map := localizationMap M
  map_id A := localizationObj_hom_ext fun a ↦ by
    rw [localizationMap_hom_algebraMap]
    rfl
  map_comp f g := localizationObj_hom_ext fun a ↦ by
    -- Morphism composition in `CommAlgCat` evaluates as composition of underlying `AlgHom`s.
    change (localizationMap M (f ≫ g)).hom _ =
      (localizationMap M g).hom ((localizationMap M f).hom _)
    rw [localizationMap_hom_algebraMap, localizationMap_hom_algebraMap,
      localizationMap_hom_algebraMap]
    rfl

/-- Object value of `localizationFunctor M` on `A`. -/
@[simp]
theorem localizationFunctor_obj (M : Submonoid R) (A : CommAlgCat.{v} R) :
    (localizationFunctor M).obj A = localizationObj M A :=
  (rfl)

/-- `R`-algebra structure on `(localizationFunctor M).obj A`. -/
noncomputable instance (M : Submonoid R) (A : CommAlgCat.{v} R) :
    Algebra R ((localizationFunctor M).obj A) :=
  inferInstanceAs (Algebra R (Localization (Algebra.algebraMapSubmonoid A M)))

/-- `A`-algebra structure on `(localizationFunctor M).obj A`. -/
noncomputable instance (M : Submonoid R) (A : CommAlgCat.{v} R) :
    Algebra A ((localizationFunctor M).obj A) :=
  inferInstanceAs (Algebra A (Localization (Algebra.algebraMapSubmonoid A M)))

/-- Compatibility of the `R`- and `A`-algebra structures on `(localizationFunctor M).obj A`. -/
instance (M : Submonoid R) (A : CommAlgCat.{v} R) :
    IsScalarTower R A ((localizationFunctor M).obj A) :=
  inferInstanceAs (IsScalarTower R A (Localization (Algebra.algebraMapSubmonoid A M)))

/-- Compatibility of the `R`- and `Localization M`-algebra structures on
`(localizationFunctor M).obj A`. -/
instance (M : Submonoid R) (A : CommAlgCat.{v} R) :
    IsScalarTower R (Localization M) ((localizationFunctor M).obj A) :=
  inferInstanceAs
    (IsScalarTower R (Localization M) (Localization (Algebra.algebraMapSubmonoid A M)))

/-- `(localizationFunctor M).obj A` is a localization of `A` at
`Algebra.algebraMapSubmonoid A M`. -/
instance (M : Submonoid R) (A : CommAlgCat.{v} R) :
    IsLocalization (Algebra.algebraMapSubmonoid A M) ((localizationFunctor M).obj A) :=
  inferInstanceAs
    (IsLocalization (Algebra.algebraMapSubmonoid A M)
      (Localization (Algebra.algebraMapSubmonoid A M)))

/-- On canonical numerators `algebraMap A _ a`, `(localizationFunctor M).map f` acts through `f`. -/
@[simp]
theorem localizationFunctor_map_hom_algebraMap (M : Submonoid R) {A B : CommAlgCat.{v} R}
    (f : A ⟶ B) (a : A) :
    ((localizationFunctor M).map f).hom
        (algebraMap A ((localizationFunctor M).obj A) a) =
      algebraMap B ((localizationFunctor M).obj B) (f.hom a) :=
  localizationMap_hom_algebraMap M f a

/-- On fractions `a / m`, `(localizationFunctor M).map f` applies `f` to the numerator. -/
@[simp]
theorem localizationFunctor_map_hom_mk' (M : Submonoid R) {A B : CommAlgCat.{v} R}
    (f : A ⟶ B) (a : A) (m : M) :
    ((localizationFunctor M).map f).hom
        (IsLocalization.mk' ((localizationFunctor M).obj A) a
          ⟨algebraMap R A m, Algebra.mem_algebraMapSubmonoid_of_mem m⟩) =
      IsLocalization.mk' ((localizationFunctor M).obj B) (f.hom a)
        ⟨algebraMap R B m, Algebra.mem_algebraMapSubmonoid_of_mem m⟩ :=
  localizationMap_hom_mk' M f a m

/-- Viewed as an `R`-linear map, `(localizationFunctor M).map f` agrees with the localized module
map of `f.hom.toLinearMap` at `M`. -/
theorem localizationFunctor_map_toLinearMap (M : Submonoid R) {A B : CommAlgCat.{v} R}
    (f : A ⟶ B) :
    ((localizationFunctor M).map f).hom.toLinearMap.restrictScalars R =
      IsLocalizedModule.map M
        (IsScalarTower.toAlgHom R A ((localizationFunctor M).obj A)).toLinearMap
        (IsScalarTower.toAlgHom R B ((localizationFunctor M).obj B)).toLinearMap
        f.hom.toLinearMap := by
  refine IsLocalizedModule.ext M
    (IsScalarTower.toAlgHom R A ((localizationFunctor M).obj A)).toLinearMap
    (IsLocalizedModule.map_units
      (IsScalarTower.toAlgHom R B ((localizationFunctor M).obj B)).toLinearMap)
    ?_
  ext a
  exact (localizationFunctor_map_hom_algebraMap M f a).trans
    (IsLocalizedModule.map_apply M
      (IsScalarTower.toAlgHom R A ((localizationFunctor M).obj A)).toLinearMap
      (IsScalarTower.toAlgHom R B ((localizationFunctor M).obj B)).toLinearMap
      f.hom.toLinearMap a).symm

/-- If some `m ∈ M` annihilates `1 : A` (equivalently `A`), then `(localizationFunctor M).obj A` is
the zero algebra. -/
theorem subsingleton_localizationFunctor_obj_of_smul_one_eq_zero {M : Submonoid R}
    {A : CommAlgCat.{v} R} {m : R} (hm : m ∈ M) (h : m • (1 : A) = 0) :
    Subsingleton ((localizationFunctor M).obj A) :=
  IsLocalization.subsingleton (M := Algebra.algebraMapSubmonoid A M)
    (S := (localizationFunctor M).obj A)
    ⟨m, hm, by simpa [Algebra.smul_def] using h⟩

/-- When every element of `M` maps to a unit in `A`, `A ≃ₐ[R] (localizationFunctor M).obj A`. -/
noncomputable def localizationFunctorObjAlgEquivOfIsUnit {M : Submonoid R} (A : CommAlgCat.{v} R)
    (hM : ∀ m ∈ M, IsUnit (algebraMap R A m)) :
    A ≃ₐ[R] (localizationFunctor M).obj A :=
  (IsLocalization.atUnits A (Algebra.algebraMapSubmonoid A M)
    (S := (localizationFunctor M).obj A)
    (by rintro _ ⟨m, hm, rfl⟩; exact hM m hm)).restrictScalars R

/-- `localizationFunctorObjAlgEquivOfIsUnit` acts as `algebraMap A _`. -/
@[simp]
theorem localizationFunctorObjAlgEquivOfIsUnit_apply {M : Submonoid R} (A : CommAlgCat.{v} R)
    (hM : ∀ m ∈ M, IsUnit (algebraMap R A m)) (a : A) :
    localizationFunctorObjAlgEquivOfIsUnit A hM a =
      algebraMap A ((localizationFunctor M).obj A) a :=
  (rfl)

end CommAlgCat
