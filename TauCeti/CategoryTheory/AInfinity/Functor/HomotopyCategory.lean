/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Cohomology
public import TauCeti.CategoryTheory.AInfinity.Functor.Basic
public import TauCeti.CategoryTheory.AInfinity.HomotopyCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The functor on homotopy categories induced by an A-infinity functor

An `A∞` functor `ℱ : ℬ ⟶ 𝒞` induces a functor `H⁰(ℱ) : H⁰(ℬ) ⥤ H⁰(𝒞)` between the homotopy
categories of cohomologically unital `A∞` categories.  On objects it is the object map of `ℱ`,
and it sends the class of a closed degree-zero morphism `f` to the class of `f₁(f)`, where `f₁` is
the arity-one component of `ℱ` (`TauCeti.AInfinityFunctor.map`).

The arity-one component is a chain map for `m₁`, so it carries cycles to cycles and boundaries to
boundaries, and hence descends to Hom classes.  It is not multiplicative on chains: the arity-two
`A∞` functor equation says that on closed morphisms `g` and `f` the defect
`f₁(m₂(g, f)) - m₂(f₁ g, f₁ f)` is the differential of the arity-two component `f₂(g, f)`
(`TauCeti.AInfinityFunctor.map_comp_sub_comp_mem_range`).  So the induced map on classes
preserves composition.

Preservation of identities is not automatic, because the units of `H⁰(ℬ)` and `H⁰(𝒞)` are only
cohomological.  Following Lyubashenko, an `A∞` functor is *unital*
(`TauCeti.AInfinityFunctor.IsUnital`) when `f₁` carries cohomological units of `ℬ` to cohomological
units of `𝒞` modulo boundaries.  Unit classes are unique, so it suffices to check this for one
choice of units on each side (`TauCeti.AInfinityFunctor.isUnital_iff`).  The identity `A∞` functor
is unital.

## Main definitions

* `TauCeti.AInfinityFunctor.homClassMap`: the linear map induced by an `A∞` functor on the Hom
  classes of closed degree-zero morphisms.
* `TauCeti.AInfinityFunctor.IsUnital`: an `A∞` functor which preserves cohomological units.
* `TauCeti.AInfinityFunctor.mapHomotopyCategory`: the functor `H⁰(ℱ)` induced by a unital `A∞`
  functor `ℱ`.  It is additive and linear over the ground ring.
* `TauCeti.AInfinityFunctor.mapHomotopyCategoryIdIso`: `H⁰` of the identity `A∞` functor is the
  identity functor.

## Main results

* `TauCeti.AInfinityFunctor.map_comp_sub_comp_mem_range`: an `A∞` functor preserves the
  composition of closed morphisms up to a boundary.
* `TauCeti.AInfinityFunctor.homClassMap_homClass`: the induced map sends the class of `f` to the
  class of `f₁(f)`.
* `TauCeti.AInfinityFunctor.isUnital_iff`: unitality can be checked on one choice of cohomological
  units of the source and of the target.
* `TauCeti.AInfinityFunctor.mapHomotopyCategory_map_homOf`: `H⁰(ℱ)` sends the class of a closed
  morphism `f` to the class of `f₁(f)`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 7.
* V. Lyubashenko, *Category of A-infinity-categories*, Homology, Homotopy and Applications 5
  (2003), for unital `A∞` functors.
-/

public section

open CategoryTheory

namespace TauCeti

universe u₁ u₂ v₁ v₂ w

open GradedLinearQuiver

variable {R : Type w} [CommRing R] {C : Type u₁} {D : Type u₂}
  [GradedLinearQuiver.{u₁, v₁, w} R C] [GradedLinearQuiver.{u₂, v₂, w} R D]

namespace AInfinityFunctor

variable {ℬ : AInfinityCategory R C} {𝒞 : AInfinityCategory R D} (ℱ : AInfinityFunctor ℬ 𝒞)

/-! ### Cycles, boundaries and composition -/

/-- The map of an `A∞` functor on a Hom module sends closed degree-zero morphisms to closed
degree-zero morphisms. -/
theorem map_mem_homCyclesZero {X Y : C} {f : homModule (R := R) X Y}
    (hf : f ∈ ℬ.homCyclesZero X Y) : ℱ.map X Y f ∈ 𝒞.homCyclesZero (ℱ.obj X) (ℱ.obj Y) := by
  rw [AInfinityCategory.mem_homCyclesZero] at hf ⊢
  exact ⟨ℱ.map_mem X Y hf.1, by rw [← map_homDifferential, hf.2, map_zero]⟩

/-- The map of an `A∞` functor on a Hom module sends boundaries to boundaries. -/
theorem map_mem_range_homDifferential {X Y : C} {f : homModule (R := R) X Y}
    (hf : f ∈ LinearMap.range (ℬ.homDifferential X Y)) :
    ℱ.map X Y f ∈ LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y)) := by
  obtain ⟨h, rfl⟩ := hf
  exact ⟨ℱ.map X Y h, (ℱ.map_homDifferential X Y h).symm⟩

/-- **An `A∞` functor preserves composition up to a boundary.**  For closed morphisms
`g : Y ⟶ Z` and `f : X ⟶ Y`, the defect `f₁(m₂(g, f)) - m₂(f₁ g, f₁ f)` is a boundary: by the
arity-two `A∞` functor equation it is the differential of the arity-two component `f₂(g, f)`. -/
theorem map_comp_sub_comp_mem_range {X Y Z : C} {g : homModule (R := R) Y Z}
    {f : homModule (R := R) X Y} (hg : ℬ.homDifferential Y Z g = 0)
    (hf : ℬ.homDifferential X Y f = 0) :
    ℱ.map X Z (ℬ.comp X Y Z g f) -
        𝒞.comp (ℱ.obj X) (ℱ.obj Y) (ℱ.obj Z) (ℱ.map Y Z g) (ℱ.map X Y f) ∈
      LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj Z)) := by
  -- The total version: the defect of the linear part on the included cycles is a boundary of the
  -- total algebra of the induced category.
  obtain ⟨y, hy⟩ := (𝒞.induced ℱ.obj).toAInfinityAlgebra.mem_boundaries.mp <|
    ℱ.toAInfinityHom.linearPart_m_two_sub_mem_boundaries
      (ℬ.homInclusion_mem_cycles hg) (ℬ.homInclusion_mem_cycles hf)
  rw [← ℬ.homInclusion_comp, ← homInclusion_map, ← homInclusion_map, ← homInclusion_map,
    ← AInfinityCategory.homInclusion_comp, ← map_sub,
    ← AInfinityAlgebra.differential_apply] at hy
  -- Its component between the images of `X` and `Z` is the claimed defect.
  refine ⟨homProjection (R := R) (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Z⟩ y, ?_⟩
  have h := congrArg (homProjection (R := R) (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Z⟩) hy
  rwa [AInfinityCategory.homProjection_differential, homProjection_homInclusion,
    AInfinityCategory.homDifferential_induced, AInfinityCategory.comp_induced] at h

/-! ### The map on Hom classes -/

/-- An `A∞` functor carries closed degree-zero morphisms with the same Hom class to closed
degree-zero morphisms with the same Hom class. -/
private theorem homClass_map_eq_homClass_map {X Y : C} {f g : homModule (R := R) X Y}
    (hf : f ∈ ℬ.homCyclesZero X Y) (hg : g ∈ ℬ.homCyclesZero X Y)
    (h : ℬ.homClass f hf = ℬ.homClass g hg) :
    𝒞.homClass (ℱ.map X Y f) (ℱ.map_mem_homCyclesZero hf) =
      𝒞.homClass (ℱ.map X Y g) (ℱ.map_mem_homCyclesZero hg) := by
  rw [AInfinityCategory.homClass_eq_iff_sub_mem_range] at h ⊢
  rw [← map_sub]
  exact ℱ.map_mem_range_homDifferential h

/-- The Hom class of the image of a chosen representative. -/
private noncomputable def homClassMapAux (X Y : C) (a : ℬ.homCohomologyZero X Y) :
    𝒞.homCohomologyZero (ℱ.obj X) (ℱ.obj Y) :=
  𝒞.homClass (ℱ.map X Y (ℬ.exists_homClass_eq a).choose)
    (ℱ.map_mem_homCyclesZero (ℬ.exists_homClass_eq a).choose_spec.choose)

private theorem homClassMapAux_homClass {X Y : C} (f : homModule (R := R) X Y)
    (hf : f ∈ ℬ.homCyclesZero X Y) :
    ℱ.homClassMapAux X Y (ℬ.homClass f hf) =
      𝒞.homClass (ℱ.map X Y f) (ℱ.map_mem_homCyclesZero hf) :=
  ℱ.homClass_map_eq_homClass_map _ _
    (ℬ.exists_homClass_eq (ℬ.homClass f hf)).choose_spec.choose_spec

/-- The **map induced by an `A∞` functor on Hom classes** of closed degree-zero morphisms: the
class of `f` goes to the class of `f₁(f)` (`TauCeti.AInfinityFunctor.homClassMap_homClass`). -/
noncomputable def homClassMap (X Y : C) :
    ℬ.homCohomologyZero X Y →ₗ[R] 𝒞.homCohomologyZero (ℱ.obj X) (ℱ.obj Y) where
  toFun := ℱ.homClassMapAux X Y
  map_add' a b := by
    obtain ⟨f, hf, rfl⟩ := ℬ.exists_homClass_eq a
    obtain ⟨g, hg, rfl⟩ := ℬ.exists_homClass_eq b
    rw [← AInfinityCategory.homClass_add]
    simp only [homClassMapAux_homClass, map_add]
    exact 𝒞.homClass_add _ _ (ℱ.map_mem_homCyclesZero hf) (ℱ.map_mem_homCyclesZero hg)
  map_smul' r a := by
    obtain ⟨f, hf, rfl⟩ := ℬ.exists_homClass_eq a
    rw [← AInfinityCategory.homClass_smul]
    simp only [homClassMapAux_homClass, map_smul, RingHom.id_apply]
    exact 𝒞.homClass_smul r _ (ℱ.map_mem_homCyclesZero hf)

/-- The map on Hom classes sends the class of a closed degree-zero morphism `f` to the class of
`f₁(f)`. -/
@[simp]
theorem homClassMap_homClass {X Y : C} (f : homModule (R := R) X Y)
    (hf : f ∈ ℬ.homCyclesZero X Y) :
    ℱ.homClassMap X Y (ℬ.homClass f hf) =
      𝒞.homClass (ℱ.map X Y f) (ℱ.map_mem_homCyclesZero hf) :=
  ℱ.homClassMapAux_homClass f hf

/-- The map on Hom classes preserves the composition of classes. -/
theorem homClassMap_homCohomologyComp {X Y Z : C} (a : ℬ.homCohomologyZero X Y)
    (b : ℬ.homCohomologyZero Y Z) :
    ℱ.homClassMap X Z (ℬ.homCohomologyComp X Y Z a b) =
      𝒞.homCohomologyComp (ℱ.obj X) (ℱ.obj Y) (ℱ.obj Z) (ℱ.homClassMap X Y a)
        (ℱ.homClassMap Y Z b) := by
  obtain ⟨f, hf, rfl⟩ := ℬ.exists_homClass_eq a
  obtain ⟨g, hg, rfl⟩ := ℬ.exists_homClass_eq b
  rw [AInfinityCategory.homCohomologyComp_homClass, homClassMap_homClass, homClassMap_homClass,
    homClassMap_homClass, AInfinityCategory.homCohomologyComp_homClass,
    AInfinityCategory.homClass_eq_iff_sub_mem_range]
  exact ℱ.map_comp_sub_comp_mem_range (ℬ.mem_homCyclesZero.mp hg).2 (ℬ.mem_homCyclesZero.mp hf).2

/-! ### Unital functors -/

/-- An `A∞` functor is **unital** if its arity-one component carries cohomological units of the
source to cohomological units of the target modulo boundaries: for all families of
cohomological-unit representatives `e` of `ℬ` and `e'` of `𝒞`, every `f₁(e X) - e' (ℱ.obj X)` is
a boundary.  Unit classes are unique, so it is enough to check this for one choice of `e` and `e'`
(`TauCeti.AInfinityFunctor.isUnital_iff`). -/
def IsUnital : Prop :=
  ∀ ⦃e : ∀ X : C, homModule (R := R) X X⦄ ⦃e' : ∀ Y : D, homModule (R := R) Y Y⦄,
    ℬ.CohomologicalUnits e → 𝒞.CohomologicalUnits e' → ∀ X : C,
      ℱ.map X X (e X) - e' (ℱ.obj X) ∈
        LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj X))

/-- An `A∞` functor is unital when it carries every family of cohomological-unit representatives
of the source to every family of cohomological-unit representatives of the target, modulo
boundaries. -/
theorem isUnital_def : ℱ.IsUnital ↔
    ∀ ⦃e : ∀ X : C, homModule (R := R) X X⦄ ⦃e' : ∀ Y : D, homModule (R := R) Y Y⦄,
      ℬ.CohomologicalUnits e → 𝒞.CohomologicalUnits e' → ∀ X : C,
        ℱ.map X X (e X) - e' (ℱ.obj X) ∈
          LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj X)) :=
  Iff.rfl

/-- **Unitality can be checked on one choice of units.**  Given cohomological-unit
representatives `e` of `ℬ` and `e'` of `𝒞`, an `A∞` functor is unital exactly when it carries each
`e X` to `e' (ℱ.obj X)` modulo boundaries. -/
theorem isUnital_iff {e : ∀ X : C, homModule (R := R) X X} {e' : ∀ Y : D, homModule (R := R) Y Y}
    (he : ℬ.CohomologicalUnits e) (he' : 𝒞.CohomologicalUnits e') :
    ℱ.IsUnital ↔ ∀ X : C, ℱ.map X X (e X) - e' (ℱ.obj X) ∈
      LinearMap.range (𝒞.homDifferential (ℱ.obj X) (ℱ.obj X)) := by
  refine ⟨fun h ↦ h he he', fun h e₁ e₁' he₁ he₁' X ↦ ?_⟩
  -- Pass to Hom classes, where both families of units give the same identity classes.
  have key : 𝒞.homClass (ℱ.map X X (e₁ X)) (ℱ.map_mem_homCyclesZero (he₁.cycle X)) =
      𝒞.homClass (e₁' (ℱ.obj X)) (he₁'.cycle (ℱ.obj X)) := by
    rw [← homClassMap_homClass ℱ (e₁ X) (he₁.cycle X), ← he.homClass_eq he₁ X, homClassMap_homClass,
      ← he'.homClass_eq he₁' (ℱ.obj X), AInfinityCategory.homClass_eq_iff_sub_mem_range]
    exact h X
  exact (AInfinityCategory.homClass_eq_iff_sub_mem_range _ _ _).mp key

/-- The identity `A∞` functor is unital. -/
theorem isUnital_id : (AInfinityFunctor.id ℬ).IsUnital := fun e e' he he' X ↦ by
  simp only [id_map_apply]
  exact (ℬ.homClass_eq_iff_sub_mem_range (he.cycle X) (he'.cycle X)).mp (he.homClass_eq he' X)

/-! ### The functor on homotopy categories -/

variable (hℬ : ℬ.CohomologicallyUnital) (h𝒞 : 𝒞.CohomologicallyUnital) {ℱ}

/-- The **functor `H⁰(ℱ)` on homotopy categories** induced by a unital `A∞` functor `ℱ`.  On
objects it is the object map of `ℱ`, and it sends the class of a closed degree-zero morphism `f`
to the class of `f₁(f)` (`TauCeti.AInfinityFunctor.mapHomotopyCategory_map_homOf`). -/
-- Expose the object and morphism maps, so that the types of the characteristic lemmas reduce.
@[expose]
noncomputable def mapHomotopyCategory (hℱ : ℱ.IsUnital) :
    AInfinityHomotopyCategory ℬ hℬ ⥤ AInfinityHomotopyCategory 𝒞 h𝒞 where
  obj X := .of (ℱ.obj X.obj)
  map {X Y} a := ℱ.homClassMap X.obj Y.obj a
  map_id X := by
    obtain ⟨e, he⟩ := ℬ.cohomologicallyUnital_iff.mp hℬ
    obtain ⟨e', he'⟩ := 𝒞.cohomologicallyUnital_iff.mp h𝒞
    rw [AInfinityHomotopyCategory.id_eq_homClass he, AInfinityHomotopyCategory.id_eq_homClass he',
      homClassMap_homClass, AInfinityCategory.homClass_eq_iff_sub_mem_range]
    exact hℱ he he' X.obj
  map_comp {X Y Z} a b := ℱ.homClassMap_homCohomologyComp a b

variable (hℱ : ℱ.IsUnital)

/-- `H⁰(ℱ)` sends an object `X` to the image of its underlying object under `ℱ`. -/
@[simp]
theorem mapHomotopyCategory_obj (X : AInfinityHomotopyCategory ℬ hℬ) :
    (mapHomotopyCategory hℬ h𝒞 hℱ).obj X = .of (ℱ.obj X.obj) :=
  (rfl)

/-- `H⁰(ℱ)` acts on morphisms by the map induced by `ℱ` on Hom classes. -/
theorem mapHomotopyCategory_map {X Y : AInfinityHomotopyCategory ℬ hℬ} (a : X ⟶ Y) :
    (mapHomotopyCategory hℬ h𝒞 hℱ).map a = ℱ.homClassMap X.obj Y.obj a :=
  (rfl)

/-- `H⁰(ℱ)` sends the class of a closed degree-zero morphism `f` to the class of `f₁(f)`. -/
@[simp]
theorem mapHomotopyCategory_map_homOf {X Y : C} (f : homModule (R := R) X Y)
    (hf : f ∈ ℬ.homCyclesZero X Y) :
    (mapHomotopyCategory hℬ h𝒞 hℱ).map (AInfinityHomotopyCategory.homOf (h𝒞 := hℬ) f hf) =
      AInfinityHomotopyCategory.homOf (ℱ.map X Y f) (ℱ.map_mem_homCyclesZero hf) := by
  rw [mapHomotopyCategory_map, AInfinityHomotopyCategory.homOf_def,
    AInfinityHomotopyCategory.homOf_def]
  exact ℱ.homClassMap_homClass f hf

instance : (mapHomotopyCategory hℬ h𝒞 hℱ).Additive where
  map_add {X Y} a b := (ℱ.homClassMap X.obj Y.obj).map_add a b

instance : (mapHomotopyCategory hℬ h𝒞 hℱ).Linear R where
  map_smul {X Y} a r := (ℱ.homClassMap X.obj Y.obj).map_smul r a

/-- `H⁰` of the identity `A∞` functor is the identity functor. -/
noncomputable def mapHomotopyCategoryIdIso :
    mapHomotopyCategory hℬ hℬ (isUnital_id (ℬ := ℬ)) ≅ 𝟭 (AInfinityHomotopyCategory ℬ hℬ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {X Y} a ↦ by
    obtain ⟨f, hf, rfl⟩ := ℬ.exists_homClass_eq a
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    -- The identity functor acts on Hom modules by the identity, hence on classes too.
    rw [mapHomotopyCategory_map, homClassMap_homClass, Functor.id_map]
    simp only [id_map_apply]
    -- The two classes now differ only in the object `(AInfinityFunctor.id ℬ).obj X.obj`, which
    -- is `X.obj` by definition (`AInfinityFunctor.id_obj`).
    rfl

end AInfinityFunctor

end TauCeti
