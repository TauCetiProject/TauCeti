/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Underlying module complexes of representations

An element of a monoid acts degreewise on the underlying module complex of a complex of
representations. The differentials are intertwining maps, so these actions are chain maps.
For a noncommutative monoid they need not be morphisms of representations.

Restriction of a representation changes only its action. The isomorphism
`HomologicalComplex.repResForget₂Iso` identifies the underlying module complexes before
and after restriction explicitly, so naturality squares need not rely on unfolding
whole complexes to identify their intermediate objects.
-/

public section

open CategoryTheory

namespace HomologicalComplex

universe u v w t

variable {k : Type u} [Ring k] {G : Type v} [Monoid G] {ι : Type t}
  {c : ComplexShape ι} (C : HomologicalComplex (Rep.{w} k G) c)

/-- The degreewise action of a monoid element on the underlying complex of modules. -/
def repTranslation (g : G) :
    ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex c).obj C ⟶
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex c).obj C where
  f n := ModuleCat.ofHom ((C.X n).ρ g)
  comm' i j _ := ModuleCat.hom_ext ((C.d i j).hom.isIntertwining' g)

/-- The component of translation is the action on that degree's representation. -/
@[simp]
theorem repTranslation_f (g : G) (n : ι) :
    (C.repTranslation g).f n = ModuleCat.ofHom ((C.X n).ρ g) := (rfl)

/-- The identity monoid element acts as the identity chain map. -/
@[simp]
theorem repTranslation_one : C.repTranslation 1 = 𝟙 _ := by
  ext n : 1
  apply ModuleCat.hom_ext
  simp only [repTranslation_f, HomologicalComplex.id_f, ModuleCat.hom_ofHom,
    map_one, ModuleCat.hom_id, Module.End.one_eq_id]

/-- Translation by a product is successive translation, with categorical composition order. -/
theorem repTranslation_mul (g h : G) :
    C.repTranslation (g * h) = C.repTranslation h ≫ C.repTranslation g := by
  ext n : 1
  apply ModuleCat.hom_ext
  simp only [repTranslation_f, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, map_mul, Module.End.mul_eq_comp]

/-- Chain maps of representations intertwine degreewise translation. -/
@[reassoc]
theorem repTranslation_naturality {D : HomologicalComplex (Rep.{w} k G) c}
    (φ : C ⟶ D) (g : G) :
    C.repTranslation g ≫ ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex c).map φ =
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex c).map φ ≫
        D.repTranslation g := by
  ext n : 1
  exact ModuleCat.hom_ext ((φ.f n).hom.isIntertwining' g)

section Restriction

variable {H : Type*} [Monoid H]
  (D : HomologicalComplex (Rep.{w} k H) c) (φ : G →* H)

/-- Restriction changes only the group action, not the underlying module complex. -/
def repResForget₂Iso :
    ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex c).obj
        (((Rep.resFunctor φ).mapHomologicalComplex c).obj D) ≅
      ((forget₂ (Rep k H) (ModuleCat k)).mapHomologicalComplex c).obj D :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ rfl)

/-- The comparison after forgetting restriction is the identity in each degree. -/
@[simp]
theorem repResForget₂Iso_hom_f (n : ι) :
    (D.repResForget₂Iso φ).hom.f n = 𝟙 _ := (rfl)

/-- The inverse comparison after forgetting restriction is the identity in each degree. -/
@[simp]
theorem repResForget₂Iso_inv_f (n : ι) :
    (D.repResForget₂Iso φ).inv.f n = 𝟙 _ := (rfl)

/-- The underlying-complex comparison commutes with maps of representations. -/
@[reassoc]
theorem repResForget₂Iso_hom_naturality {E : HomologicalComplex (Rep.{w} k H) c}
    (f : D ⟶ E) :
    ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex c).map
          (((Rep.resFunctor φ).mapHomologicalComplex c).map f) ≫
        (E.repResForget₂Iso φ).hom =
      (D.repResForget₂Iso φ).hom ≫
        ((forget₂ (Rep k H) (ModuleCat k)).mapHomologicalComplex c).map f := by
  ext n : 1
  simp only [comp_f, repResForget₂Iso_hom_f, Category.comp_id, Category.id_comp]
  rfl

end Restriction

end HomologicalComplex
