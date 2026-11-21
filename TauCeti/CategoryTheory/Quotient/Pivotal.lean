/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Quotient.Rigid
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Functor.Basic

/-!
# Pivotal and spherical quotients by monoidal relations

The pivotal isomorphism of a rigid monoidal category descends to its quotient by any monoidal
relation. With the descended duals, its component is simply the class of the original component.
The quotient functor is pivotal and preserves both traces. A pivotal functor identifying related
morphisms factors through the quotient as a pivotal functor. Consequently sphericality also
descends. In particular, these structures permit taking quotients by tensor ideals, including
negligible quotients, without losing the trace and dimension operations.

## References

* J. W. Barrett and B. W. Westbury, *Spherical categories*, Adv. Math. 143 (1999), 357–375.
* F. M. Goodman and H. Wenzl, *Ideals in the Temperley–Lieb category*, Sections 1–3.
-/

public section

universe v u

namespace CategoryTheory.Quotient

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {r : HomRel C} [r.IsMonoidal] [RigidCategory C] [PivotalCategory C]

/-- A pivotal structure descends through any monoidal relation: its components are the classes
of the original pivotal components, for the descended dual choices. -/
noncomputable instance instPivotalCategory : PivotalCategory (Quotient r) where
  pivotalIso := NatIso.ofComponents
    (fun X => (functor r).mapIso (PivotalCategory.pivotalIso.app X.as)) (by
      intro X Y f
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      simp only [Functor.id_map, doubleRightDualFunctor_map, rightAdjointMate_map]
      exact congrArg (functor r).map (PivotalCategory.pivotalIso.hom.naturality f))
  pivotalIso_isMonoidal := {
    unit := by
      -- The component is definitionally the image of the source pivotal component.
      rw [Functor.LaxMonoidal.id_ε, Category.id_comp, doubleRightDualFunctor_ε_eq_map]
      have h := pivotalIsoApp_unit_hom (C := C)
      rw [← TauCeti.pivotalIso_hom_app] at h
      exact congrArg (functor r).map h
    tensor := by
      rintro ⟨X⟩ ⟨Y⟩
      rw [Functor.LaxMonoidal.id_μ, Category.id_comp]
      have h := pivotalIsoApp_tensor_hom X Y
      simp only [← TauCeti.pivotalIso_hom_app] at h
      -- Components are definitionally mapped source components; term congruence keeps
      -- their dependent bidual endpoints together when comparing the tensorators.
      exact ((congrArg (functor r).map h).trans ((functor r).map_comp _ _)).trans
        (congrArg₂ (· ≫ ·) (map_tensorHom_map _ _).symm
          (doubleRightDualFunctor_μ_obj X Y).symm) }

/-- Each descended pivotal component is the class of the original component. -/
theorem pivotalIsoApp_hom (X : Quotient r) :
    (pivotalIsoApp X).hom = (functor r).map (pivotalIsoApp X.as).hom := by
  simp only [← TauCeti.pivotalIso_hom_app]
  rfl

/-- The inverse pivotal component is the class of the original inverse component. -/
theorem pivotalIsoApp_inv (X : Quotient r) :
    (pivotalIsoApp X).inv = (functor r).map (pivotalIsoApp X.as).inv := by
  simp only [← TauCeti.pivotalIso_inv_app]
  rfl

/-- The pivotal component at an image object is the image of its source component. -/
theorem pivotalIsoApp_hom_obj (X : C) :
    (pivotalIsoApp ((functor r).obj X)).hom = (functor r).map (pivotalIsoApp X).hom :=
  pivotalIsoApp_hom (Quotient.mk X)

/-- The inverse pivotal component at an image object is the image of its source inverse. -/
theorem pivotalIsoApp_inv_obj (X : C) :
    (pivotalIsoApp ((functor r).obj X)).inv = (functor r).map (pivotalIsoApp X).inv :=
  pivotalIsoApp_inv (Quotient.mk X)

/-- The quotient functor preserves the pivotal structure, with its descended duals. -/
instance isPivotal_functor : (functor r).IsPivotal :=
  Functor.isPivotal_iff_map_pivotalIsoApp_hom_comp_mapDoubleRightDualIso_hom.mpr fun X => by
    rw [functor_mapDoubleRightDualIso, Iso.refl_hom]
    -- Descended bidual endpoints are definitionally the images of source biduals.
    exact (Category.comp_id _).trans (pivotalIsoApp_hom_obj X).symm

/-- A pivotal functor identifying related morphisms factors as a pivotal functor. -/
instance isPivotal_lift {D : Type*} [Category* D] [MonoidalCategory D] [RigidCategory D]
    [PivotalCategory D] (F : C ⥤ D) [F.Monoidal] [F.IsPivotal]
    (H : ∀ (X Y : C) (f g : X ⟶ Y), r f g → F.map f = F.map g) :
    (lift r F H).IsPivotal where
  map_pivotalIsoApp_hom X := by
    simp only [pivotalIsoApp_hom, lift_mapRightDualIso]
    -- The underlying object (Xᘁ).as is definitionally (X.as)ᘁ, and the lift sends
    -- a class (functor r).map f definitionally to F.map f.
    exact Functor.IsPivotal.map_pivotalIsoApp_hom (F := F) X.as

/-- Sphericality descends through any monoidal relation. -/
instance instSphericalCategory [SphericalCategory C] : SphericalCategory (Quotient r) where
  leftTrace_eq_rightTrace := by
    rintro ⟨X⟩ f
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    rw [Functor.leftTrace_map, Functor.rightTrace_map, SphericalCategory.leftTrace_eq_rightTrace]

-- The general pivotal-functor API gives trace and dimension preservation without extra
-- quotient-specific wrappers or any assumption of nondegeneracy.
example [SphericalCategory C] {X : C} (f : X ⟶ X) :
    trace ((functor r).map f) = (functor r).map (trace f) := by
  simp [Functor.trace_map]

example [SphericalCategory C] (X : C) :
    quantumDim ((functor r).obj X) = (functor r).map (quantumDim X) := by
  simp [Functor.quantumDim_map]

end CategoryTheory.Quotient
