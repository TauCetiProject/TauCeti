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
    (fun X => (functor r).mapIso (pivotalIsoApp X.as)) (by
      intro X Y f
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      simp only [Functor.id_map, doubleRightDualFunctor_map, rightAdjointMate_map]
      exact congrArg (functor r).map (pivotalIsoApp_hom_naturality f))
  pivotalIso_isMonoidal := {
    unit := by
      -- Expose the components together with their dependent bidual endpoints.
      change 𝟙 _ ≫ (functor r).map (pivotalIsoApp (𝟙_ C)).hom = _
      rw [Category.id_comp, doubleRightDualFunctor_ε_eq_map]
      exact congrArg (functor r).map (pivotalIsoApp_unit_hom (C := C))
    tensor := by
      rintro ⟨X⟩ ⟨Y⟩
      -- Unfolding components alone leaves the bidual functor's object wrappers in their types.
      change 𝟙 _ ≫ (functor r).map (pivotalIsoApp (X ⊗ Y)).hom =
        ((functor r).map (pivotalIsoApp X).hom ⊗ₘ (functor r).map (pivotalIsoApp Y).hom) ≫
          μ (doubleRightDualFunctor (Quotient r)) ((functor r).obj X) ((functor r).obj Y)
      rw [Category.id_comp, doubleRightDualFunctor_μ_obj, map_tensorHom_map]
      exact (congrArg (functor r).map (pivotalIsoApp_tensor_hom X Y)).trans
        ((functor r).map_comp _ _) }

/-- Each descended pivotal component is the class of the original component. -/
@[simp]
theorem pivotalIsoApp_hom (X : Quotient r) :
    (pivotalIsoApp X).hom = (functor r).map (pivotalIsoApp X.as).hom := by
  rw [← TauCeti.pivotalIso_hom_app]
  rfl

/-- The inverse pivotal component is the class of the original inverse component. -/
@[simp]
theorem pivotalIsoApp_inv (X : Quotient r) :
    (pivotalIsoApp X).inv = (functor r).map (pivotalIsoApp X.as).inv := by
  rw [← TauCeti.pivotalIso_inv_app]
  rfl

/-- The pivotal component at an image object is the image of its source component. -/
@[simp↓]
theorem pivotalIsoApp_obj_hom (X : C) :
    (pivotalIsoApp ((functor r).obj X)).hom = (functor r).map (pivotalIsoApp X).hom :=
  pivotalIsoApp_hom (Quotient.mk X)

/-- The inverse pivotal component at an image object is the image of its source inverse. -/
@[simp↓]
theorem pivotalIsoApp_obj_inv (X : C) :
    (pivotalIsoApp ((functor r).obj X)).inv = (functor r).map (pivotalIsoApp X).inv :=
  pivotalIsoApp_inv (Quotient.mk X)

/-- The quotient functor preserves the pivotal structure, with its descended duals. -/
instance functor_isPivotal : (functor r).IsPivotal where
  map_pivotalIsoApp_hom X := by
    simp only [pivotalIsoApp_hom, mapRightDualIso_eq_refl, Iso.refl_hom, Iso.refl_inv,
      rightAdjointMate_id]
    -- Normalize the bidual endpoints together; separately simplifying them cannot
    -- rewrite the identities whose domains are fixed by the mapped pivotal component.
    change (functor r).map (pivotalIsoApp X).hom =
      (functor r).map (pivotalIsoApp X).hom ≫ 𝟙 _ ≫ 𝟙 _
    simp

/-- A pivotal functor identifying related morphisms factors as a pivotal functor. -/
instance lift_isPivotal {D : Type*} [Category* D] [MonoidalCategory D] [RigidCategory D]
    [PivotalCategory D] (F : C ⥤ D) [F.Monoidal] [F.IsPivotal]
    (H : ∀ (X Y : C) (f g : X ⟶ Y), r f g → F.map f = F.map g) :
    (lift r F H).IsPivotal where
  map_pivotalIsoApp_hom X := by
    simp only [pivotalIsoApp_hom, lift_mapRightDualIso]
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
