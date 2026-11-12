/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Envelope.Quotient.Rigid
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Functor.Basic

/-!
# Pivotal and spherical quotients by tensor ideals

The pivotal isomorphism of a rigid monoidal preadditive category descends to its quotient
by a tensor ideal. With the descended duals, its component is simply the class of the original
component. The quotient functor is pivotal and preserves both traces. Consequently sphericality
also descends. These structures permit taking negligible quotients without losing the trace
and dimension operations.

## References

* J. W. Barrett and B. W. Westbury, *Spherical categories*, Adv. Math. 143 (1999), 357–375.
* F. M. Goodman and H. Wenzl, *Ideals in the Temperley–Lieb category*, Sections 1–3.
-/

public section

universe v u

namespace TauCeti.MonoidalQuotient

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] {I : MonoidalIdeal C}

variable [RigidCategory C] [PivotalCategory C]

/-- A pivotal structure descends through any tensor ideal: its components are the classes
of the original pivotal components, for the descended dual choices. -/
noncomputable instance instPivotalCategory : PivotalCategory (MonoidalQuotient I) where
  pivotalIso := NatIso.ofComponents
    (fun X => (toMonoidalQuotient I).mapIso (pivotalIsoApp X.as)) (by
      intro X Y f
      obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
      simp only [Functor.id_map, doubleRightDualFunctor_map, rightAdjointMate_map]
      exact congrArg (toMonoidalQuotient I).map (pivotalIsoApp_hom_naturality f))
  pivotalIso_isMonoidal := {
    unit := by
      -- Expose the components together with their dependent bidual endpoints.
      change 𝟙 _ ≫ (toMonoidalQuotient I).map (pivotalIsoApp (𝟙_ C)).hom = _
      rw [Category.id_comp, doubleRightDualFunctor_ε_eq_map]
      exact congrArg (toMonoidalQuotient I).map (pivotalIsoApp_unit_hom (C := C))
    tensor := by
      rintro ⟨X⟩ ⟨Y⟩
      -- Unfolding components alone leaves the bidual functor's object wrappers in their types.
      change 𝟙 _ ≫ (toMonoidalQuotient I).map (pivotalIsoApp (X ⊗ Y)).hom =
        ((toMonoidalQuotient I).map (pivotalIsoApp X).hom ⊗ₘ
          (toMonoidalQuotient I).map (pivotalIsoApp Y).hom) ≫
            μ (doubleRightDualFunctor (MonoidalQuotient I))
              ((toMonoidalQuotient I).obj X) ((toMonoidalQuotient I).obj Y)
      rw [Category.id_comp, doubleRightDualFunctor_μ_obj,
        CategoryTheory.Quotient.map_tensorHom_map]
      exact (congrArg (toMonoidalQuotient I).map (pivotalIsoApp_tensor_hom X Y)).trans
        ((toMonoidalQuotient I).map_comp _ _) }

/-- Each descended pivotal component is the class of the original component. -/
@[simp]
theorem pivotalIsoApp_hom (X : MonoidalQuotient I) :
    (pivotalIsoApp X).hom = (toMonoidalQuotient I).map (pivotalIsoApp X.as).hom := by
  rw [← TauCeti.pivotalIso_hom_app]
  rfl

/-- The inverse pivotal component is the class of the original inverse component. -/
@[simp]
theorem pivotalIsoApp_inv (X : MonoidalQuotient I) :
    (pivotalIsoApp X).inv = (toMonoidalQuotient I).map (pivotalIsoApp X.as).inv := by
  rw [← TauCeti.pivotalIso_inv_app]
  rfl

/-- The quotient functor preserves the pivotal structure, with its descended duals. -/
instance toMonoidalQuotient_isPivotal : (toMonoidalQuotient I).IsPivotal where
  map_pivotalIsoApp_hom X := by
    simp only [pivotalIsoApp_hom, mapRightDualIso_eq_refl, Iso.refl_hom, Iso.refl_inv,
      rightAdjointMate_id]
    -- Normalize the bidual endpoints together; separately simplifying them cannot
    -- rewrite the identities whose domains are fixed by the mapped pivotal component.
    change (toMonoidalQuotient I).map (pivotalIsoApp X).hom =
      (toMonoidalQuotient I).map (pivotalIsoApp X).hom ≫ 𝟙 _ ≫ 𝟙 _
    simp

/-- Sphericality descends through any tensor ideal: both traces of a class are the classes
of the corresponding source traces. -/
instance instSphericalCategory [SphericalCategory C] : SphericalCategory (MonoidalQuotient I) where
  leftTrace_eq_rightTrace := by
    rintro ⟨X⟩ f
    obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
    rw [Functor.leftTrace_map, Functor.rightTrace_map, SphericalCategory.leftTrace_eq_rightTrace]

-- The general pivotal-functor API gives trace and dimension preservation without extra
-- quotient-specific wrappers or any assumption of nondegeneracy.
example [SphericalCategory C] {X : C} (f : X ⟶ X) :
    trace ((toMonoidalQuotient I).map f) = (toMonoidalQuotient I).map (trace f) := by
  simp [Functor.trace_map]

example [SphericalCategory C] (X : C) :
    quantumDim ((toMonoidalQuotient I).obj X) = (toMonoidalQuotient I).map (quantumDim X) := by
  simp [Functor.quantumDim_map]

end TauCeti.MonoidalQuotient
