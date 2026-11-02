/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Transport of compactifications along a base isomorphism

An isomorphism of bases identifies their categories of compactifications by postcomposing
the proper structure map. The ambient scheme, the open interior and every refinement map
are unchanged. In particular this equivalence restricts to schematically dense
compactifications, without any reducedness or finiteness assumption on the base.

The inverse is constructed directly over the original base, rather than by transporting
along an equality of composite morphisms. The unit and counit are identity maps of ambient
schemes.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti

variable {X S T : Scheme.{u}} {f : X ⟶ S}

namespace Compactification

/-- Relabel the base by an isomorphism, retaining the ambient scheme and open interior. -/
-- Dependent interior and ambient-map equations need the unchanged carrier to be visible.
@[expose, implicit_reducible]
def baseIso (C : Compactification f) (e : S ≅ T) : Compactification (f ≫ e.hom) :=
  ofHom C.j (C.p ≫ e.hom) (by simp)

@[simp]
theorem baseIso_Xbar (C : Compactification f) (e : S ≅ T) :
    (C.baseIso e).Xbar = C.Xbar := (rfl)

@[simp]
theorem baseIso_j (C : Compactification f) (e : S ≅ T) :
    (C.baseIso e).j = C.j := (rfl)

@[simp]
theorem baseIso_p (C : Compactification f) (e : S ≅ T) :
    (C.baseIso e).p = C.p ≫ e.hom := (rfl)

/-- Base relabelling acts as the identity on the underlying refinement maps. -/
-- Exposure retains the ambient carriers of the object part for dependent map equations.
@[expose, implicit_reducible, simps! obj map_hom_h]
def baseIsoFunctor (e : S ≅ T) : Compactification f ⥤ Compactification (f ≫ e.hom) where
  obj C := C.baseIso e
  map h := ObjectProperty.homMk
    { h := h.hom.h
      ι_h := h.hom.ι_h
      h_π := by simp [← Category.assoc] }

/-- Undo base relabelling, with the result directly indexed by the original morphism. -/
-- This direct construction avoids casts through `(f ≫ e.hom) ≫ e.inv = f`.
@[expose, implicit_reducible]
def baseIsoInverse {e : S ≅ T} (C : Compactification (f ≫ e.hom)) : Compactification f :=
  ofHom C.j (C.p ≫ e.inv) (by
    rw [← Category.assoc, C.obj.ι_π]
    simp [Category.assoc])

@[simp]
theorem baseIsoInverse_Xbar (e : S ≅ T) (C : Compactification (f ≫ e.hom)) :
    (C.baseIsoInverse (e := e)).Xbar = C.Xbar := (rfl)

@[simp]
theorem baseIsoInverse_j (e : S ≅ T) (C : Compactification (f ≫ e.hom)) :
    (C.baseIsoInverse (e := e)).j = C.j := (rfl)

@[simp]
theorem baseIsoInverse_p (e : S ≅ T) (C : Compactification (f ≫ e.hom)) :
    (C.baseIsoInverse (e := e)).p = C.p ≫ e.inv := (rfl)

/-- The inverse base-relabelling functor. -/
-- Exposure retains the ambient carriers of the object part for dependent map equations.
@[expose, implicit_reducible, simps! obj map_hom_h]
def baseIsoInverseFunctor (e : S ≅ T) :
    Compactification (f ≫ e.hom) ⥤ Compactification f where
  obj C := C.baseIsoInverse (e := e)
  map h := ObjectProperty.homMk
    { h := h.hom.h
      ι_h := h.hom.ι_h
      h_π := by simp [← Category.assoc] }

/-- Isomorphic bases have equivalent compactification categories. -/
-- Consumers need the explicitly unchanged ambient carriers in both directions.
@[expose, implicit_reducible]
def baseIsoEquivalence (f : X ⟶ S) (e : S ≅ T) :
    Compactification f ≌ Compactification (f ≫ e.hom) where
  functor := baseIsoFunctor e
  inverse := baseIsoInverseFunctor e
  unitIso := NatIso.ofComponents (fun C ↦
    { hom := ObjectProperty.homMk
        { h := 𝟙 C.Xbar
          h_π := by
            simp [baseIsoFunctor, baseIsoInverseFunctor, Xbar, p, Category.assoc] }
      inv := ObjectProperty.homMk
        { h := 𝟙 C.Xbar
          h_π := by
            simp only [Functor.comp_obj, baseIsoFunctor_obj, baseIsoInverseFunctor_obj,
              Functor.id_obj, baseIsoInverse_p, baseIso_p, Category.assoc, Iso.hom_inv_id,
              Category.comp_id]
            exact Category.id_comp _ }
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        apply Factorisation.Hom.ext
        simp [baseIsoFunctor, baseIsoInverseFunctor, baseIso, baseIsoInverse]
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        apply Factorisation.Hom.ext
        simp [baseIsoFunctor, baseIsoInverseFunctor, baseIso, baseIsoInverse] }) (by
      intros
      apply ObjectProperty.hom_ext
      apply Factorisation.Hom.ext
      simp [baseIsoFunctor, baseIsoInverseFunctor, baseIso, baseIsoInverse])
  counitIso := NatIso.ofComponents (fun C ↦
    { hom := ObjectProperty.homMk
        { h := 𝟙 C.Xbar
          h_π := by
            simp only [Functor.comp_obj, baseIsoInverseFunctor_obj, baseIsoFunctor_obj,
              Functor.id_obj, baseIso_p, baseIsoInverse_p, Category.assoc, Iso.inv_hom_id,
              Category.comp_id]
            exact Category.id_comp _ }
      inv := ObjectProperty.homMk
        { h := 𝟙 C.Xbar
          h_π := by
            simp [baseIsoFunctor, baseIsoInverseFunctor, Xbar, p, Category.assoc] }
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        apply Factorisation.Hom.ext
        simp [baseIsoFunctor, baseIsoInverseFunctor, baseIso, baseIsoInverse]
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        apply Factorisation.Hom.ext
        simp [baseIsoFunctor, baseIsoInverseFunctor, baseIso, baseIsoInverse] }) (by
      intros
      apply ObjectProperty.hom_ext
      apply Factorisation.Hom.ext
      simp [baseIsoFunctor, baseIsoInverseFunctor, baseIso, baseIsoInverse])

-- These whole-functor equations are named rewrites: making them simp rules disrupts
-- dependent ambient carriers in ordinary importing-module projection and map checks.
theorem baseIsoEquivalence_functor (e : S ≅ T) :
    (baseIsoEquivalence f e).functor = baseIsoFunctor e := (rfl)

theorem baseIsoEquivalence_inverse (e : S ≅ T) :
    (baseIsoEquivalence f e).inverse = baseIsoInverseFunctor e := (rfl)

@[simp]
theorem baseIsoEquivalence_functor_obj_Xbar (e : S ≅ T) (C : Compactification f) :
    ((baseIsoEquivalence f e).functor.obj C).Xbar = C.Xbar := (rfl)

@[simp]
theorem baseIsoEquivalence_functor_obj_j (e : S ≅ T) (C : Compactification f) :
    ((baseIsoEquivalence f e).functor.obj C).j = C.j := (rfl)

@[simp]
theorem baseIsoEquivalence_functor_obj_p (e : S ≅ T) (C : Compactification f) :
    ((baseIsoEquivalence f e).functor.obj C).p = C.p ≫ e.hom := (rfl)

@[simp]
theorem baseIsoEquivalence_functor_map_hom_h (e : S ≅ T)
    {C D : Compactification f} (h : C ⟶ D) :
    ((baseIsoEquivalence f e).functor.map h).hom.h = h.hom.h := (rfl)

@[simp]
theorem baseIsoEquivalence_inverse_obj_Xbar (e : S ≅ T) (C : Compactification (f ≫ e.hom)) :
    ((baseIsoEquivalence f e).inverse.obj C).Xbar = C.Xbar := (rfl)

@[simp]
theorem baseIsoEquivalence_inverse_obj_j (e : S ≅ T) (C : Compactification (f ≫ e.hom)) :
    ((baseIsoEquivalence f e).inverse.obj C).j = C.j := (rfl)

@[simp]
theorem baseIsoEquivalence_inverse_obj_p (e : S ≅ T) (C : Compactification (f ≫ e.hom)) :
    ((baseIsoEquivalence f e).inverse.obj C).p = C.p ≫ e.inv := (rfl)

@[simp]
theorem baseIsoEquivalence_inverse_map_hom_h (e : S ≅ T)
    {C D : Compactification (f ≫ e.hom)} (h : C ⟶ D) :
    ((baseIsoEquivalence f e).inverse.map h).hom.h = h.hom.h := (rfl)

@[simp]
theorem baseIsoEquivalence_unitIso_hom_app_hom_h (e : S ≅ T) (C : Compactification f) :
    ((baseIsoEquivalence f e).unitIso.hom.app C).hom.h = 𝟙 C.Xbar := (rfl)

@[simp]
theorem baseIsoEquivalence_counitIso_hom_app_hom_h (e : S ≅ T)
    (C : Compactification (f ≫ e.hom)) :
    ((baseIsoEquivalence f e).counitIso.hom.app C).hom.h = 𝟙 C.Xbar := (rfl)

@[simp]
theorem baseIsoEquivalence_unitIso_inv_app_hom_h (e : S ≅ T) (C : Compactification f) :
    ((baseIsoEquivalence f e).unitIso.inv.app C).hom.h = 𝟙 C.Xbar := (rfl)

@[simp]
theorem baseIsoEquivalence_counitIso_inv_app_hom_h (e : S ≅ T)
    (C : Compactification (f ≫ e.hom)) :
    ((baseIsoEquivalence f e).counitIso.inv.app C).hom.h = 𝟙 C.Xbar := (rfl)

end Compactification

namespace DenseCompactification

/-- Base relabelling preserves schematic density, since the interior is unchanged. -/
-- The underlying compactification must remain visible for dependent projection formulas.
-- Spell out the functor data: the generic restriction's semireducible carrier otherwise
-- prevents ordinary importing-module simplification of the interior and refinement maps.
-- Its unit, counit and coherence proofs are still supplied by the generic restriction.
@[expose, implicit_reducible]
def baseIsoEquivalence (f : X ⟶ S) (e : S ≅ T) :
    DenseCompactification f ≌ DenseCompactification (f ≫ e.hom) :=
  { (Compactification.baseIsoEquivalence f e).congrFullSubcategory (by
      ext C
      simp [ObjectProperty.inverseImage, Compactification.baseIsoEquivalence]) with
    functor := (denseCompactificationProperty _).lift
      ((denseCompactificationProperty _).ι ⋙ Compactification.baseIsoFunctor e)
      (fun C ↦ (denseCompactificationProperty_iff _ _).mpr (inferInstanceAs
        (IsSchemeTheoreticallyDominant C.obj.j)))
    inverse := (denseCompactificationProperty _).lift
      ((denseCompactificationProperty _).ι ⋙ Compactification.baseIsoInverseFunctor e)
      (fun C ↦ (denseCompactificationProperty_iff _ _).mpr (inferInstanceAs
        (IsSchemeTheoreticallyDominant C.obj.j))) }

@[simp]
theorem baseIsoEquivalence_functor_obj_Xbar (e : S ≅ T)
    (C : DenseCompactification f) :
    ((baseIsoEquivalence f e).functor.obj C).obj.Xbar = C.obj.Xbar := (rfl)

@[simp]
theorem baseIsoEquivalence_functor_obj_j (e : S ≅ T)
    (C : DenseCompactification f) :
    ((baseIsoEquivalence f e).functor.obj C).obj.j = C.obj.j := (rfl)

@[simp]
theorem baseIsoEquivalence_functor_obj_p (e : S ≅ T)
    (C : DenseCompactification f) :
    ((baseIsoEquivalence f e).functor.obj C).obj.p = C.obj.p ≫ e.hom := (rfl)

@[simp]
theorem baseIsoEquivalence_functor_map_hom_hom_h (e : S ≅ T)
    {C D : DenseCompactification f} (h : C ⟶ D) :
    ((baseIsoEquivalence f e).functor.map h).hom.hom.h = h.hom.hom.h := (rfl)

@[simp]
theorem baseIsoEquivalence_inverse_obj_Xbar (e : S ≅ T)
    (C : DenseCompactification (f ≫ e.hom)) :
    ((baseIsoEquivalence f e).inverse.obj C).obj.Xbar = C.obj.Xbar := (rfl)

@[simp]
theorem baseIsoEquivalence_inverse_obj_j (e : S ≅ T)
    (C : DenseCompactification (f ≫ e.hom)) :
    ((baseIsoEquivalence f e).inverse.obj C).obj.j = C.obj.j := (rfl)

@[simp]
theorem baseIsoEquivalence_inverse_obj_p (e : S ≅ T)
    (C : DenseCompactification (f ≫ e.hom)) :
    ((baseIsoEquivalence f e).inverse.obj C).obj.p = C.obj.p ≫ e.inv := (rfl)

@[simp]
theorem baseIsoEquivalence_inverse_map_hom_hom_h (e : S ≅ T)
    {C D : DenseCompactification (f ≫ e.hom)} (h : C ⟶ D) :
    ((baseIsoEquivalence f e).inverse.map h).hom.hom.h = h.hom.hom.h := (rfl)

@[simp]
theorem baseIsoEquivalence_unitIso_hom_app_hom_hom_h (e : S ≅ T)
    (C : DenseCompactification f) :
    ((baseIsoEquivalence f e).unitIso.hom.app C).hom.hom.h = 𝟙 C.obj.Xbar := (rfl)

@[simp]
theorem baseIsoEquivalence_unitIso_inv_app_hom_hom_h (e : S ≅ T)
    (C : DenseCompactification f) :
    ((baseIsoEquivalence f e).unitIso.inv.app C).hom.hom.h = 𝟙 C.obj.Xbar := (rfl)

@[simp]
theorem baseIsoEquivalence_counitIso_hom_app_hom_hom_h (e : S ≅ T)
    (C : DenseCompactification (f ≫ e.hom)) :
    ((baseIsoEquivalence f e).counitIso.hom.app C).hom.hom.h = 𝟙 C.obj.Xbar := (rfl)

@[simp]
theorem baseIsoEquivalence_counitIso_inv_app_hom_hom_h (e : S ≅ T)
    (C : DenseCompactification (f ≫ e.hom)) :
    ((baseIsoEquivalence f e).counitIso.inv.app C).hom.hom.h = 𝟙 C.obj.Xbar := (rfl)

end DenseCompactification

end TauCeti
