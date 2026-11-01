/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Transport of compactifications along a source isomorphism

A compactification `C` of `f : X ⟶ S` restricts along a quasi-compact open immersion
`e : Y ⟶ X` to a compactification `C.precomp e w` of any `f' : Y ⟶ S` with `e ≫ f = f'`: the
open immersion becomes `e ≫ C.j`, while the ambient scheme and proper map are unchanged.
Refinement maps are unchanged too, so this is a functor `precompFunctor e w`.

For an isomorphism `e : Y ≅ X` of sources, precomposition with `e.hom` and with `e.inv` are
mutually inverse through identity maps of ambient schemes. This identifies the compactifications
of `f` with those of `f'` (`Compactification.sourceIsoEquivalence`), and the equivalence
restricts to schematically dense compactifications
(`DenseCompactification.sourceIsoEquivalence`).

The target morphism `f'` is a separate argument, related to `f` by an equation, rather than
the composite `e ≫ f` itself. Sources are often isomorphic only through a canonical
comparison, for instance two iterated fibre products, and this form avoids casts along
equalities of morphisms there.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ S}

namespace Compactification

/-- Restrict a compactification along a quasi-compact open immersion `e` of sources,
retaining the ambient scheme and the proper map; the open immersion becomes `e ≫ C.j`. -/
-- Dependent interior and ambient-map equations need the unchanged carrier to be visible.
@[expose, implicit_reducible]
def precomp (C : Compactification f) (e : Y ⟶ X) [IsOpenImmersion e] [QuasiCompact e]
    (w : e ≫ f = f') : Compactification f' :=
  ofHom (e ≫ C.j) C.p (by simp [w])

section Precomp

variable (e : Y ⟶ X) [IsOpenImmersion e] [QuasiCompact e] (w : e ≫ f = f')

@[simp]
theorem precomp_Xbar (C : Compactification f) : (C.precomp e w).Xbar = C.Xbar := (rfl)

@[simp]
theorem precomp_j (C : Compactification f) : (C.precomp e w).j = e ≫ C.j := (rfl)

@[simp]
theorem precomp_p (C : Compactification f) : (C.precomp e w).p = C.p := (rfl)

/-- Restriction along `e` preserves schematic density of the interior when `e` is itself
schematically dense, for instance an isomorphism. -/
instance precomp_isSchemeTheoreticallyDominant (C : Compactification f)
    [IsSchemeTheoreticallyDominant C.j] [IsSchemeTheoreticallyDominant e] :
    IsSchemeTheoreticallyDominant (C.precomp e w).j := by
  rw [precomp_j]
  infer_instance

/-- Restriction along `e` acts as the identity on the underlying refinement maps. -/
-- Exposure retains the ambient carriers of the object part for dependent map equations.
@[expose, implicit_reducible, simps! obj map_hom_h]
def precompFunctor : Compactification f ⥤ Compactification f' where
  obj C := C.precomp e w
  map h := ObjectProperty.homMk
    { h := h.hom.h
      ι_h := by simp [precomp]
      h_π := h.hom.h_π }

end Precomp

/-- Restricting along `e.hom` and then along `e.inv` recovers the original compactification,
through the identity of ambient schemes. -/
def precompHomInvIso (C : Compactification f) (e : Y ≅ X) (w : e.hom ≫ f = f') :
    C ≅ (C.precomp e.hom w).precomp e.inv ((Iso.inv_comp_eq e).mpr w.symm) :=
  isoMk (Iso.refl _) (by simp) (by simp)

@[simp]
theorem precompHomInvIso_hom_hom_h (C : Compactification f) (e : Y ≅ X)
    (w : e.hom ≫ f = f') : (C.precompHomInvIso e w).hom.hom.h = 𝟙 C.Xbar :=
  isoMk_hom_hom_h _ _ _

@[simp]
theorem precompHomInvIso_inv_hom_h (C : Compactification f) (e : Y ≅ X)
    (w : e.hom ≫ f = f') : (C.precompHomInvIso e w).inv.hom.h = 𝟙 C.Xbar :=
  isoMk_inv_hom_h _ _ _

variable (f f') in
/-- Isomorphic sources, compatibly with the maps to the base, have equivalent compactification
categories. -/
-- Consumers need the explicitly unchanged ambient carriers in both directions.
@[expose, implicit_reducible]
def sourceIsoEquivalence (e : Y ≅ X) (w : e.hom ≫ f = f') :
    Compactification f ≌ Compactification f' where
  functor := precompFunctor e.hom w
  inverse := precompFunctor e.inv ((Iso.inv_comp_eq e).mpr w.symm)
  unitIso := NatIso.ofComponents (fun C ↦ C.precompHomInvIso e w) (by
    intros
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    simp)
  counitIso := NatIso.ofComponents (fun C ↦ (C.precompHomInvIso e.symm
    ((Iso.inv_comp_eq e).mpr w.symm)).symm) (by
    intros
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
      ObjectProperty.FullSubcategory.comp_hom, Factorisation.comp_h, Iso.symm_hom,
      precompHomInvIso_inv_hom_h, precompFunctor_map_hom_h]
    -- The identities live on definitionally equal but syntactically different carriers.
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp _ := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    simp only [Functor.id_obj, Functor.comp_obj, NatIso.ofComponents_hom_app,
      ObjectProperty.FullSubcategory.comp_hom, Factorisation.comp_h, Iso.symm_hom,
      precompHomInvIso_hom_hom_h, precompHomInvIso_inv_hom_h, precompFunctor_map_hom_h,
      ObjectProperty.FullSubcategory.id_hom, Factorisation.id_h]
    exact Category.id_comp _

-- These whole-functor equations are named rewrites, as for base relabelling.
theorem sourceIsoEquivalence_functor (e : Y ≅ X) (w : e.hom ≫ f = f') :
    (sourceIsoEquivalence f f' e w).functor = precompFunctor e.hom w := (rfl)

theorem sourceIsoEquivalence_inverse (e : Y ≅ X) (w : e.hom ≫ f = f') :
    (sourceIsoEquivalence f f' e w).inverse =
      precompFunctor e.inv ((Iso.inv_comp_eq e).mpr w.symm) := (rfl)

@[simp]
theorem sourceIsoEquivalence_functor_obj_Xbar (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : Compactification f) :
    ((sourceIsoEquivalence f f' e w).functor.obj C).Xbar = C.Xbar := (rfl)

@[simp]
theorem sourceIsoEquivalence_functor_obj_j (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : Compactification f) :
    ((sourceIsoEquivalence f f' e w).functor.obj C).j = e.hom ≫ C.j := (rfl)

@[simp]
theorem sourceIsoEquivalence_functor_obj_p (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : Compactification f) :
    ((sourceIsoEquivalence f f' e w).functor.obj C).p = C.p := (rfl)

@[simp]
theorem sourceIsoEquivalence_functor_map_hom_h (e : Y ≅ X) (w : e.hom ≫ f = f')
    {C D : Compactification f} (h : C ⟶ D) :
    ((sourceIsoEquivalence f f' e w).functor.map h).hom.h = h.hom.h := (rfl)

@[simp]
theorem sourceIsoEquivalence_inverse_obj_Xbar (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : Compactification f') :
    ((sourceIsoEquivalence f f' e w).inverse.obj C).Xbar = C.Xbar := (rfl)

@[simp]
theorem sourceIsoEquivalence_inverse_obj_j (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : Compactification f') :
    ((sourceIsoEquivalence f f' e w).inverse.obj C).j = e.inv ≫ C.j := (rfl)

@[simp]
theorem sourceIsoEquivalence_inverse_obj_p (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : Compactification f') :
    ((sourceIsoEquivalence f f' e w).inverse.obj C).p = C.p := (rfl)

@[simp]
theorem sourceIsoEquivalence_inverse_map_hom_h (e : Y ≅ X) (w : e.hom ≫ f = f')
    {C D : Compactification f'} (h : C ⟶ D) :
    ((sourceIsoEquivalence f f' e w).inverse.map h).hom.h = h.hom.h := (rfl)

@[simp]
theorem sourceIsoEquivalence_unitIso_hom_app_hom_h (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : Compactification f) :
    ((sourceIsoEquivalence f f' e w).unitIso.hom.app C).hom.h = 𝟙 C.Xbar := by
  simp [sourceIsoEquivalence]

@[simp]
theorem sourceIsoEquivalence_unitIso_inv_app_hom_h (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : Compactification f) :
    ((sourceIsoEquivalence f f' e w).unitIso.inv.app C).hom.h = 𝟙 C.Xbar := by
  simp [sourceIsoEquivalence]

@[simp]
theorem sourceIsoEquivalence_counitIso_hom_app_hom_h (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : Compactification f') :
    ((sourceIsoEquivalence f f' e w).counitIso.hom.app C).hom.h = 𝟙 C.Xbar := by
  simp [sourceIsoEquivalence]

@[simp]
theorem sourceIsoEquivalence_counitIso_inv_app_hom_h (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : Compactification f') :
    ((sourceIsoEquivalence f f' e w).counitIso.inv.app C).hom.h = 𝟙 C.Xbar := by
  simp [sourceIsoEquivalence]

end Compactification

namespace DenseCompactification

variable (f f') in
/-- Transport along a source isomorphism restricts to dense compactifications. -/
-- Spell out the functor data, as for base relabelling: the generic restriction's carrier
-- otherwise prevents importing-module simplification of the interior and refinement maps.
@[expose, implicit_reducible]
def sourceIsoEquivalence (e : Y ≅ X) (w : e.hom ≫ f = f') :
    DenseCompactification f ≌ DenseCompactification f' :=
  { (Compactification.sourceIsoEquivalence f f' e w).congrFullSubcategory (by
      ext C
      simp only [ObjectProperty.inverseImage, Compactification.sourceIsoEquivalence,
        denseCompactificationProperty_iff, Compactification.precompFunctor_obj,
        Compactification.precomp_j]
      constructor <;> intro h
      · rw [← e.inv_hom_id_assoc C.j]
        infer_instance
      · infer_instance) with
    functor := (denseCompactificationProperty _).lift
      ((denseCompactificationProperty _).ι ⋙ Compactification.precompFunctor e.hom w)
      (fun C ↦ (denseCompactificationProperty_iff _ _).mpr
        (Compactification.precomp_isSchemeTheoreticallyDominant e.hom w C.obj))
    inverse := (denseCompactificationProperty _).lift
      ((denseCompactificationProperty _).ι ⋙
        Compactification.precompFunctor e.inv ((Iso.inv_comp_eq e).mpr w.symm))
      (fun C ↦ (denseCompactificationProperty_iff _ _).mpr
        (Compactification.precomp_isSchemeTheoreticallyDominant e.inv
          ((Iso.inv_comp_eq e).mpr w.symm) C.obj)) }

@[simp]
theorem sourceIsoEquivalence_functor_obj_Xbar (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : DenseCompactification f) :
    ((sourceIsoEquivalence f f' e w).functor.obj C).obj.Xbar = C.obj.Xbar := (rfl)

@[simp]
theorem sourceIsoEquivalence_functor_obj_j (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : DenseCompactification f) :
    ((sourceIsoEquivalence f f' e w).functor.obj C).obj.j = e.hom ≫ C.obj.j := (rfl)

@[simp]
theorem sourceIsoEquivalence_functor_obj_p (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : DenseCompactification f) :
    ((sourceIsoEquivalence f f' e w).functor.obj C).obj.p = C.obj.p := (rfl)

@[simp]
theorem sourceIsoEquivalence_functor_map_hom_hom_h (e : Y ≅ X) (w : e.hom ≫ f = f')
    {C D : DenseCompactification f} (h : C ⟶ D) :
    ((sourceIsoEquivalence f f' e w).functor.map h).hom.hom.h = h.hom.hom.h := (rfl)

@[simp]
theorem sourceIsoEquivalence_inverse_obj_Xbar (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : DenseCompactification f') :
    ((sourceIsoEquivalence f f' e w).inverse.obj C).obj.Xbar = C.obj.Xbar := (rfl)

@[simp]
theorem sourceIsoEquivalence_inverse_obj_j (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : DenseCompactification f') :
    ((sourceIsoEquivalence f f' e w).inverse.obj C).obj.j = e.inv ≫ C.obj.j := (rfl)

@[simp]
theorem sourceIsoEquivalence_inverse_obj_p (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : DenseCompactification f') :
    ((sourceIsoEquivalence f f' e w).inverse.obj C).obj.p = C.obj.p := (rfl)

@[simp]
theorem sourceIsoEquivalence_inverse_map_hom_hom_h (e : Y ≅ X) (w : e.hom ≫ f = f')
    {C D : DenseCompactification f'} (h : C ⟶ D) :
    ((sourceIsoEquivalence f f' e w).inverse.map h).hom.hom.h = h.hom.hom.h := (rfl)

end DenseCompactification

end TauCeti
