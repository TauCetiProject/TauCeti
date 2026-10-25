/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.Basic

/-!
# Transport of compactifications along source isomorphisms

Changing the source by an isomorphism does not change the ambient proper scheme of a
compactification. This transport lets us compare compactifications whose interiors have
canonically isomorphic, rather than equal, sources, as happens for iterated fibre products.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.Compactification

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ S}

/-- Transport a compactification to an isomorphic source, retaining its ambient scheme. -/
abbrev sourceIso (C : Compactification f) (e : Y ≅ X) (w : e.hom ≫ f = f') :
    Compactification f' :=
  ofHom (e.hom ≫ C.j) C.p (by simp [w])

/-- Source transport acts as the identity on ambient refinement maps. -/
-- Exposure is needed to type the ambient-map computation rule without equality transports.
@[expose, implicit_reducible]
def sourceIsoFunctor (e : Y ≅ X) (w : e.hom ≫ f = f') :
    Compactification f ⥤ Compactification f' where
  obj C := C.sourceIso e w
  map h := ObjectProperty.homMk
    { h := h.hom.h
      ι_h := by simp [sourceIso, Category.assoc]
      h_π := h.hom.h_π }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem sourceIsoFunctor_obj (e : Y ≅ X) (w : e.hom ≫ f = f')
    (C : Compactification f) :
    (sourceIsoFunctor e w).obj C = C.sourceIso e w :=
  (rfl)

@[simp]
theorem sourceIsoFunctor_map_hom_h (e : Y ≅ X) (w : e.hom ≫ f = f')
    {C D : Compactification f} (h : C ⟶ D) :
    ((sourceIsoFunctor e w).map h).hom.h = h.hom.h :=
  (rfl)

/-- An isomorphism of sources induces an equivalence of compactification categories. -/
def sourceIsoEquivalence (e : Y ≅ X) (w : e.hom ≫ f = f') :
    Compactification f ≌ Compactification f' where
  functor := sourceIsoFunctor e w
  inverse := sourceIsoFunctor e.symm (by rw [← w]; simp)
  unitIso := NatIso.ofComponents (fun C ↦ isoMk (Iso.refl C.Xbar)
    (by simp [sourceIsoFunctor, sourceIso]) (by simp [sourceIsoFunctor, sourceIso]))
    (fun h ↦ by
      apply ObjectProperty.hom_ext
      apply Factorisation.Hom.ext
      simp [sourceIsoFunctor])
  counitIso := NatIso.ofComponents (fun C ↦ isoMk (Iso.refl C.Xbar)
    (by simp [sourceIsoFunctor, sourceIso]) (by simp [sourceIsoFunctor, sourceIso]))
    (fun h ↦ by
      apply ObjectProperty.hom_ext
      apply Factorisation.Hom.ext
      simp [sourceIsoFunctor])
  functor_unitIso_comp C := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    simp [sourceIsoFunctor]

@[simp]
theorem sourceIsoEquivalence_functor (e : Y ≅ X) (w : e.hom ≫ f = f') :
    (sourceIsoEquivalence e w).functor = sourceIsoFunctor e w := by
  simp [sourceIsoEquivalence]

@[simp]
theorem sourceIsoEquivalence_inverse (e : Y ≅ X) (w : e.hom ≫ f = f') :
    (sourceIsoEquivalence e w).inverse =
      sourceIsoFunctor e.symm (by rw [← w]; simp) := by
  simp [sourceIsoEquivalence]

@[simp]
theorem sourceIso_Xbar (C : Compactification f) (e : Y ≅ X) (w : e.hom ≫ f = f') :
    (C.sourceIso e w).Xbar = C.Xbar :=
  (rfl)

@[simp]
theorem sourceIso_j (C : Compactification f) (e : Y ≅ X) (w : e.hom ≫ f = f') :
    (C.sourceIso e w).j = e.hom ≫ C.j :=
  (rfl)

@[simp]
theorem sourceIso_p (C : Compactification f) (e : Y ≅ X) (w : e.hom ≫ f = f') :
    (C.sourceIso e w).p = C.p :=
  (rfl)

/-- Source transport preserves scheme-theoretic density. -/
instance (C : Compactification f) [IsSchemeTheoreticallyDominant C.j]
    (e : Y ≅ X) (w : e.hom ≫ f = f') :
    IsSchemeTheoreticallyDominant (C.sourceIso e w).j := by
  rw [sourceIso_j]
  infer_instance

end TauCeti.Compactification
