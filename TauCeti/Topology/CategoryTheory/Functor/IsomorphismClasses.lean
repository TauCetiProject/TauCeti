/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.IsomorphismClasses
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Constructions

/-!
# Coarse maps of refinement functors

Give the isomorphism classes of a category the quotient topology from its objects. A functor
continuous on objects induces a continuous map on these quotients. If its object map is a
quotient map, so is the induced map. Consequently a full functor reflecting isomorphisms whose
object map is quotient induces a homeomorphism
`CategoryTheory.Functor.isomorphismClassesHomeomorph`. This covers fully faithful functors and
full functors out of groupoids. In particular this applies to fully faithful refinements with
open surjective object map.

For groupoids these quotients are the coarse spaces. The construction keeps all arrows and
requires no faithfulness of an isotropy action. It does not require a continuous choice of
inverse functor or of representatives. The homeomorphisms respect composition and naturally
isomorphic functors, as required when comparing different refinements of a presentation.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 2–3.
-/

public noncomputable section

open Topology

universe v u

namespace CategoryTheory.Functor

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace E]

/-- A functor continuous on objects induces a continuous map on isomorphism classes with
their quotient topologies. -/
theorem continuous_isomorphismClasses_map (F : C ⥤ D) (hF : Continuous F.obj) :
    Continuous (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map F.toCatHom) := by
  exact (isQuotientMap_quotient_mk' (X := C) (s := isIsomorphicSetoid C)).continuous_iff.2
    (F.isomorphismClasses_map_comp_mk.symm ▸ continuous_quotient_mk'.comp hF)

/-- A functor whose object map is quotient induces a quotient map on isomorphism classes. -/
theorem isQuotientMap_isomorphismClasses_map (F : C ⥤ D) (hF : IsQuotientMap F.obj) :
    IsQuotientMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map F.toCatHom) := by
  exact (isQuotientMap_quotient_mk' (X := C) (s := isIsomorphicSetoid C)).of_comp_isQuotientMap
    (F.isomorphismClasses_map_comp_mk.symm ▸
      (isQuotientMap_quotient_mk' (X := D) (s := isIsomorphicSetoid D)).comp hF)

/-- A full functor reflecting isomorphisms, for instance a fully faithful functor, with quotient
object map identifies the spaces of isomorphism classes homeomorphically. For groupoids this is
the coarse homeomorphism of the refinement. -/
def isomorphismClassesHomeomorph (F : C ⥤ D) [F.Full] [F.ReflectsIsomorphisms]
    (hF : IsQuotientMap F.obj) :
    Quotient (isIsomorphicSetoid C) ≃ₜ Quotient (isIsomorphicSetoid D) :=
  (isHomeomorph_iff_isQuotientMap_injective
    (X := Quotient (isIsomorphicSetoid C)) (Y := Quotient (isIsomorphicSetoid D))).2
    ⟨F.isQuotientMap_isomorphismClasses_map hF, F.isomorphismClasses_map_injective⟩ |>.homeomorph _

-- The underlying function is preserved by `IsHomeomorph.homeomorph`.
/-- The coarse homeomorphism has Mathlib's map on isomorphism classes as its underlying
function. -/
@[simp]
theorem coe_isomorphismClassesHomeomorph (F : C ⥤ D) [F.Full] [F.ReflectsIsomorphisms]
    (hF : IsQuotientMap F.obj) :
    ⇑(F.isomorphismClassesHomeomorph hF) =
      (isomorphismClasses.map F.toCatHom :
        Quotient (isIsomorphicSetoid C) → Quotient (isIsomorphicSetoid D)) := (rfl)

/-- The coarse homeomorphism sends the class of an object to the class of its image. -/
@[simp]
theorem isomorphismClassesHomeomorph_apply_mk (F : C ⥤ D) [F.Full] [F.ReflectsIsomorphisms]
    (hF : IsQuotientMap F.obj) (x : C) :
    F.isomorphismClassesHomeomorph hF (Quotient.mk _ x) =
      Quotient.mk _ (F.obj x) := by
  simp only [coe_isomorphismClassesHomeomorph, isomorphismClasses_map_mk]

/-- The inverse coarse homeomorphism takes the class of an image object back to its class. -/
@[simp]
theorem isomorphismClassesHomeomorph_symm_apply_mk (F : C ⥤ D) [F.Full] [F.ReflectsIsomorphisms]
    (hF : IsQuotientMap F.obj) (x : C) :
    (F.isomorphismClassesHomeomorph hF).symm (Quotient.mk _ (F.obj x)) =
      Quotient.mk _ x := by
  simpa only [isomorphismClassesHomeomorph_apply_mk] using
    (F.isomorphismClassesHomeomorph hF).symm_apply_apply (Quotient.mk _ x)

/-- The identity refinement induces the identity coarse homeomorphism. -/
@[simp]
theorem isomorphismClassesHomeomorph_id :
    (𝟭 C).isomorphismClassesHomeomorph IsQuotientMap.id = Homeomorph.refl _ := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => simp

/-- Composing refinements composes their coarse homeomorphisms in the same order. -/
@[simp]
theorem isomorphismClassesHomeomorph_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Full] [F.ReflectsIsomorphisms] [G.Full] [G.ReflectsIsomorphisms]
    (hF : IsQuotientMap F.obj) (hG : IsQuotientMap G.obj) :
    (F ⋙ G).isomorphismClassesHomeomorph (hG.comp hF) =
      (F.isomorphismClassesHomeomorph hF).trans (G.isomorphismClassesHomeomorph hG) := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => simp

/-- Naturally isomorphic refinements give equal coarse homeomorphisms. -/
theorem isomorphismClassesHomeomorph_eq_of_iso (F : C ⥤ D) (G : C ⥤ D)
    [F.Full] [F.ReflectsIsomorphisms] [G.Full] [G.ReflectsIsomorphisms]
    (hF : IsQuotientMap F.obj) (hG : IsQuotientMap G.obj) (e : F ≅ G) :
    F.isomorphismClassesHomeomorph hF = G.isomorphismClassesHomeomorph hG := by
  ext q
  simp only [coe_isomorphismClassesHomeomorph]
  exact ConcreteCategory.congr_hom (F.isomorphismClasses_map_eq_of_iso e) q

end CategoryTheory.Functor
