/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.GTopology.Basic
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Classical points and neighbourhood stalks of a G-site

Each point of the underlying set of a G-topological space defines a point of its site.
Its fiber on a presheaf is the colimit over admissible neighbourhoods, with the usual
restriction maps. This identifies classical neighbourhood stalks with native site fibers,
so the site-point API applies without introducing a separate category of sheaves or stalks.
For the G-topology of ordinary open covers, the comparison recovers Mathlib's stalk.

The construction of `point` adapts `Opens.pointGrothendieckTopology` in Mathlib
(by Joël Riou), replacing ordinary open covers by admissible covers. Classical points
need not form a conservative family for an arbitrary G-topology: a set-theoretic cover
need not be admissible.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §9.1.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace TauCeti.GTopology

variable {X : Type u} {B : Type v} [SemilatticeInf B] [OrderTop B]
  {ι : B ↪o Set X} (G : GTopology ι)

/-- The site point associated to `x`: its fiber on an admissible open is a singleton
if the open contains `x`, and is empty otherwise. -/
@[expose, simps! fiber_obj]
def point (x : X) : GrothendieckTopology.Point.{v} G.grothendieckTopology where
  fiber.obj U := ULift.{v} (PLift (x ∈ ι U))
  fiber.map f := ↾fun h ↦ ⟨⟨ι.monotone (leOfHom f) h.down.down⟩⟩
  isCofiltered :=
    { nonempty := ⟨.mk (obj := ⊤) ⟨⟨G.map_top.symm ▸ Set.mem_univ x⟩⟩⟩
      cone_objs U V := by
        induction U with | @mk U hU
        induction V with | @mk V hV
        obtain ⟨⟨hU⟩⟩ := hU
        obtain ⟨⟨hV⟩⟩ := hV
        exact ⟨.mk (obj := U ⊓ V) ⟨⟨(G.map_inf U V).symm ▸ ⟨hU, hV⟩⟩⟩,
          Functor.Elements.homMk (homOfLE inf_le_left) rfl,
          Functor.Elements.homMk (homOfLE inf_le_right) rfl, by tauto⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U R hR ⟨⟨hx⟩⟩
    obtain ⟨S, hS, hSR⟩ := G.mem_grothendieckTopology_iff.mp hR
    rw [← G.union_eq hS] at hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV⟩ := hx
    exact ⟨V, homOfLE (G.subset hS V hV),
      hSR _ _ ((coverPresieve_apply _ _).mpr hV), ⟨⟨hxV⟩⟩, rfl⟩

/-- The element of the fiber on an admissible open containing the point. -/
def pointElement (x : X) {U : B} (hx : x ∈ ι U) : (G.point x).fiber.obj U :=
  ⟨⟨hx⟩⟩

/-- Every element of the fiber is the element determined by its membership proof. -/
theorem pointElement_down (x : X) (U : B) (h : (G.point x).fiber.obj U) :
    G.pointElement x h.down.down = h := (rfl)

@[simp]
theorem point_map_pointElement (x : X) {U V : B} (f : U ⟶ V) (hx : x ∈ ι U) :
    (G.point x).fiber.map f (G.pointElement x hx) =
      G.pointElement x (ι.monotone (leOfHom f) hx) := (rfl)

/-- The forgetful functor from admissible neighbourhoods of a point to admissible opens. -/
@[simps!]
abbrev neighbourhoodInclusion (x : X) : {U : B // x ∈ ι U} ⥤ B :=
  (Subtype.mono_coe _).functor

section Fibers

variable {A : Type w} [Category.{t} A] [HasColimitsOfSize.{v, v} A]
  (x : X) (P : Bᵒᵖ ⥤ A)

/-- The cocone of germs into the fiber of the classical site point, indexed by admissible
neighbourhoods of that point. -/
noncomputable def neighbourhoodCocone : Cocone ((neighbourhoodInclusion (ι := ι) x).op ⋙ P) where
  pt := (G.point x).presheafFiber.obj P
  ι.app U := (G.point x).toPresheafFiber U.unop.1 (G.pointElement x U.unop.2) P
  ι.naturality _ V f :=
    ((G.point x).toPresheafFiber_w
      ((neighbourhoodInclusion (ι := ι) x).map f.unop)
        (G.pointElement x V.unop.2) P).trans (Category.comp_id _).symm

/-- The fiber at a classical site point satisfies the colimit universal property for
admissible neighbourhoods. This holds for presheaves, without a sheaf hypothesis. -/
noncomputable def isColimitNeighbourhoodCocone :
    IsColimit (G.neighbourhoodCocone x P) where
  desc c := (G.point x).presheafFiberDesc
    (fun U h ↦ c.ι.app (op ⟨U, h.down.down⟩))
    (fun {U V} f h ↦ c.w (homOfLE (leOfHom f) :
      (⟨U, h.down.down⟩ : {U : B // x ∈ ι U}) ⟶
        ⟨V, ι.monotone (leOfHom f) h.down.down⟩).op)
  fac c U := by
    exact (G.point x).toPresheafFiber_presheafFiberDesc _ _ _ _
  uniq c m hm := by
    apply (G.point x).presheafFiber_hom_ext
    intro U h
    have hf := (G.point x).toPresheafFiber_presheafFiberDesc
      (fun V h ↦ c.ι.app (op ⟨V, h.down.down⟩))
      (fun {U V} f h ↦ c.w (homOfLE (leOfHom f) :
        (⟨U, h.down.down⟩ : {U : B // x ∈ ι U}) ⟶
          ⟨V, ι.monotone (leOfHom f) h.down.down⟩).op) U h
    exact (congrArg (fun z ↦ (G.point x).toPresheafFiber U z P ≫ m)
      (G.pointElement_down x U h)).symm.trans
        ((hm (op ⟨U, h.down.down⟩)).trans hf.symm)

/-- The canonical identification of a classical site fiber with the colimit over admissible
neighbourhoods. -/
noncomputable def neighbourhoodColimitIso :
    (G.point x).presheafFiber.obj P ≅ colimit ((neighbourhoodInclusion (ι := ι) x).op ⋙ P) :=
  (G.isColimitNeighbourhoodCocone x P).coconePointUniqueUpToIso (colimit.isColimit _)

/-- The comparison carries the site germ of a section to its neighbourhood-colimit germ. -/
@[simp, reassoc (attr := simp)]
theorem toPresheafFiber_neighbourhoodColimitIso_hom (U : B) (hx : x ∈ ι U) :
    (G.point x).toPresheafFiber U (G.pointElement x hx) P ≫
      (G.neighbourhoodColimitIso x P).hom =
        colimit.ι ((neighbourhoodInclusion (ι := ι) x).op ⋙ P) (op ⟨U, hx⟩) :=
  (G.isColimitNeighbourhoodCocone x P).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) (op ⟨U, hx⟩)

/-- The inverse comparison carries a neighbourhood-colimit germ to the site germ. -/
@[simp, reassoc (attr := simp)]
theorem colimit_ι_neighbourhoodColimitIso_inv (U : B) (hx : x ∈ ι U) :
    colimit.ι ((neighbourhoodInclusion (ι := ι) x).op ⋙ P) (op ⟨U, hx⟩) ≫
      (G.neighbourhoodColimitIso x P).inv =
        (G.point x).toPresheafFiber U (G.pointElement x hx) P :=
  (G.isColimitNeighbourhoodCocone x P).comp_coconePointUniqueUpToIso_inv
    (colimit.isColimit _) (op ⟨U, hx⟩)

/-- The neighbourhood-colimit comparison is natural in the presheaf. -/
@[reassoc]
theorem neighbourhoodColimitIso_naturality {Q : Bᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (G.point x).presheafFiber.map f ≫ (G.neighbourhoodColimitIso x Q).hom =
      (G.neighbourhoodColimitIso x P).hom ≫
        colimMap (Functor.whiskerLeft (neighbourhoodInclusion (ι := ι) x).op f) := by
  apply (G.point x).presheafFiber_hom_ext
  intro U h
  calc
    _ = f.app (op U) ≫ (G.point x).toPresheafFiber U h Q ≫
        (G.neighbourhoodColimitIso x Q).hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (G.neighbourhoodColimitIso x Q).hom)
          ((G.point x).toPresheafFiber_naturality f U h)) |>.trans (Category.assoc _ _ _)
    _ = _ := by
      have hP := G.toPresheafFiber_neighbourhoodColimitIso_hom x P U h.down.down
      have hQ := G.toPresheafFiber_neighbourhoodColimitIso_hom x Q U h.down.down
      rw [G.pointElement_down x U h] at hP hQ
      rw [hQ, ← Category.assoc, hP]
      exact (ι_colimMap (Functor.whiskerLeft (neighbourhoodInclusion (ι := ι) x).op f)
        (op ⟨U, h.down.down⟩)).symm

end Fibers

section Topological

open TopologicalSpace TopCat.Presheaf

variable {Y : TopCat.{v}} {A : Type w} [Category.{v} A] [HasColimitsOfSize.{v, v} A]

-- The G-site and the topological site bundle membership differently; the underlying
-- neighbourhoods and their inclusion order are identical.
private def topologicalNeighbourhoodOrderIso (x : Y) :
    {U : Opens Y // x ∈ opensEmbedding Y U} ≃o OpenNhds x where
  toFun U := ⟨U.1, by simpa using U.2⟩
  invFun U := ⟨U.1, by simpa using U.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private def topologicalNeighbourhoodDiagramIso (x : Y) (P : Y.Presheaf A) :
    (topologicalNeighbourhoodOrderIso x).equivalence.op.functor ⋙
        (OpenNhds.inclusion x).op ⋙ P ≅
      (neighbourhoodInclusion (ι := opensEmbedding Y) x).op ⋙ P :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm)

private noncomputable def topologicalNeighbourhoodColimitIso (x : Y) (P : Y.Presheaf A) :
    colimit ((neighbourhoodInclusion (ι := opensEmbedding Y) x).op ⋙ P) ≅ P.stalk x :=
  HasColimit.isoOfEquivalence (topologicalNeighbourhoodOrderIso x).equivalence.op
    (topologicalNeighbourhoodDiagramIso x P)

@[simp]
private theorem colimit_ι_topologicalNeighbourhoodColimitIso_hom (x : Y) (P : Y.Presheaf A)
    (U : Opens Y) (hx : x ∈ opensEmbedding Y U) :
    colimit.ι ((neighbourhoodInclusion (ι := opensEmbedding Y) x).op ⋙ P) (op ⟨U, hx⟩) ≫
        (topologicalNeighbourhoodColimitIso x P).hom =
      P.germ U x (by simpa using hx) :=
  (HasColimit.ι_isoOfEquivalence_hom (topologicalNeighbourhoodOrderIso x).equivalence.op
    (topologicalNeighbourhoodDiagramIso x P) (op ⟨U, hx⟩)).trans (Category.id_comp _)

/-- For the G-topology of ordinary open covers, the classical site fiber is Mathlib's
ordinary stalk. -/
noncomputable def topologicalStalkIso (x : Y) (P : Y.Presheaf A) :
    ((topological Y).point x).presheafFiber.obj P ≅ P.stalk x :=
  ((topological Y).neighbourhoodColimitIso x P).trans
    (topologicalNeighbourhoodColimitIso x P)

/-- The topological comparison preserves germs of sections. -/
@[simp, reassoc (attr := simp)]
theorem toPresheafFiber_topologicalStalkIso_hom (x : Y) (P : Y.Presheaf A)
    (U : Opens Y) (hx : x ∈ U) :
    ((topological Y).point x).toPresheafFiber U
        ((topological Y).pointElement x (by simpa using hx)) P ≫
      (topologicalStalkIso x P).hom = P.germ U x hx := by
  simp [topologicalStalkIso, Iso.trans_hom, ← Category.assoc]

/-- The inverse topological comparison preserves germs of sections. -/
@[simp, reassoc (attr := simp)]
theorem germ_topologicalStalkIso_inv (x : Y) (P : Y.Presheaf A)
    (U : Opens Y) (hx : x ∈ U) :
    P.germ U x hx ≫ (topologicalStalkIso x P).inv =
      ((topological Y).point x).toPresheafFiber U
        ((topological Y).pointElement x (by simpa using hx)) P := by
  rw [← toPresheafFiber_topologicalStalkIso_hom x P U hx]
  simp

end Topological

end TauCeti.GTopology
