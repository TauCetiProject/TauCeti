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
For coefficients in a concrete category whose forgetful functor preserves filtered colimits,
every element of a classical stalk is a germ, and two sections have the same germ exactly
when they agree on a common smaller admissible neighbourhood.

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

/-- The fiber of the classical point over an admissible open is inhabited exactly when the
open contains the point. -/
theorem nonempty_point_fiber_obj_iff (x : X) (U : B) :
    Nonempty ((G.point x).fiber.obj U) ↔ x ∈ ι U :=
  ⟨fun ⟨h⟩ ↦ h.down.down, fun h ↦ ⟨G.pointElement x h⟩⟩

/-- The fiber of any point of the G-site over an admissible open has at most one element:
the open maps monomorphically to the terminal admissible open `⊤`, since the site is a poset. -/
instance (U : B) (Φ : GrothendieckTopology.Point.{v} G.grothendieckTopology) :
    Subsingleton (Φ.fiber.obj U) :=
  Φ.subsingleton_fiber_obj (homOfLE le_top) isTerminalTop

/-- The forgetful functor from admissible neighbourhoods of a point to admissible opens. -/
@[simps!]
abbrev nhdsInclusion (x : X) : {U : B // x ∈ ι U} ⥤ B :=
  (Subtype.mono_coe _).functor

section Fibers

variable {A : Type w} [Category.{t} A] [HasColimitsOfSize.{v, v} A]
  (x : X) (P : Bᵒᵖ ⥤ A)

/-- The cocone of germs into the fiber of the classical site point, indexed by admissible
neighbourhoods of that point. -/
noncomputable def nhdsCocone : Cocone ((nhdsInclusion (ι := ι) x).op ⋙ P) where
  pt := (G.point x).presheafFiber.obj P
  ι.app U := (G.point x).toPresheafFiber U.unop.1 (G.pointElement x U.unop.2) P
  ι.naturality _ V f :=
    ((G.point x).toPresheafFiber_w
      ((nhdsInclusion (ι := ι) x).map f.unop)
        (G.pointElement x V.unop.2) P).trans (Category.comp_id _).symm

/-- The fiber at a classical site point satisfies the colimit universal property for
admissible neighbourhoods. This holds for presheaves, without a sheaf hypothesis. -/
noncomputable def isColimitNhdsCocone : IsColimit (G.nhdsCocone x P) := by
  let desc (c : Cocone ((nhdsInclusion (ι := ι) x).op ⋙ P)) :=
    (G.point x).presheafFiberDesc
      (fun U h ↦ c.ι.app (op ⟨U, h.down.down⟩))
      (fun {U V} f h ↦ c.w (homOfLE (leOfHom f) :
        (⟨U, h.down.down⟩ : {U : B // x ∈ ι U}) ⟶
          ⟨V, ι.monotone (leOfHom f) h.down.down⟩).op)
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro c U
    -- Op/unop and subtype eta identify the reconstructed neighbourhood with U.
    exact (G.point x).toPresheafFiber_presheafFiberDesc _ _ _ _
  · intro c m hm
    apply (G.point x).presheafFiber_hom_ext
    intro U h
    simp [desc, ← hm, nhdsCocone, G.pointElement_down x U h]

/-- The canonical identification of a classical site fiber with the colimit over admissible
neighbourhoods. -/
noncomputable def nhdsColimitIso :
    (G.point x).presheafFiber.obj P ≅ colimit ((nhdsInclusion (ι := ι) x).op ⋙ P) :=
  (G.isColimitNhdsCocone x P).coconePointUniqueUpToIso (colimit.isColimit _)

/-- The comparison carries the site germ of a section to its neighbourhood-colimit germ. -/
@[simp, reassoc (attr := simp)]
theorem toPresheafFiber_nhdsColimitIso_hom (U : B) (h : (G.point x).fiber.obj U) :
    (G.point x).toPresheafFiber U h P ≫ (G.nhdsColimitIso x P).hom =
      colimit.ι ((nhdsInclusion (ι := ι) x).op ⋙ P) (op ⟨U, h.down.down⟩) :=
  (G.isColimitNhdsCocone x P).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) (op ⟨U, h.down.down⟩)

/-- The inverse comparison carries a neighbourhood-colimit germ to the site germ. -/
@[simp, reassoc (attr := simp)]
theorem ι_nhdsColimitIso_inv (U : B) (h : (G.point x).fiber.obj U) :
    colimit.ι ((nhdsInclusion (ι := ι) x).op ⋙ P) (op ⟨U, h.down.down⟩) ≫
      (G.nhdsColimitIso x P).inv = (G.point x).toPresheafFiber U h P :=
  (G.isColimitNhdsCocone x P).comp_coconePointUniqueUpToIso_inv
    (colimit.isColimit _) (op ⟨U, h.down.down⟩)

/-- The neighbourhood-colimit comparison is natural in the presheaf. -/
@[reassoc]
theorem nhdsColimitIso_naturality {Q : Bᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (G.point x).presheafFiber.map f ≫ (G.nhdsColimitIso x Q).hom =
      (G.nhdsColimitIso x P).hom ≫
        colimMap (Functor.whiskerLeft (nhdsInclusion (ι := ι) x).op f) := by
  ext U h
  simp

end Fibers

section Concrete

variable {A : Type w} [Category.{t} A] [HasColimitsOfSize.{v, v} A]
  {FC : A → A → Type*} {CC : A → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory A FC] [PreservesFilteredColimitsOfSize.{v, v} (forget A)]
  {P : Bᵒᵖ ⥤ A} {x : X}

/-- Every element of a classical stalk is the germ of a section over an admissible
neighbourhood of the point. -/
theorem exists_toPresheafFiber_pointElement_eq (p : ToType ((G.point x).presheafFiber.obj P)) :
    ∃ (U : B) (hx : x ∈ ι U) (s : ToType (P.obj (op U))),
      (G.point x).toPresheafFiber U (G.pointElement x hx) P s = p := by
  obtain ⟨U, h, s, rfl⟩ := (G.point x).toPresheafFiber_jointly_surjective p
  exact ⟨U, h.down.down, s, rfl⟩

/-- Two sections over the same admissible neighbourhood of `x` have the same germ at `x` if and
only if they agree on a smaller admissible neighbourhood of `x`. -/
theorem toPresheafFiber_pointElement_eq_iff' {U : B} (hx : x ∈ ι U)
    (s t : ToType (P.obj (op U))) :
    (G.point x).toPresheafFiber U (G.pointElement x hx) P s =
        (G.point x).toPresheafFiber U (G.pointElement x hx) P t ↔
      ∃ (V : B) (h : V ≤ U), x ∈ ι V ∧ P.map (homOfLE h).op s = P.map (homOfLE h).op t := by
  refine ((G.point x).toPresheafFiber_eq_iff' U _ s t).trans ⟨?_, ?_⟩
  · rintro ⟨V, f, ⟨⟨hV⟩⟩, -, hst⟩
    exact ⟨V, leOfHom f, hV, hst⟩
  · rintro ⟨V, h, hV, hst⟩
    exact ⟨V, homOfLE h, G.pointElement x hV, Subsingleton.elim _ _, hst⟩

/-- Two sections over admissible neighbourhoods of `x` have the same germ at `x` if and only if
they agree on a common smaller admissible neighbourhood of `x`. -/
theorem toPresheafFiber_pointElement_eq_iff {U V : B} (hU : x ∈ ι U) (hV : x ∈ ι V)
    (s : ToType (P.obj (op U))) (t : ToType (P.obj (op V))) :
    (G.point x).toPresheafFiber U (G.pointElement x hU) P s =
        (G.point x).toPresheafFiber V (G.pointElement x hV) P t ↔
      ∃ (W : B) (hWU : W ≤ U) (hWV : W ≤ V), x ∈ ι W ∧
        P.map (homOfLE hWU).op s = P.map (homOfLE hWV).op t := by
  have hUV : x ∈ ι (U ⊓ V) := (G.map_inf U V).symm ▸ ⟨hU, hV⟩
  -- The restricted fiber element is the neighbourhood element by proof irrelevance.
  have hs : (G.point x).toPresheafFiber (U ⊓ V) (G.pointElement x hUV) P
      (P.map (homOfLE inf_le_left).op s) =
        (G.point x).toPresheafFiber U (G.pointElement x hU) P s :=
    (G.point x).toPresheafFiber_w_apply (homOfLE inf_le_left) _ P s
  have ht : (G.point x).toPresheafFiber (U ⊓ V) (G.pointElement x hUV) P
      (P.map (homOfLE inf_le_right).op t) =
        (G.point x).toPresheafFiber V (G.pointElement x hV) P t :=
    (G.point x).toPresheafFiber_w_apply (homOfLE inf_le_right) _ P t
  rw [← hs, ← ht]
  refine (G.toPresheafFiber_pointElement_eq_iff' hUV _ _).trans ⟨?_, ?_⟩
  · rintro ⟨W, hW, hxW, hst⟩
    refine ⟨W, hW.trans inf_le_left, hW.trans inf_le_right, hxW, ?_⟩
    simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] using hst
  · rintro ⟨W, hWU, hWV, hxW, hst⟩
    refine ⟨W, le_inf hWU hWV, hxW, ?_⟩
    simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] using hst

end Concrete

/-- Transporting the point, presheaf and admissible open transports germs compatibly. -/
@[reassoc]
theorem toPresheafFiber_congr {A : Type w} [Category.{t} A]
    [HasColimitsOfSize.{v, v} A] {x y : X} (hxy : x = y)
    {P Q : Bᵒᵖ ⥤ A} (hPQ : P = Q) {U V : B} (hUV : U = V)
    (h : (G.point x).fiber.obj U) :
    (G.point x).toPresheafFiber U h P ≫ eqToHom (by subst_vars; rfl) =
      eqToHom (by subst_vars; rfl) ≫
        (G.point y).toPresheafFiber V
          (G.pointElement y (hxy ▸ hUV ▸ h.down.down)) Q := by
  subst_vars
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  congr 1

section Topological

open TopologicalSpace TopCat.Presheaf

variable {Y : TopCat.{v}} {A : Type w} [Category.{v} A] [HasColimitsOfSize.{v, v} A]

-- The G-site and the topological site bundle membership differently; the underlying
-- neighbourhoods and their inclusion order are identical.
private def topologicalNhdsOrderIso (x : Y) :
    {U : Opens Y // x ∈ opensEmbedding Y U} ≃o OpenNhds x where
  toFun U := ⟨U.1, by simpa using U.2⟩
  invFun U := ⟨U.1, by simpa using U.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private def topologicalNhdsDiagramIso (x : Y) (P : Y.Presheaf A) :
    (topologicalNhdsOrderIso x).equivalence.op.functor ⋙
        (OpenNhds.inclusion x).op ⋙ P ≅
      (nhdsInclusion (ι := opensEmbedding Y) x).op ⋙ P :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm)

private noncomputable def topologicalNhdsColimitIso (x : Y) (P : Y.Presheaf A) :
    colimit ((nhdsInclusion (ι := opensEmbedding Y) x).op ⋙ P) ≅ P.stalk x :=
  HasColimit.isoOfEquivalence (topologicalNhdsOrderIso x).equivalence.op
    (topologicalNhdsDiagramIso x P)

@[simp]
private theorem ι_topologicalNhdsColimitIso_hom (x : Y) (P : Y.Presheaf A)
    (U : Opens Y) (hx : x ∈ opensEmbedding Y U) :
    colimit.ι ((nhdsInclusion (ι := opensEmbedding Y) x).op ⋙ P) (op ⟨U, hx⟩) ≫
        (topologicalNhdsColimitIso x P).hom =
      P.germ U x (by simpa using hx) :=
  (HasColimit.ι_isoOfEquivalence_hom (topologicalNhdsOrderIso x).equivalence.op
    (topologicalNhdsDiagramIso x P) (op ⟨U, hx⟩)).trans (Category.id_comp _)

/-- For the G-topology of ordinary open covers, the classical site fiber is Mathlib's
ordinary stalk. -/
noncomputable def topologicalStalkIso (x : Y) (P : Y.Presheaf A) :
    ((topological Y).point x).presheafFiber.obj P ≅ P.stalk x :=
  ((topological Y).nhdsColimitIso x P).trans (topologicalNhdsColimitIso x P)

/-- The topological comparison preserves germs of sections. -/
@[simp, reassoc (attr := simp)]
theorem toPresheafFiber_topologicalStalkIso_hom (x : Y) (P : Y.Presheaf A)
    (U : Opens Y) (h : ((topological Y).point x).fiber.obj U) :
    ((topological Y).point x).toPresheafFiber U h P ≫
      (topologicalStalkIso x P).hom = P.germ U x (by simpa using h.down.down) := by
  simp [topologicalStalkIso, Iso.trans_hom, ← Category.assoc]

/-- The inverse topological comparison preserves germs of sections. -/
@[simp, reassoc (attr := simp)]
theorem germ_topologicalStalkIso_inv (x : Y) (P : Y.Presheaf A)
    (U : Opens Y) (hx : x ∈ U) :
    P.germ U x hx ≫ (topologicalStalkIso x P).inv =
      ((topological Y).point x).toPresheafFiber U
        ((topological Y).pointElement x (by simpa using hx)) P := by
  rw [Iso.comp_inv_eq, toPresheafFiber_topologicalStalkIso_hom]

/-- The topological stalk comparison is natural in the presheaf. -/
@[reassoc]
theorem topologicalStalkIso_naturality (x : Y) {P Q : Y.Presheaf A} (f : P ⟶ Q) :
    ((topological Y).point x).presheafFiber.map f ≫ (topologicalStalkIso x Q).hom =
      (topologicalStalkIso x P).hom ≫ (stalkFunctor A x).map f := by
  ext U h
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc,
    toPresheafFiber_topologicalStalkIso_hom]
  -- Reassociation must unfold stalk to identify it with the stalk functor's object.
  erw [← Category.assoc, toPresheafFiber_topologicalStalkIso_hom, stalkFunctor_map_germ]

end Topological

end TauCeti.GTopology
