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
# Points of G-sites and stalks

Every point `x` of the underlying set of a G-topology `G` defines a point `G.point x` of the
site `G.grothendieckTopology`, in the sense of Mathlib's `GrothendieckTopology.Point`: its fibre
over an admissible open `U` is a singleton when `x ∈ U` and empty otherwise. The fibre of a
presheaf at this point is the classical stalk of [BGR, §9.1]. We introduce the germ maps into it
(`GTopology.germ`) and show that they exhibit it as the colimit of the sections over the
admissible opens containing `x` (`GTopology.isColimitGermCocone`). For presheaves with values in
a concrete category whose forgetful functor preserves filtered colimits, every element of the
stalk is a germ (`GTopology.exists_germ_eq`), and two sections have the same germ exactly when
they agree on a common smaller admissible open containing `x` (`GTopology.germ_eq_iff`).

Thus Mathlib's general theory of points of sites applies to these stalks. For instance, under the
usual hypotheses on the coefficient category, they are exact functors and invert the morphisms
which become isomorphisms after sheafification.

For the G-topology of ordinary open covers, the stalk at a point is Mathlib's stalk of a presheaf
on a topological space, compatibly with germs (`GTopology.topologicalStalkIso`).

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §9.1.
* The construction of the point follows Mathlib's `Opens.pointGrothendieckTopology`, the point of
  the open-set site of a topological space.
-/

public section

namespace TauCeti

open CategoryTheory Opposite Limits

universe u v w w'

namespace GTopology

variable {X : Type u} {B : Type v} [SemilatticeInf B] [OrderTop B] {ι : B ↪o Set X}
  (G : GTopology ι)

/-- The point of the G-site of `G` given by a point `x` of the underlying set. Its fibre over an
admissible open `U` is inhabited exactly when `x ∈ U`. -/
def point (x : X) : GrothendieckTopology.Point.{v} G.grothendieckTopology where
  fiber.obj U := ULift.{v} (PLift (x ∈ ι U))
  fiber.map f := ↾fun h ↦ ⟨⟨ι.monotone (leOfHom f) h.down.down⟩⟩
  isCofiltered :=
    { nonempty := ⟨.mk (obj := ⊤) ⟨⟨by simp [G.map_top]⟩⟩⟩
      cone_objs U V := by
        induction U with | @mk U hU
        induction V with | @mk V hV
        obtain ⟨⟨hU⟩⟩ := hU
        obtain ⟨⟨hV⟩⟩ := hV
        exact ⟨.mk (obj := U ⊓ V) ⟨⟨by simpa only [G.map_inf] using ⟨hU, hV⟩⟩⟩,
          Functor.Elements.homMk (homOfLE inf_le_left) rfl,
          Functor.Elements.homMk (homOfLE inf_le_right) rfl, by tauto⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U R hR ⟨⟨hx⟩⟩
    obtain ⟨S, hS, hSR⟩ := (G.mem_grothendieckTopology_iff).mp hR
    rw [← G.union_eq hS] at hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV⟩ := hx
    exact ⟨V, homOfLE (G.subset hS V hV), hSR _ _ ((coverPresieve_apply _ _).mpr hV),
      ⟨⟨hxV⟩⟩, rfl⟩

/-- The fibre of `G.point x` over an admissible open `U` is inhabited exactly when `x ∈ U`. -/
@[simp]
theorem nonempty_point_fiber_obj_iff (x : X) (U : B) :
    Nonempty ((G.point x).fiber.obj U) ↔ x ∈ ι U :=
  ⟨fun ⟨h⟩ ↦ h.down.down, fun h ↦ ⟨⟨⟨h⟩⟩⟩⟩

/-- The fibre of any point `Φ` of the G-site over an admissible open `U` has at most one element:
`U` maps monomorphically to the terminal admissible open `⊤`, since the site is a poset. -/
instance (U : B) (Φ : GrothendieckTopology.Point.{v} G.grothendieckTopology) :
    Subsingleton (Φ.fiber.obj U) :=
  Φ.subsingleton_fiber_obj (homOfLE le_top) isTerminalTop

section Germ

variable {A : Type w} [Category.{w'} A] [HasColimitsOfSize.{v, v} A]

/-- The germ at `x` of a section of a presheaf over an admissible open `U` containing `x`: the
canonical map to the fibre of the presheaf at the point `G.point x`. -/
noncomputable def germ (P : Bᵒᵖ ⥤ A) (U : B) (x : X) (hx : x ∈ ι U) :
    P.obj (op U) ⟶ (G.point x).presheafFiber.obj P :=
  (G.point x).toPresheafFiber U ⟨⟨hx⟩⟩ P

/-- Mathlib's canonical maps to the fibre at the point `G.point x` are the germs. -/
@[simp]
theorem toPresheafFiber_point (x : X) (U : B) (u : (G.point x).fiber.obj U) (P : Bᵒᵖ ⥤ A) :
    (G.point x).toPresheafFiber U u P =
      G.germ P U x ((G.nonempty_point_fiber_obj_iff x U).mp ⟨u⟩) := by
  rw [Subsingleton.elim u ⟨⟨(G.nonempty_point_fiber_obj_iff x U).mp ⟨u⟩⟩⟩]
  rfl

/-- The germ of a restricted section is the germ of the original section. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem germ_res (P : Bᵒᵖ ⥤ A) {U V : B} (f : V ⟶ U) (x : X) (hx : x ∈ ι V) :
    P.map f.op ≫ G.germ P V x hx = G.germ P U x (ι.monotone (leOfHom f) hx) :=
  (G.point x).toPresheafFiber_w f _ P

/-- Germs are natural in the presheaf. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem germ_naturality {P Q : Bᵒᵖ ⥤ A} (g : P ⟶ Q) (U : B) (x : X) (hx : x ∈ ι U) :
    G.germ P U x hx ≫ (G.point x).presheafFiber.map g = g.app (op U) ≫ G.germ Q U x hx :=
  (G.point x).toPresheafFiber_naturality g U _

/-- Morphisms out of a stalk agree as soon as they agree on all germs. -/
theorem stalk_hom_ext {P : Bᵒᵖ ⥤ A} {x : X} {T : A}
    {f g : (G.point x).presheafFiber.obj P ⟶ T}
    (h : ∀ (U : B) (hx : x ∈ ι U), G.germ P U x hx ≫ f = G.germ P U x hx ≫ g) : f = g :=
  (G.point x).presheafFiber_hom_ext fun U ⟨⟨hx⟩⟩ ↦ h U hx

/-- The cocone of germs at `x`, over the admissible opens containing `x`. -/
@[expose, simps]
noncomputable def germCocone (P : Bᵒᵖ ⥤ A) (x : X) :
    Cocone ((ObjectProperty.ι fun U : B ↦ x ∈ ι U).op ⋙ P) where
  pt := (G.point x).presheafFiber.obj P
  ι.app U := G.germ P U.unop.obj x U.unop.property
  ι.naturality U V f := by
    simp [G.germ_res P f.unop.hom x V.unop.property]

/-- The stalk at `x` is the colimit of the sections over the admissible opens containing `x`,
the colimit cocone being given by the germs. This identifies the fibre at the point `G.point x`
with the classical stalk. -/
noncomputable def isColimitGermCocone (P : Bᵒᵖ ⥤ A) (x : X) :
    IsColimit (G.germCocone P x) where
  desc s := (G.point x).presheafFiberDesc
    (fun U hU ↦ s.ι.app (op ⟨U, hU.down.down⟩))
    (fun U V f hU ↦ by
      simpa using s.w (ObjectProperty.homMk (P := fun U : B ↦ x ∈ ι U)
        (X := ⟨U, hU.down.down⟩) (Y := ⟨V, ι.monotone (leOfHom f) hU.down.down⟩) f).op)
  fac s U := (G.point x).toPresheafFiber_presheafFiberDesc _ _ U.unop.obj _
  uniq s m hm := G.stalk_hom_ext fun U hx ↦
    (hm (op ⟨U, hx⟩)).trans ((G.point x).toPresheafFiber_presheafFiberDesc
      (fun U hU ↦ s.ι.app (op ⟨U, hU.down.down⟩)) _ U ⟨⟨hx⟩⟩).symm

/-- The morphism out of the stalk induced by a cocone restricts on germs to the cocone maps. -/
@[reassoc, simp]
theorem germ_isColimitGermCocone_desc {P : Bᵒᵖ ⥤ A} {x : X}
    (s : Cocone ((ObjectProperty.ι fun U : B ↦ x ∈ ι U).op ⋙ P)) (U : B) (hx : x ∈ ι U) :
    G.germ P U x hx ≫ (G.isColimitGermCocone P x).desc s = s.ι.app (op ⟨U, hx⟩) :=
  (G.isColimitGermCocone P x).fac s (op ⟨U, hx⟩)

section Concrete

variable {FC : A → A → Type*} {CC : A → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory A FC] [PreservesFilteredColimitsOfSize.{v, v} (forget A)]

/-- Every element of a stalk is the germ of a section over an admissible open containing the
point. -/
theorem exists_germ_eq {P : Bᵒᵖ ⥤ A} {x : X} (p : ToType ((G.point x).presheafFiber.obj P)) :
    ∃ (U : B) (hx : x ∈ ι U) (s : ToType (P.obj (op U))), G.germ P U x hx s = p := by
  obtain ⟨U, ⟨⟨hx⟩⟩, s, rfl⟩ := (G.point x).toPresheafFiber_jointly_surjective p
  exact ⟨U, hx, s, rfl⟩

/-- Two sections over the same admissible open containing `x` have the same germ at `x` if and
only if they agree on a smaller admissible open containing `x`. -/
theorem germ_eq_iff' {P : Bᵒᵖ ⥤ A} {U : B} {x : X} (hx : x ∈ ι U) (s t : ToType (P.obj (op U))) :
    G.germ P U x hx s = G.germ P U x hx t ↔
      ∃ (V : B) (h : V ≤ U), x ∈ ι V ∧ P.map (homOfLE h).op s = P.map (homOfLE h).op t := by
  refine ((G.point x).toPresheafFiber_eq_iff' U ⟨⟨hx⟩⟩ s t).trans ⟨?_, ?_⟩
  · rintro ⟨V, f, ⟨⟨hV⟩⟩, -, hst⟩
    exact ⟨V, leOfHom f, hV, hst⟩
  · rintro ⟨V, h, hV, hst⟩
    exact ⟨V, homOfLE h, ⟨⟨hV⟩⟩, Subsingleton.elim _ _, hst⟩

/-- Two sections over admissible opens containing `x` have the same germ at `x` if and only if
they agree on a common smaller admissible open containing `x`. -/
theorem germ_eq_iff {P : Bᵒᵖ ⥤ A} {U V : B} {x : X} (hU : x ∈ ι U) (hV : x ∈ ι V)
    (s : ToType (P.obj (op U))) (t : ToType (P.obj (op V))) :
    G.germ P U x hU s = G.germ P V x hV t ↔
      ∃ (W : B) (hWU : W ≤ U) (hWV : W ≤ V), x ∈ ι W ∧
        P.map (homOfLE hWU).op s = P.map (homOfLE hWV).op t := by
  have hUV : x ∈ ι (U ⊓ V) := by simpa only [G.map_inf] using ⟨hU, hV⟩
  rw [← G.germ_res_apply P (homOfLE inf_le_left) x hUV s,
    ← G.germ_res_apply P (homOfLE inf_le_right) x hUV t, G.germ_eq_iff']
  constructor
  · rintro ⟨W, hW, hxW, hst⟩
    refine ⟨W, hW.trans inf_le_left, hW.trans inf_le_right, hxW, ?_⟩
    simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] using hst
  · rintro ⟨W, hWU, hWV, hxW, hst⟩
    refine ⟨W, le_inf hWU hWV, hxW, ?_⟩
    simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] using hst

end Concrete

end Germ

section Topological

open TopologicalSpace

variable (Y : Type u) [TopologicalSpace Y] {A : Type w} [Category.{u} A] [HasColimits.{u} A]

/-- For the G-topology of ordinary open covers, the stalk at the point `y` is Mathlib's stalk of
the presheaf at `y`, compatibly with germs (`GTopology.germ_topologicalStalkIso_hom`). -/
noncomputable def topologicalStalkIso (P : (Opens Y)ᵒᵖ ⥤ A) (y : Y) :
    ((topological Y).point y).presheafFiber.obj P ≅
      TopCat.Presheaf.stalk (X := TopCat.of Y) P y where
  hom := (isColimitGermCocone _ P y).desc
    { pt := TopCat.Presheaf.stalk (X := TopCat.of Y) P y
      ι.app U := TopCat.Presheaf.germ (X := TopCat.of Y) P U.unop.obj y
        (by simpa using U.unop.property)
      ι.naturality U V f := by
        simpa using TopCat.Presheaf.germ_res (X := TopCat.of Y) P f.unop.hom y _ }
  inv := colimit.desc ((OpenNhds.inclusion (X := TopCat.of Y) y).op ⋙ P)
    { pt := ((topological Y).point y).presheafFiber.obj P
      ι.app U := (topological Y).germ P ((OpenNhds.inclusion (X := TopCat.of Y) y).obj U.unop) y
        (by simpa [OpenNhds.inclusion] using U.unop.2)
      ι.naturality U V f := by simp }
  hom_inv_id := (topological Y).stalk_hom_ext fun U hy ↦
    ((isColimitGermCocone _ P y).fac_assoc _ (op ⟨U, hy⟩) _).trans
      ((colimit.ι_desc _ _).trans (by simp [OpenNhds.inclusion]))
  inv_hom_id := TopCat.Presheaf.stalk_hom_ext (X := TopCat.of Y) P fun U hy ↦
    (colimit.ι_desc_assoc _ _ _).trans
      ((germ_isColimitGermCocone_desc _ _ U _).trans (by simp))

/-- Under `GTopology.topologicalStalkIso`, germs correspond to Mathlib's germs. -/
@[reassoc (attr := simp)]
theorem germ_topologicalStalkIso_hom (P : (Opens Y)ᵒᵖ ⥤ A) (U : Opens Y) (y : Y)
    (hy : y ∈ opensEmbedding Y U) :
    (topological Y).germ P U y hy ≫ (topologicalStalkIso Y P y).hom =
      TopCat.Presheaf.germ (X := TopCat.of Y) P U y (by simpa using hy) :=
  germ_isColimitGermCocone_desc _ _ U hy

/-- Under `GTopology.topologicalStalkIso`, Mathlib's germs correspond to germs. -/
@[reassoc (attr := simp)]
theorem germ_topologicalStalkIso_inv (P : (Opens Y)ᵒᵖ ⥤ A) (U : Opens Y) (y : Y) (hy : y ∈ U) :
    TopCat.Presheaf.germ (X := TopCat.of Y) P U y hy ≫ (topologicalStalkIso Y P y).inv =
      (topological Y).germ P U y (show y ∈ opensEmbedding Y U by simpa using hy) :=
  (Iso.comp_inv_eq _).mpr (germ_topologicalStalkIso_hom Y P U y _).symm

end Topological

end GTopology

end TauCeti
