/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Maps from stalks and change of coefficients

Compatible additive maps on sections of an additive-group-valued presheaf induce an additive
map from each stalk. Its value on a germ is the prescribed value of the section map.
The canonical map `(f_* F)_{f(x)} ⟶ F_x` is natural in the presheaf, permitting
transport of complexes through the stalk comparison for an embedding.

The stalk of an additive-group-valued presheaf at `x` vanishes exactly when every section over a
neighbourhood of `x` restricts to zero on a smaller neighbourhood of `x`
(`TopCat.Presheaf.isZero_stalk_iff`). Since sheafification does not change stalks
(`TopCat.Presheaf.isZero_stalk_sheafify_iff`), the sheafification of a presheaf vanishes exactly
when every section is locally zero (`TopCat.Presheaf.isZero_presheafToSheaf_obj_iff`). The same
criteria hold for module-valued presheaves (`TopCat.Presheaf.isZero_stalk_iff_moduleCat` and
`TopCat.Presheaf.isZero_presheafToSheaf_obj_iff_moduleCat`).

Taking stalks commutes with a coefficient functor preserving the neighborhood colimit,
even after sheafifying the composed presheaf
(`CategoryTheory.Functor.stalkComposeAndSheafifyIso`). The comparison is natural in the
sheaf and characterized on germs. In particular it applies to scalar extension of module
sheaves, since Mathlib's `ModuleCat.extendScalars` is a left adjoint. The construction uses
Mathlib's invariance of stalks under sheafification and `preservesColimitNatIso`.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

noncomputable section

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (F : X.Presheaf AddCommGrpCat.{u}) (x : X)
  {T : Type u} [AddCommGroup T]

/-- The additive universal property of a presheaf stalk, using maps compatible with restriction. -/
def stalkLiftAddHom
    (f : ∀ (U : Opens X), x ∈ U → F.obj (op U) →+ T)
    (hf : ∀ {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (m : F.obj (op V)),
      f U hx (F.map i.op m) = f V (i.le hx) m) :
    ↑(TopCat.Presheaf.stalk F x) →+ T :=
  (colimit.desc ((OpenNhds.inclusion x).op ⋙ F)
    { pt := AddCommGrpCat.of T
      ι :=
        { app := fun U ↦ AddCommGrpCat.ofHom (f U.unop.1 U.unop.2)
          naturality := fun {U V} i ↦ by
            ext m
            exact hf i.unop V.unop.2 m } }).hom

/-- The additive map induced from compatible section maps takes a germ to its prescribed value. -/
@[simp]
theorem stalkLiftAddHom_germ
    (f : ∀ (U : Opens X), x ∈ U → F.obj (op U) →+ T)
    (hf : ∀ {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (m : F.obj (op V)),
      f U hx (F.map i.op m) = f V (i.le hx) m)
    (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    F.stalkLiftAddHom x f hf (TopCat.Presheaf.germ F U x hx m) = f U hx m :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (F := (OpenNhds.inclusion x).op ⋙ F) _ (op ⟨U, hx⟩)) m

section Sheafify

variable {C : Type*} [Category.{u} C] [HasColimits C] [HasTerminal C]
  [HasWeakSheafify (Opens.grothendieckTopology X) C] (P : X.Presheaf C)

omit [HasTerminal C] in
/-- Sheafification does not change whether a stalk vanishes. -/
theorem isZero_stalk_sheafify_iff :
    IsZero (stalk (CategoryTheory.sheafify (Opens.grothendieckTopology X) P) x) ↔
      IsZero (P.stalk x) :=
  have : HasTerminal C := (TopCat.Sheaf.isTerminalOfEmpty
    ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P)).hasTerminal
  have := stalkFunctor_map_unit_toSheafify_isIso x C P
  (asIso ((stalkFunctor C x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P))).isZero_iff.symm

end Sheafify

/-- The stalk of an additive-group-valued presheaf at `x` vanishes if and only if every section
over a neighbourhood of `x` restricts to zero on some smaller neighbourhood of `x`. -/
theorem isZero_stalk_iff :
    IsZero (F.stalk x) ↔ ∀ (U : Opens X) (s : F.obj (op U)), x ∈ U →
      ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ F.map (homOfLE h).op s = 0 := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  constructor
  · intro _ U s hx
    obtain ⟨W, hxW, iU, iV, e⟩ := F.germ_eq x hx hx s 0 (Subsingleton.elim _ _)
    exact ⟨W, iU.le, hxW, e.trans (map_zero _)⟩
  · intro h
    suffices ∀ t : F.stalk x, t = 0 from ⟨fun a b ↦ (this a).trans (this b).symm⟩
    intro t
    obtain ⟨U, hx, s, rfl⟩ := F.exists_germ_eq t
    obtain ⟨V, hVU, hxV, hs⟩ := h U s hx
    rw [← F.germ_res_apply (homOfLE hVU) x hxV, hs, map_zero]

/-- The sheafification of an additive-group-valued presheaf vanishes if and only if every
section of the presheaf is locally zero: each point of its domain has a neighbourhood on which
it restricts to zero. -/
theorem isZero_presheafToSheaf_obj_iff :
    IsZero ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj F) ↔
      ∀ (x : X) (U : Opens X) (s : F.obj (op U)), x ∈ U →
        ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ F.map (homOfLE h).op s = 0 := by
  refine (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (X := X)
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj F)).trans
      (forall_congr' fun x ↦ ?_)
  exact (isZero_stalk_sheafify_iff x F).trans (isZero_stalk_iff F x)

section ModuleCat

variable {R : Type u} [Ring R] (P : X.Presheaf (ModuleCat.{u} R))

/-- The stalk of a module-valued presheaf at `x` vanishes if and only if every section over a
neighbourhood of `x` restricts to zero on some smaller neighbourhood of `x`. -/
theorem isZero_stalk_iff_moduleCat (x : X) :
    IsZero (P.stalk x) ↔ ∀ (U : Opens X) (s : P.obj (op U)), x ∈ U →
      ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ P.map (homOfLE h).op s = 0 := by
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  · intro _ U s hx
    obtain ⟨W, hxW, iU, iV, e⟩ := P.germ_eq x hx hx s 0 (Subsingleton.elim _ _)
    exact ⟨W, iU.le, hxW, e.trans (map_zero _)⟩
  · intro h
    refine subsingleton_of_forall_eq 0 fun t ↦ ?_
    obtain ⟨U, hx, s, rfl⟩ := P.exists_germ_eq t
    obtain ⟨V, hVU, hxV, hs⟩ := h U s hx
    rw [← P.germ_res_apply (homOfLE hVU) x hxV, hs, map_zero]

/-- The sheafification of a module-valued presheaf vanishes if and only if every section of the
presheaf is locally zero: each point of its domain has a neighbourhood on which it restricts to
zero. -/
theorem isZero_presheafToSheaf_obj_iff_moduleCat :
    IsZero ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj P) ↔
      ∀ (x : X) (U : Opens X) (s : P.obj (op U)), x ∈ U →
        ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ P.map (homOfLE h).op s = 0 := by
  refine (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (X := X)
    ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj P)).trans
      (forall_congr' fun x ↦ ?_)
  exact (isZero_stalk_sheafify_iff x P).trans (P.isZero_stalk_iff_moduleCat x)

end ModuleCat

end TopCat.Presheaf

namespace TauCeti.Topology

universe v

variable {C : Type v} [Category.{u} C] [HasColimits C]
  {X Y : TopCat.{u}} (f : X ⟶ Y) {F G : X.Presheaf C}

/-- The canonical pushforward map on stalks is natural in the presheaf. -/
@[reassoc]
theorem stalkPushforward_naturality (α : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor C (f x)).map
        ((TopCat.Presheaf.pushforward C f).map α) ≫ G.stalkPushforward C f x =
      F.stalkPushforward C f x ≫ (TopCat.Presheaf.stalkFunctor C x).map α := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    TopCat.Presheaf.stalkPushforward_germ,
    TopCat.Presheaf.stalkPushforward_germ_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

end TauCeti.Topology

namespace CategoryTheory.Functor

universe v w

variable {X : TopCat.{u}} {A : Type v} {B : Type w} [Category.{u} A] [Category.{u} B]
  [HasColimits A] [HasColimits B] [HasTerminal B]
  [HasWeakSheafify (Opens.grothendieckTopology X) B]
  (G : A ⥤ B) (x : X) [PreservesColimitsOfShape (OpenNhds x)ᵒᵖ G]

open TopCat.Presheaf

/-- Taking stalks commutes with a coefficient functor preserving the neighborhood colimit,
even after sheafifying the composed presheaf. The isomorphism is natural in the sheaf and
characterized on germs by `germ_stalkComposeAndSheafifyIso_hom_app`. -/
def stalkComposeAndSheafifyIso :
    Sheaf.composeAndSheafify (Opens.grothendieckTopology X) G ⋙
        sheafToPresheaf _ B ⋙ stalkFunctor B x ≅
      sheafToPresheaf (Opens.grothendieckTopology X) A ⋙ stalkFunctor A x ⋙ G :=
  let η := whiskerLeft
    (sheafToPresheaf (Opens.grothendieckTopology X) A ⋙ (whiskeringRight _ _ _).obj G)
    (whiskerRight (sheafificationAdjunction (Opens.grothendieckTopology X) B).unit
      (stalkFunctor B x))
  have hη : ∀ F : X.Sheaf A, IsIso
      ((stalkFunctor B x).map (toSheafify (Opens.grothendieckTopology X) (F.obj ⋙ G))) :=
    fun F ↦ stalkFunctor_map_unit_toSheafify_isIso x B (F.obj ⋙ G)
  have : IsIso η := (NatTrans.isIso_iff_isIso_app η).mpr hη
  NatIso.ofComponents
    (fun F ↦ (asIso ((stalkFunctor B x).map
      (toSheafify (Opens.grothendieckTopology X) (F.obj ⋙ G)))).symm ≪≫
        (preservesColimitIso G ((OpenNhds.inclusion x).op ⋙ F.obj)).symm)
    (fun α ↦ by
      -- Naturality comes from the unit and colimit comparisons. Normalize functor composition
      -- to identify the diagrams `(inclusion ⋙ F.obj) ⋙ G` and `inclusion ⋙ (F.obj ⋙ G)`.
      simpa [Iso.trans_hom, Iso.symm_hom, asIso_inv, η, stalkFunctor, Functor.comp] using
        (((asIso η).symm ≪≫
          isoWhiskerLeft (sheafToPresheaf (Opens.grothendieckTopology X) A)
            (isoWhiskerLeft ((whiskeringLeft _ _ _).obj (OpenNhds.inclusion x).op)
              (preservesColimitNatIso G).symm)).hom.naturality α))

/-- The stalk comparison undoes sheafification and then uses the coefficient functor's
colimit comparison. This specifies its direction without unfolding the construction. -/
@[reassoc]
private lemma stalkFunctor_map_toSheafify_comp_stalkComposeAndSheafifyIso_hom_app
    (F : X.Sheaf A) :
    (stalkFunctor B x).map (toSheafify (Opens.grothendieckTopology X) (F.obj ⋙ G)) ≫
      (G.stalkComposeAndSheafifyIso x).hom.app F =
    (preservesColimitIso G ((OpenNhds.inclusion x).op ⋙ F.obj)).inv := by
  have := stalkFunctor_map_unit_toSheafify_isIso x B (F.obj ⋙ G)
  exact IsIso.hom_inv_id_assoc
    ((stalkFunctor B x).map (toSheafify (Opens.grothendieckTopology X) (F.obj ⋙ G)))
    (preservesColimitIso G ((OpenNhds.inclusion x).op ⋙ F.obj)).inv

/-- The germ of a sheafified coefficient section corresponds to the image of the original
germ under the coefficient functor. The first arrow is the sheafification unit. -/
@[reassoc (attr := simp)]
theorem germ_stalkComposeAndSheafifyIso_hom_app (F : X.Sheaf A)
    (U : Opens X) (hx : x ∈ U) :
    (toSheafify (Opens.grothendieckTopology X) (F.obj ⋙ G)).app (op U) ≫
      germ ((presheafToSheaf (Opens.grothendieckTopology X) B).obj
        (F.obj ⋙ G)).obj U x hx ≫
      (G.stalkComposeAndSheafifyIso x).hom.app F = G.map (F.presheaf.germ U x hx) := by
  -- Keep the germ in simp-normal form: the native composite's presheaf is `sheafify (F.obj ⋙ G)`.
  exact (stalkFunctor_map_germ_assoc U x hx _ _).symm.trans
    ((congrArg (germ (F.obj ⋙ G) U x hx ≫ ·)
      (stalkFunctor_map_toSheafify_comp_stalkComposeAndSheafifyIso_hom_app G x F)).trans
        (ι_preservesColimitIso_inv G ((OpenNhds.inclusion x).op ⋙ F.obj) (op ⟨U, hx⟩)))

end CategoryTheory.Functor
