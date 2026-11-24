/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import TauCeti.CategoryTheory.Limits.ConcreteCategory.ZeroObjects

/-!
# Maps from stalks and change of coefficients

Compatible additive maps on sections of an additive-group-valued presheaf induce an additive
map from each stalk. Its value on a germ is the prescribed value of the section map.
The canonical map `(f_* F)_{f(x)} ⟶ F_x` is natural in the presheaf
(`TopCat.Presheaf.stalkPushforward_naturality`), permitting transport of complexes through the
stalk comparison for an embedding.

For a presheaf valued in a concrete category whose objects carry a zero preserved by the
morphisms (such as abelian groups or modules), the stalk at `x` vanishes exactly when every section
over a neighbourhood of `x` restricts to zero on a smaller neighbourhood of `x`
(`TopCat.Presheaf.isZero_stalk_iff`). If a morphism of presheaves valued in a category with zero
morphisms vanishes on all opens inside `V`, its induced map on stalks vanishes at every point of `V`
(`TopCat.Presheaf.stalkFunctor_map_eq_zero_of_app_eq_zero`). A sheaf valued in a concrete
category with zero morphisms, whose forgetful functor preserves limits and filtered colimits,
vanishes exactly when all its stalks do (`TopCat.Sheaf.isZero_iff_forall_isZero_stalk`); no zero
on the underlying types is needed. Sheafification does not change stalks
(`TopCat.Presheaf.isIso_stalkFunctor_map_toSheafify`, needing only weak sheafification), so the
sheafification of a presheaf valued in a concrete category with zero morphisms whose objects carry
a zero preserved by the morphisms vanishes exactly when every section is locally zero
(`TopCat.Presheaf.isZero_presheafToSheaf_obj_iff`).

Taking stalks commutes with a coefficient functor preserving the neighborhood colimit,
even after sheafifying the composed presheaf
(`CategoryTheory.Functor.stalkComposeAndSheafifyIso`). The comparison is natural in the
sheaf, inverts the stalk map of the sheafification unit up to the coefficient functor's colimit
comparison
(`CategoryTheory.Functor.stalkFunctor_map_toSheafify_comp_stalkComposeAndSheafifyIso_hom_app`),
and is characterized on germs. In particular it applies to scalar extension of module
sheaves, since Mathlib's `ModuleCat.extendScalars` is a left adjoint. The construction uses
Mathlib's invariance of stalks under sheafification and `preservesColimitNatIso`.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

noncomputable section

namespace TopCat.Presheaf

section ZeroMorphisms

/-- A morphism of presheaves valued in a category with zero morphisms that vanishes on all opens
inside `V` induces the zero map on stalks at every point of `V`. -/
theorem stalkFunctor_map_eq_zero_of_app_eq_zero
    {C : Type*} [Category.{u} C] [HasZeroMorphisms C] [HasColimits C]
    {X : TopCat.{u}} {F G : X.Presheaf C} (α : F ⟶ G) {V : Opens X}
    (hα : ∀ ⦃W : Opens X⦄, W ≤ V → α.app (op W) = 0) {x : X} (hx : x ∈ V) :
    (stalkFunctor C x).map α = 0 := by
  refine F.stalk_hom_ext fun U hxU ↦ ?_
  have hxUV : x ∈ U ⊓ V := ⟨hxU, hx⟩
  have hUV : F.germ (U ⊓ V) x hxUV ≫ (stalkFunctor C x).map α = 0 :=
    (stalkFunctor_map_germ (U ⊓ V) x hxUV α).trans
      ((congrArg (· ≫ G.germ (U ⊓ V) x hxUV) (hα inf_le_right)).trans zero_comp)
  have hres := F.germ_res_assoc (homOfLE inf_le_left : U ⊓ V ⟶ U) x hxUV
    ((stalkFunctor C x).map α)
  exact (hres.symm.trans ((congrArg (_ ≫ ·) hUV).trans comp_zero)).trans comp_zero.symm

end ZeroMorphisms

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
        { app := fun U ↦ AddCommGrpCat.ofHom (f U.unop.val U.unop.property)
          naturality := fun {U V} i ↦ by
            ext m
            exact hf i.unop V.unop.property m } }).hom

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

variable {C : Type*} [Category.{u} C] [HasColimits C]
  [HasWeakSheafify (Opens.grothendieckTopology X) C] (P : X.Presheaf C)

/-- The stalk map of the sheafification unit `P ⟶ sheafify P` is an isomorphism: sheafification
does not change stalks. Unlike Mathlib's `stalkFunctor_map_unit_toSheafify_isIso`, this needs no
`HasTerminal C` hypothesis. -/
theorem isIso_stalkFunctor_map_toSheafify :
    IsIso ((stalkFunctor C x).map (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)) :=
  have : HasTerminal C := (TopCat.Sheaf.isTerminalOfEmpty
    ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P)).hasTerminal
  stalkFunctor_map_unit_toSheafify_isIso x C P

/-- Sheafification does not change whether a stalk vanishes. -/
theorem isZero_stalk_sheafify_iff :
    IsZero (stalk (CategoryTheory.sheafify (Opens.grothendieckTopology X) P) x) ↔
      IsZero (P.stalk x) :=
  have := isIso_stalkFunctor_map_toSheafify x P
  (asIso ((stalkFunctor C x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P))).isZero_iff.symm

end Sheafify

section Concrete

variable {C : Type*} [Category.{u} C] [HasColimits C] {FC : C → C → Type*} {CC : C → Type u}
  [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{u} C FC]
  [PreservesFilteredColimits (forget C)]

/-- The stalk at `x` of a presheaf valued in a concrete category whose objects carry a zero
preserved by the morphisms vanishes if and only if every section over a neighbourhood of `x`
restricts to zero on some smaller neighbourhood of `x`. The category needs zero morphisms, and
its forgetful functor must preserve filtered colimits and the terminal object. -/
theorem isZero_stalk_iff [∀ A, Zero (CC A)] [∀ A B, ZeroHomClass (FC A B) (CC A) (CC B)]
    [HasZeroMorphisms C] [PreservesLimit (Functor.empty.{0} C) (forget C)]
    (P : X.Presheaf C) (x : X) :
    IsZero (P.stalk x) ↔ ∀ (U : Opens X) (s : ToType (P.obj (op U))), x ∈ U →
      ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ P.map (homOfLE h).op s = 0 := by
  rw [ConcreteCategory.isZero_iff_subsingleton, subsingleton_iff_forall_eq 0]
  constructor
  · intro hP U s hx
    obtain ⟨W, hxW, iU, iV, e⟩ := P.germ_eq x hx hx s 0 ((hP _).trans (hP _).symm)
    exact ⟨W, iU.le, hxW, e.trans (map_zero _)⟩
  · intro h t
    obtain ⟨U, hx, s, rfl⟩ := P.exists_germ_eq t
    obtain ⟨V, hVU, hxV, hs⟩ := h U s hx
    rw [← P.germ_res_apply (homOfLE hVU) x hxV, hs, map_zero]

/-- A sheaf valued in a concrete category with zero morphisms, whose forgetful functor preserves
limits and filtered colimits, vanishes if and only if all its stalks vanish. Unlike Mathlib's
`TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero`, this needs neither `Abelian C` nor
`HasLimits C`. -/
theorem _root_.TopCat.Sheaf.isZero_iff_forall_isZero_stalk [HasZeroMorphisms C]
    [PreservesLimits (forget C)] (Q : TopCat.Sheaf C X) :
    IsZero Q ↔ ∀ x : X, IsZero (Q.presheaf.stalk x) := by
  refine ⟨fun hQ x ↦ ?_, fun h ↦ ?_⟩
  · -- `𝟙 Q` equals the sheaf morphism with underlying presheaf morphism `0`
    have h0 : 𝟙 Q.obj = 0 := by
      simpa using congrArg (·.hom) (hQ.eq_of_src (𝟙 Q) (ObjectProperty.homMk 0))
    -- so the identity of the stalk, the stalk map of `𝟙 Q.obj`, vanishes
    exact (IsZero.iff_id_eq_zero _).2 <| ((stalkFunctor C x).map_id Q.obj).symm.trans <|
      stalkFunctor_map_eq_zero_of_app_eq_zero (𝟙 Q.obj) (V := ⊤)
        (fun W _ ↦ by simpa using NatTrans.congr_app h0 (op W)) (Set.mem_univ x)
  refine IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ C) Q
    (Functor.isZero _ fun U ↦ (ConcreteCategory.isZero_iff_subsingleton _).2 ⟨fun s t ↦ ?_⟩)
  -- the underlying presheaf of types is a sheaf: equal germs give local, hence global, equality
  let Qt : TopCat.Sheaf (Type u) X :=
    ⟨Q.obj ⋙ forget C, Presheaf.isSheaf_comp_of_isSheaf _ _ (forget C) Q.property⟩
  have hgerm (x : U.unop) :
      Q.presheaf.germ _ x x.property s = Q.presheaf.germ _ x x.property t :=
    have := (ConcreteCategory.isZero_iff_subsingleton _).1 (h x)
    Subsingleton.elim _ _
  choose V hxV iU iV hst using fun x : U.unop ↦
    Q.presheaf.germ_eq x x.property x.property s t (hgerm x)
  exact Qt.eq_of_locally_eq' V U.unop iU (fun x hx ↦ Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV _⟩) s t
    fun x ↦ (hst x).trans
      (congrArg (fun i : V x ⟶ U.unop ↦ Q.presheaf.map i.op t) (Subsingleton.elim _ _))

/-- The sheafification of a presheaf valued in a concrete category with zero morphisms whose
objects carry a zero preserved by the morphisms vanishes if and only if every section of the
presheaf is locally zero: each point of its domain has a neighbourhood on which it restricts to
zero. -/
theorem isZero_presheafToSheaf_obj_iff [∀ A, Zero (CC A)]
    [∀ A B, ZeroHomClass (FC A B) (CC A) (CC B)] [HasZeroMorphisms C]
    [PreservesLimits (forget C)] [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (P : X.Presheaf C) :
    IsZero ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P) ↔
      ∀ (x : X) (U : Opens X) (s : ToType (P.obj (op U))), x ∈ U →
        ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ P.map (homOfLE h).op s = 0 :=
  (TopCat.Sheaf.isZero_iff_forall_isZero_stalk _).trans <| forall_congr' fun x ↦
    (isZero_stalk_sheafify_iff x P).trans (P.isZero_stalk_iff x)

end Concrete

section Pushforward

universe v

variable {C : Type v} [Category.{u} C] [HasColimits C]
  {X Y : TopCat.{u}} (f : X ⟶ Y) {F G : X.Presheaf C}

/-- The canonical pushforward map on stalks is natural in the presheaf. -/
@[reassoc]
theorem stalkPushforward_naturality (α : F ⟶ G) (x : X) :
    (stalkFunctor C (f x)).map ((pushforward C f).map α) ≫ G.stalkPushforward C f x =
      F.stalkPushforward C f x ≫ (stalkFunctor C x).map α := by
  refine stalk_hom_ext _ fun U hxU ↦ ?_
  -- The composites pass through both `P.stalk x` and `(stalkFunctor C x).obj P`, which agree only
  -- after unfolding `stalk`, so `rw` and `simp` cannot match the germ lemmas; chain them as terms.
  -- The middle step uses `pushforward_map_app'`, which holds by `rfl`.
  exact (stalkFunctor_map_germ_assoc U (f x) hxU _ _).trans
    ((congrArg (_ ≫ ·) (stalkPushforward_germ C f G U x hxU)).trans
      ((stalkFunctor_map_germ _ x hxU α).symm.trans
        (stalkPushforward_germ_assoc C f F U x hxU _).symm))

end Pushforward

end TopCat.Presheaf

namespace CategoryTheory.Functor

universe v w

variable {X : TopCat.{u}} {A : Type v} {B : Type w} [Category.{u} A] [Category.{u} B]
  [HasColimits A] [HasColimits B]
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
    fun F ↦ isIso_stalkFunctor_map_toSheafify x (F.obj ⋙ G)
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
lemma stalkFunctor_map_toSheafify_comp_stalkComposeAndSheafifyIso_hom_app
    (F : X.Sheaf A) :
    (stalkFunctor B x).map (toSheafify (Opens.grothendieckTopology X) (F.obj ⋙ G)) ≫
      (G.stalkComposeAndSheafifyIso x).hom.app F =
    (preservesColimitIso G ((OpenNhds.inclusion x).op ⋙ F.obj)).inv := by
  have := isIso_stalkFunctor_map_toSheafify x (F.obj ⋙ G)
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
