/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import TauCeti.CategoryTheory.Sites.Equivalence
public import Mathlib.Topology.Sheaves.Abelian
public import TauCeti.CategoryTheory.Sites.Continuous
public import TauCeti.CategoryTheory.Sites.GlobalSections
public import TauCeti.CategoryTheory.Sites.Over.Basic

public import Mathlib.Topology.Sheaves.Over
public import TauCeti.Topology.Category.TopCat.Opens

/-!
# Open embeddings and over categories of open subsets

Let `f : X ⟶ Y` be an open embedding of topological spaces, with open image `U = range f`.
Mathlib's `TopologicalSpace.Opens.overEquivalence` identifies `Over U` with the open subsets of the
subspace `U`. This file gives the corresponding equivalence `Over U ≌ Opens X` for the open
embedding itself: an open subset `W ⊆ U` goes to `f⁻¹(W)`, and an open subset `V ⊆ X` goes back to
`f(V)`. The equivalence is a dense subsite in both directions, so it induces an equivalence of
sheaf categories under which a sheaf `F` on `Y`, restricted to `U`, becomes the sheaf
`V ↦ F(f(V))` on `X`.

Working with `f` rather than with the subspace `U` keeps that sheaf literally equal to the
pushforward along `f(-)`, which is how Mathlib defines the restriction of a sheaf of modules along
an open immersion of schemes.

The construction of the dense-subsite instances is adapted from
`Mathlib.Topology.Sheaves.Over`, by Joël Riou.

## Main declarations

* `Topology.IsOpenEmbedding.overEquivalence`: the equivalence `Over (range f) ≌ Opens X`.
* The instances saying that its functor and inverse are dense subsites for the Grothendieck
  topologies of open covers.
* `Topology.IsOpenEmbedding.overPullbackSheafCongrIso`: restricting a sheaf on `Y` to `range f`
  and transporting it along `overEquivalence` is pushforward along the image functor `f(-)`.
* `TopologicalSpace.Opens.isLeftAdjoint_sheafRestrict`: restriction of sheaves to an open subset
  is a left adjoint whenever restriction to the over site is a left adjoint.
-/

public section

universe u

open CategoryTheory TopologicalSpace Topology

namespace Topology.IsOpenEmbedding

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenEmbedding f)

/-- An open embedding `f : X ⟶ Y` identifies the open subsets of `Y` contained in the range of
`f` with the open subsets of `X`, by taking preimages and images under `f`. -/
def overEquivalence :
    Over (⟨Set.range f, hf.isOpen_range⟩ : Opens Y) ≌ Opens X where
  functor.obj W := (Opens.map f).obj W.left
  functor.map g := (Opens.map f).map g.left
  inverse.obj V := Over.mk (Y := hf.functor.obj V) (homOfLE (Set.image_subset_range f V))
  inverse.map g := Over.homMk (hf.functor.map g)
  unitIso := NatIso.ofComponents (fun W ↦ Over.isoMk
    (eqToIso (Opens.ext (Set.image_preimage_eq_of_subset W.hom.le).symm)))
  counitIso := NatIso.ofComponents (fun V ↦ eqToIso (Opens.map_functor_eq' f hf V))

@[simp]
lemma overEquivalence_functor_obj (W : Over (⟨Set.range f, hf.isOpen_range⟩ : Opens Y)) :
    hf.overEquivalence.functor.obj W = (Opens.map f).obj W.left :=
  (rfl)

/-- The inverse of `overEquivalence`, followed by the forgetful functor from the over category,
is the image functor on open subsets. -/
def overEquivalenceInverseCompForgetIso :
    hf.overEquivalence.inverse ⋙ Over.forget _ ≅ hf.functor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

instance isDenseSubsite_overEquivalence_functor :
    CategoryTheory.Functor.IsDenseSubsite ((Opens.grothendieckTopology Y).over _)
      (Opens.grothendieckTopology X) hf.overEquivalence.functor where
  functorPushforward_mem_iff {V S} := by
    simp only [Opens.mem_grothendieckTopology, Sieve.mem_functorPushforward_functor]
    constructor
    · intro H y hyV
      obtain ⟨x, rfl⟩ := V.hom.le hyV
      obtain ⟨W, g, hW, hxW⟩ := H x hyV
      exact ⟨_, ((hf.overEquivalence.symm.toAdjunction.homEquiv _ _).symm g).left,
        ⟨_, _, 𝟙 _, hW, rfl⟩, x, hxW, rfl⟩
    · intro H x hxV
      obtain ⟨W, g, ⟨W', hW'V, hWW', hSW'V, rfl⟩, hxW⟩ := H (f x) hxV
      exact ⟨_, hf.overEquivalence.functor.map hW'V,
        S.downward_closed hSW'V (hf.overEquivalence.unitInv.app W'), hWW'.le hxW⟩

instance isDenseSubsite_overEquivalence_symm_inverse :
    CategoryTheory.Functor.IsDenseSubsite ((Opens.grothendieckTopology Y).over _)
      (Opens.grothendieckTopology X) hf.overEquivalence.symm.inverse :=
  inferInstanceAs (CategoryTheory.Functor.IsDenseSubsite
    ((Opens.grothendieckTopology Y).over _) (Opens.grothendieckTopology X)
      hf.overEquivalence.functor)

instance isDenseSubsite_overEquivalence_inverse :
    CategoryTheory.Functor.IsDenseSubsite (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology Y).over _) hf.overEquivalence.inverse :=
  inferInstanceAs (CategoryTheory.Functor.IsDenseSubsite (Opens.grothendieckTopology X)
    ((Opens.grothendieckTopology Y).over _) hf.overEquivalence.symm.functor)

instance isContinuous_functor : hf.functor.IsContinuous
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  hf.functor_isContinuous

/-- Restriction to the range of an open embedding, followed by transport along
`overEquivalence`, is naturally isomorphic to pushforward along the image functor on opens. -/
def overPullbackSheafCongrIso (A : Type*) [Category A] :
    (Opens.grothendieckTopology Y).overPullback A
        (⟨Set.range f, hf.isOpen_range⟩ : Opens Y) ⋙
      (hf.overEquivalence.sheafCongr
        ((Opens.grothendieckTopology Y).over _)
        (Opens.grothendieckTopology X) A).functor ≅
    hf.functor.sheafPushforwardContinuous A
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  CategoryTheory.Functor.sheafPushforwardContinuousComp'
    hf.overEquivalenceInverseCompForgetIso A (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology Y).over _) (Opens.grothendieckTopology Y)

end Topology.IsOpenEmbedding

namespace TopologicalSpace.Opens

/-- Restriction of sheaves to an open subset `U` is a left adjoint whenever restriction to the over
site `Over U` is a left adjoint. -/
instance isLeftAdjoint_sheafRestrict {X : TopCat} (U : Opens X) {A : Type*} [Category* A]
    [((Opens.grothendieckTopology X).overPullback A U).IsLeftAdjoint] :
    (U.sheafRestrict (C := A)).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso U.overPullbackSheafEquivOver

/-- Open restriction is additive because it is continuous pushforward on sheaves. -/
instance sheafRestrict_additive {X : Type*} [TopologicalSpace X] (U : Opens X)
    {A : Type*} [Category* A] [Preadditive A] :
    (U.sheafRestrict (X := TopCat.of X) (C := A)).Additive := by
  unfold TopologicalSpace.Opens.sheafRestrict
  infer_instance

end TopologicalSpace.Opens

/-! ### Sections and nested restriction -/

public noncomputable section
open CategoryTheory Limits Opposite
namespace TopologicalSpace.Opens
universe uA vA
variable {X : TopCat.{u}} {A : Type uA} [Category.{vA} A]
/-- The canonical map from the over-site representative of the top open to the identity open. -/
abbrev overTopMap (U : Opens X) :
    U.overEquivalence.inverse.obj (⊤ : Opens U) ⟶ Over.mk (𝟙 U) :=
  (Over.mkIdTerminal (X := U)).from _

/-- Sections on an open set are sections at the top of the restricted sheaf. -/
def sheafRestrictSectionsTopIso (U : Opens X) :
    (sheafSections (Opens.grothendieckTopology X) A).obj (op U) ≅
      U.sheafRestrict ⋙
        (sheafSections (Opens.grothendieckTopology U) A).obj
          (op (⊤ : Opens U)) :=
  NatIso.ofComponents (fun F ↦ F.obj.mapIso (eqToIso U.isOpenEmbedding_obj_top).op)
    (fun f ↦ (f.hom.naturality (eqToIso U.isOpenEmbedding_obj_top).hom.op).symm)

/-- Sections on an open set are the global sections of the restricted sheaf. -/
def sheafRestrictΓIso (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology U) A] :
    (sheafSections (Opens.grothendieckTopology X) A).obj (op U) ≅
      U.sheafRestrict ⋙ Sheaf.Γ (Opens.grothendieckTopology U) A :=
  sheafRestrictSectionsTopIso U ≪≫
    Functor.isoWhiskerLeft U.sheafRestrict
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology U)
        A isTerminalTop).symm

/-- The open/global-sections comparison cancels against restriction to the top. -/
@[reassoc]
lemma sheafRestrictΓIso_hom_app_ΓRes (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology U) A] (F : X.Sheaf A) :
    (sheafRestrictΓIso U).hom.app F ≫ (U.sheafRestrict.obj F).ΓRes (op ⊤) =
      (sheafRestrictSectionsTopIso U).hom.app F := by
  simp only [sheafRestrictΓIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
  rw [Category.assoc, Sheaf.ΓNatIsoSheafSections_inv_app_ΓRes]
  -- Direct evaluation and evaluation on the pushforward use the same restricted section carrier.
  erw [Category.comp_id]

/-- The top-sections comparison is evaluation along the over-site terminal map. -/
@[simp]
lemma sheafRestrictSectionsTopIso_hom_app (U : Opens X) (F : X.Sheaf A) :
    (sheafRestrictSectionsTopIso U).hom.app F =
      F.obj.map ((Over.mkIdTerminal (X := U)).from (U.overEquivalence.inverse.obj ⊤)).left.op := by
  -- The component of NatIso.ofComponents is the presheaf map of the canonical opens equality.
  change F.obj.map _ = F.obj.map _
  congr 1
  exact Subsingleton.elim _ _

variable {U V : Opens X}

instance inclusionSites_continuous (h : V ≤ U) :
    (inclusionSites h).IsContinuous (Opens.grothendieckTopology V) (Opens.grothendieckTopology U) :=
  Topology.IsOpenEmbedding.functor_isContinuous (X := TopCat.of V) (Y := TopCat.of U)
    (f := (Opens.toTopCat X).map (homOfLE h)) (isOpenEmbedding_of_le h)

/-- For `V ≤ U`, restriction of sheaves on the subspace `U` to the subspace `V`. -/
@[expose]
def restrictAlongInclusion (h : V ≤ U) :
    (TopCat.of U).Sheaf A ⥤ (TopCat.of V).Sheaf A :=
  (inclusionSites h).sheafPushforwardContinuous A
    (Opens.grothendieckTopology V) (Opens.grothendieckTopology U)

/-- Sections of a restricted sheaf on an open `D` of `V` are sections on `D` viewed in `U`. -/
@[simp]
lemma restrictAlongInclusion_obj_obj (h : V ≤ U) (F : (TopCat.of U).Sheaf A) (D : Opens V) :
    ((restrictAlongInclusion h).obj F).obj.obj (op D) = F.obj.obj (op ((inclusionSites h).obj D)) :=
  (rfl)

/-- Restriction maps of a restricted sheaf are those of the opens viewed in `U`. -/
@[simp]
lemma restrictAlongInclusion_obj_map (h : V ≤ U) (F : (TopCat.of U).Sheaf A) {D D' : Opens V}
    (f : D ⟶ D') :
    ((restrictAlongInclusion h).obj F).obj.map f.op = F.obj.map ((inclusionSites h).map f).op :=
  (rfl)

/-- A morphism of restricted sheaves has the components of the original morphism on the opens
viewed in `U`. -/
@[simp]
lemma restrictAlongInclusion_map_hom_app (h : V ≤ U) {F G : (TopCat.of U).Sheaf A} (φ : F ⟶ G)
    (D : Opens V) :
    ((restrictAlongInclusion h).map φ).hom.app (op D) = φ.hom.app (op ((inclusionSites h).obj D)) :=
  (rfl)

/-- For `V ≤ U`, restricting a sheaf on `X` to `U` and then to `V` is restricting it to `V`. -/
def sheafRestrictionCompositionIso (h : V ≤ U) :
    U.sheafRestrict ⋙ restrictAlongInclusion (A := A) h ≅
      V.sheafRestrict (C := A) := by
  exact @Functor.sheafPushforwardContinuousComp'
    (Opens V) _ (Opens U) _ (Opens X) _
    (inclusionSites h) U.isOpenEmbedding.functor V.isOpenEmbedding.functor
    (inclusionSitesCompIso h) A _
    (Opens.grothendieckTopology V) (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)
    (inclusionSites_continuous h) U.isOpenEmbedding.functor_isContinuous
    V.isOpenEmbedding.functor_isContinuous

/-- The components of `sheafRestrictionCompositionIso` are the presheaf maps along the equality of
the two image opens. -/
@[simp]
lemma sheafRestrictionCompositionIso_hom_app_hom_app (h : V ≤ U) (F : X.Sheaf A) (D : Opens V) :
    ((sheafRestrictionCompositionIso h).hom.app F).hom.app (op D) =
      F.obj.map ((inclusionSitesCompIso h).inv.app D).op := by
  rw [sheafRestrictionCompositionIso]
  -- `U.isOpenEmbedding.functor` has source `Opens ((toTopCat X).obj U)`, which is `Opens U` only
  -- after unfolding `Opens.toTopCat`, so `rw` fails with a motive type mismatch.
  erw [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app]

/-- The canonical relative-open site equivalence is cocontinuous. -/
instance relativeSites_functor_cocontinuous (h : V ≤ U) :
    (relativeSites h).functor.IsCocontinuous
      (Opens.grothendieckTopology (relativeOpen h))
      (Opens.grothendieckTopology V) := by
  apply ((relativeSites h).toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
  exact coverPreserving_opens_map (relativeOpenIso h).hom
/-- The inverse relative-open site equivalence is cocontinuous. -/
instance relativeSites_inverse_cocontinuous (h : V ≤ U) :
    (relativeSites h).inverse.IsCocontinuous
      (Opens.grothendieckTopology V)
      (Opens.grothendieckTopology (relativeOpen h)) := by
  apply ((relativeSites h).symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
  exact coverPreserving_opens_map (relativeOpenIso h).inv
/-- The inverse relative-open site functor is a dense subsite. -/
instance relativeSites_inverse_dense (h : V ≤ U) :
    (relativeSites h).inverse.IsDenseSubsite
      (Opens.grothendieckTopology V)
      (Opens.grothendieckTopology (relativeOpen h)) := by
  exact Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _
    (relativeSites h)
/-- Transport sheaves from the relative open in U to the same open as a subspace of X. -/
abbrev relativeSheafEquivalence (h : V ≤ U) :
    (TopCat.of (relativeOpen h)).Sheaf A ≌
      (TopCat.of V).Sheaf A :=
  (relativeSites h).sheafCongr
    (Opens.grothendieckTopology (relativeOpen h))
    (Opens.grothendieckTopology V) A
/-- Transported sheaf sections are sections on the homeomorphism's inverse image open. -/
@[simp]
lemma relativeSheafEquivalence_functor_obj_obj (h : V ≤ U)
    (F : (TopCat.of (relativeOpen h)).Sheaf A) (D : Opens V) :
    ((relativeSheafEquivalence (A := A) h).functor.obj F).obj.obj (op D) =
      F.obj.obj (op ((Opens.map (relativeOpenIso h).hom).obj D)) := rfl
/-- Restriction in the transported sheaf is restriction on the homeomorphism's inverse image. -/
@[simp]
lemma relativeSheafEquivalence_functor_obj_map (h : V ≤ U)
    (F : (TopCat.of (relativeOpen h)).Sheaf A)
    {D D' : Opens V} (f : D ⟶ D') :
    ((relativeSheafEquivalence (A := A) h).functor.obj F).obj.map f.op =
      F.obj.map ((Opens.map (relativeOpenIso h).hom).map f).op := rfl

private lemma relativeSites_inverse_top (h : V ≤ U) :
    (relativeSites h).inverse.obj (⊤ : Opens V) = ⊤ := Opens.map_top _
private def relativeSectionsTopIso (h : V ≤ U) :
    (sheafSections (Opens.grothendieckTopology (relativeOpen h)) A).obj (op ⊤) ≅
    (relativeSheafEquivalence (A := A) h).functor ⋙
      (sheafSections (Opens.grothendieckTopology V) A).obj (op ⊤) :=
  NatIso.ofComponents (fun F ↦ F.obj.mapIso (eqToIso (relativeSites_inverse_top h)).op)
    (fun f ↦ (f.hom.naturality (eqToIso (relativeSites_inverse_top h)).hom.op).symm)
/-- The canonical relative-open equivalence identifies the global-sections functors. -/
def relativeΓIso (h : V ≤ U)
    [HasWeakSheafify (Opens.grothendieckTopology (relativeOpen h)) A]
    [HasWeakSheafify (Opens.grothendieckTopology V) A] :
    Sheaf.Γ (Opens.grothendieckTopology (relativeOpen h)) A ≅
      (relativeSheafEquivalence (A := A) h).functor ⋙
        Sheaf.Γ (Opens.grothendieckTopology V) A :=
  Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop ≪≫ relativeSectionsTopIso h ≪≫
    Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).symm
private lemma relativeΓIso_hom_app_ΓRes_top (h : V ≤ U)
    [HasWeakSheafify (Opens.grothendieckTopology (relativeOpen h)) A]
    [HasWeakSheafify (Opens.grothendieckTopology V) A]
    (F : (TopCat.of (relativeOpen h)).Sheaf A) :
    (relativeΓIso h).hom.app F ≫
      ((relativeSheafEquivalence (A := A) h).functor.obj F).ΓRes (op ⊤) = F.ΓRes (op ⊤) := by
  -- `relativeΓIso` is `Γ ≅ sections at ⊤`, the identity open map, then the inverse for `V`.
  simp only [relativeΓIso, relativeSectionsTopIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc, Sheaf.ΓNatIsoSheafSections_inv_app_ΓRes,
    Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes]
  -- The transport component is the restriction along the top-preservation map, which `ΓRes_map`
  -- absorbs; the two top opens agree by `relativeSites_inverse_top`.
  -- The goal is only type-correct up to unfolding `relativeSheafEquivalence`, so `rw` and `simp`
  -- cannot cancel the trailing identity; cancel it by `congrArg` instead.
  exact (congrArg (F.ΓRes (op ⊤) ≫ ·) (Category.comp_id _)).trans (Sheaf.ΓRes_map F _)

/-- Relative global-sections transport acts by the restriction on every open. -/
@[reassoc]
lemma relativeΓIso_hom_app_ΓRes (h : V ≤ U)
    [HasWeakSheafify (Opens.grothendieckTopology (relativeOpen h)) A]
    [HasWeakSheafify (Opens.grothendieckTopology V) A]
    (F : (TopCat.of (relativeOpen h)).Sheaf A) (D : Opens V) :
    (relativeΓIso h).hom.app F ≫
      ((relativeSheafEquivalence (A := A) h).functor.obj F).ΓRes (op D) =
      F.ΓRes (op ((Opens.map (relativeOpenIso h).hom).obj D)) := by
  rw [← Sheaf.ΓRes_map _ (homOfLE (show D ≤ ⊤ from le_top)).op, ← Category.assoc]
  rw [relativeΓIso_hom_app_ΓRes_top]
  -- Sections precompose with the canonical homeomorphism's opens map.
  change F.ΓRes (op ⊤) ≫ F.obj.map _ = _
  exact Sheaf.ΓRes_map F _

private def relativeRestrictionIso (h : V ≤ U) :
    (relativeOpen h).sheafRestrict ⋙ (relativeSheafEquivalence (A := A) h).functor ≅
      restrictAlongInclusion (A := A) h := by
  exact @Functor.sheafPushforwardContinuousComp'
    (Opens V) _ (Opens (relativeOpen h)) _ (Opens U) _
    (Opens.map (relativeOpenIso h).hom) (relativeInclusionSites h)
    (inclusionSites h) (relativeRestrictionSitesIso h) A _
    (Opens.grothendieckTopology V) (Opens.grothendieckTopology (relativeOpen h))
    (Opens.grothendieckTopology U)
    (by
      apply Functor.isContinuous_of_coverPreserving
      · exact compatiblePreserving_opens_map (relativeOpenIso h).hom
      · exact coverPreserving_opens_map (relativeOpenIso h).hom)
    (@Topology.IsOpenEmbedding.functor_isContinuous (TopCat.of (relativeOpen h)) (TopCat.of U)
      (Opens.inclusion' (X := TopCat.of U) (relativeOpen h))
      (Opens.isOpenEmbedding (X := TopCat.of U) (relativeOpen h)))
    (inclusionSites_continuous h)
/-- The coefficient isomorphism comparing nested restriction with direct restriction. -/
def nestedRestrictionIso (h : V ≤ U) :
    U.sheafRestrict ⋙ (relativeOpen h).sheafRestrict (X := TopCat.of U) ⋙
      (relativeSheafEquivalence (A := A) h).functor ≅ V.sheafRestrict (C := A) :=
  Functor.isoWhiskerLeft U.sheafRestrict (relativeRestrictionIso h) ≪≫
    sheafRestrictionCompositionIso h

/-- The nested coefficient isomorphism is the section map along the image-open equality. -/
@[simp]
lemma nestedRestrictionIso_hom_app_hom_app (h : V ≤ U)
    (F : X.Sheaf A) (D : Opens V) :
    ((nestedRestrictionIso h).hom.app F).hom.app (op D) =
      F.obj.map (eqToHom (nestedOpen_image_eq h D).symm).op := by
  simp only [nestedRestrictionIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app]
  simp only [relativeRestrictionIso, sheafRestrictionCompositionIso,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app]
  -- The first factor is now a map of sections of `U.sheafRestrict.obj F`, while the composite
  -- expects sections of `(U.sheafRestrict ⋙ restrictAlongInclusion h).obj F`. These agree only
  -- after unfolding the composite and `restrictAlongInclusion`, so `rw` fails with a motive type
  -- mismatch and `simp only` leaves this component.
  erw [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app]
  -- Both pushforward components are the presheaf maps of the corresponding open inclusions.
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  -- The two maps still carry the `Opens.toTopCat` form of the open-embedding proof, so the goal is
  -- not type-correct at implicit transparency and `rw [← F.obj.map_comp]` finds no match.
  erw [← CategoryTheory.Functor.map_comp]
  congr 1

end TopologicalSpace.Opens
