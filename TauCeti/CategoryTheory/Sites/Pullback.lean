/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Sites.Continuous

/-!
# Existence, functoriality, and colimit preservation of sheaf pullback

Mathlib's `CategoryTheory.Functor.sheafPullback` is the left adjoint of the pushforward of sheaves
`u.sheafPushforwardContinuous A J K` along a continuous functor `u : C ⥤ D` between sites `(C, J)`
and `(D, K)`.

This file supplies:
* existence of `sheafPullback` when `C` is `w`-essentially small, `D` is `w`-locally small, and
  `A` has `w`-small colimits and weak sheafification on `(D, K)`, as well as transport of existence
  across a continuous functor `ι : C₀ ⥤ C` whose sheaf pushforward is an equivalence (such as an
  essentially small dense subsite);
* additivity when `A` is preadditive and left-adjointness (hence preservation of all colimits) for
  any coefficient category `A`;
* natural isomorphisms for `sheafPullback` along natural isomorphisms of continuous functors,
  identities, and compositions, obtained as conjugates of Mathlib's pushforward isomorphisms,
  together with their `conjugateEquiv` characterizations and unitality/associativity coherences.

## Main declarations

* `CategoryTheory.Functor.isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall`:
  pushforward from a locally small site to an essentially small site has a left adjoint.
* `CategoryTheory.Functor.isRightAdjoint_sheafPushforwardContinuous_of_isEquivalence`:
  existence of `sheafPullback` descends along a continuous functor inducing an equivalence on
  sheaves.
* `CategoryTheory.Functor.sheafPullback_additive`: the pullback of sheaves with values in a
  preadditive category is additive.
* `CategoryTheory.Functor.isLeftAdjoint_sheafPullback`: the pullback of sheaves is a left adjoint
  (and hence preserves colimits).
* `CategoryTheory.Functor.sheafPullbackIso`, `CategoryTheory.Functor.sheafPullbackId`,
  `CategoryTheory.Functor.sheafPullbackId'`, `CategoryTheory.Functor.sheafPullbackComp`,
  `CategoryTheory.Functor.sheafPullbackComp'`: congruence, identity, and composition isomorphisms
  for `sheafPullback`, with `conjugateEquiv` and coherence lemmas.
-/

public section

universe w

namespace CategoryTheory.Functor

open Limits

section Existence

/-- If `(C, J)` is `w`-essentially small, `(D, K)` is `w`-locally small, and `A` has `w`-small
colimits and weak sheafification for `K`, then `u.sheafPushforwardContinuous A J K` is a right
adjoint. -/
lemma isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (u : C ⥤ D) (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [EssentiallySmall.{w} C] [LocallySmall.{w} D]
    [HasColimitsOfSize.{w, w} A] [HasWeakSheafify K A] :
    (u.sheafPushforwardContinuous A J K).IsRightAdjoint := by
  have (F : Cᵒᵖ ⥤ A) : u.op.HasLeftKanExtension F :=
    have : u.op.HasPointwiseLeftKanExtension F := fun Y ↦
      have := hasColimitsOfShape_of_essentiallySmall.{w} (CostructuredArrow u.op Y) A
      inferInstance
    inferInstance
  exact (sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).isRightAdjoint

/-- If `ι : C₀ ⥤ C` induces an equivalence on sheaves and `ι ⋙ u` admits a sheaf pullback, then `u`
admits a sheaf pullback. This applies for instance when `(C₀, J₀)` is an essentially small dense
subsite of a large site `(C, J)`. -/
lemma isRightAdjoint_sheafPushforwardContinuous_of_isEquivalence
    {C₀ : Type*} [Category* C₀] {C : Type*} [Category* C] {D : Type*} [Category* D]
    (ι : C₀ ⥤ C) (u : C ⥤ D) (A : Type*) [Category* A]
    (J₀ : GrothendieckTopology C₀) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [ι.IsContinuous J₀ J] [u.IsContinuous J K]
    [(ι.sheafPushforwardContinuous A J₀ J).IsEquivalence]
    [haveI := isContinuous_comp ι u J₀ J K;
      ((ι ⋙ u).sheafPushforwardContinuous A J₀ K).IsRightAdjoint] :
    (u.sheafPushforwardContinuous A J K).IsRightAdjoint := by
  have := isContinuous_comp ι u J₀ J K
  exact (isRightAdjoint_comp_iff_left _ (ι.sheafPushforwardContinuous A J₀ J)).mp
    (isRightAdjoint_of_iso (sheafPushforwardContinuousComp ι u A J₀ J K).symm)

end Existence

section ColimitPreservation

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  {A : Type*} [Category* A]
  (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- The pullback of sheaves with values in a preadditive category along a continuous functor is
additive, as a left adjoint of an additive pushforward functor. -/
instance sheafPullback_additive [Preadditive A] :
    (u.sheafPullback A J K).Additive :=
  (u.sheafAdjunctionContinuous A J K).left_adjoint_additive

/-- The pullback of sheaves along a continuous functor is a left adjoint, hence preserves all
colimits. -/
instance isLeftAdjoint_sheafPullback :
    (u.sheafPullback A J K).IsLeftAdjoint :=
  (u.sheafAdjunctionContinuous A J K).isLeftAdjoint

end ColimitPreservation

section Functoriality

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  {B : Type*} [Category* B]
  (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (M : GrothendieckTopology B)

/-- Naturally isomorphic continuous functors induce naturally isomorphic sheaf pullback functors,
conjugate to `sheafPushforwardContinuousIso`. -/
noncomputable def sheafPullbackIso {u u' : C ⥤ D} (e : u ≅ u')
    [u.IsContinuous J K] [u'.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u'.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    u.sheafPullback A J K ≅ u'.sheafPullback A J K :=
  (conjugateIsoEquiv (u'.sheafAdjunctionContinuous A J K)
    (u.sheafAdjunctionContinuous A J K)).symm (sheafPushforwardContinuousIso e.symm A J K)

@[simp]
lemma conjugateEquiv_sheafPullbackIso_hom {u u' : C ⥤ D} (e : u ≅ u')
    [u.IsContinuous J K] [u'.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u'.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    conjugateEquiv (u'.sheafAdjunctionContinuous A J K) (u.sheafAdjunctionContinuous A J K)
      (sheafPullbackIso A J K e).hom = (sheafPushforwardContinuousIso e.symm A J K).hom := by
  simp [sheafPullbackIso]

@[simp]
lemma conjugateEquiv_sheafPullbackIso_inv {u u' : C ⥤ D} (e : u ≅ u')
    [u.IsContinuous J K] [u'.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u'.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    conjugateEquiv (u.sheafAdjunctionContinuous A J K) (u'.sheafAdjunctionContinuous A J K)
      (sheafPullbackIso A J K e).inv = (sheafPushforwardContinuousIso e.symm A J K).inv := by
  simp [sheafPullbackIso]

@[simp]
lemma sheafPullbackIso_refl (u : C ⥤ D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    sheafPullbackIso A J K (Iso.refl u) = Iso.refl (u.sheafPullback A J K) := by
  ext : 1
  apply (conjugateEquiv (u.sheafAdjunctionContinuous A J K)
    (u.sheafAdjunctionContinuous A J K)).injective
  rw [conjugateEquiv_sheafPullbackIso_hom, Iso.refl_hom, conjugateEquiv_id]
  ext
  simp only [Iso.refl_symm, sheafPushforwardContinuousIso_hom, Iso.refl_inv,
    sheafPushforwardContinuousNatTrans_app_hom, NatTrans.op_id, ObjectProperty.ι_obj,
    whiskerRight_id', NatTrans.id_app, comp_obj, op_obj, ObjectProperty.FullSubcategory.id_hom]
  exact rfl

lemma sheafPullbackIso_trans {u₁ u₂ u₃ : C ⥤ D} (e₁ : u₁ ≅ u₂) (e₂ : u₂ ≅ u₃)
    [u₁.IsContinuous J K] [u₂.IsContinuous J K] [u₃.IsContinuous J K]
    [(u₁.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u₂.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u₃.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    sheafPullbackIso A J K (e₁ ≪≫ e₂) =
      sheafPullbackIso A J K e₁ ≪≫ sheafPullbackIso A J K e₂ := by
  ext : 1
  apply (conjugateEquiv (u₃.sheafAdjunctionContinuous A J K)
    (u₁.sheafAdjunctionContinuous A J K)).injective
  rw [conjugateEquiv_sheafPullbackIso_hom, Iso.trans_hom, ← conjugateEquiv_comp,
    conjugateEquiv_sheafPullbackIso_hom, conjugateEquiv_sheafPullbackIso_hom]
  ext
  simp only [Iso.trans_symm, sheafPushforwardContinuousIso_hom, Iso.trans_inv, Iso.symm_inv,
    sheafPushforwardContinuousNatTrans_app_hom, NatTrans.op_comp, ObjectProperty.ι_obj,
    NatTrans.comp_app, op_obj, whiskerRight_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.map_comp]
  exact rfl

@[simp]
lemma sheafPullbackIso_symm {u u' : C ⥤ D} (e : u ≅ u')
    [u.IsContinuous J K] [u'.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u'.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    (sheafPullbackIso A J K e).symm = sheafPullbackIso A J K e.symm := by
  ext : 1
  apply (conjugateEquiv (u.sheafAdjunctionContinuous A J K)
    (u'.sheafAdjunctionContinuous A J K)).injective
  simp

instance isRightAdjoint_sheafPushforwardContinuous_id :
    ((𝟭 C).sheafPushforwardContinuous A J J).IsRightAdjoint :=
  isRightAdjoint_of_iso (sheafPushforwardContinuousId A J).symm

/-- The sheaf pullback along the identity functor identifies with the identity functor on
sheaves. -/
noncomputable def sheafPullbackId :
    (𝟭 C).sheafPullback A J J ≅ 𝟭 (Sheaf J A) :=
  Adjunction.leftAdjointIdIso ((𝟭 C).sheafAdjunctionContinuous A J J)
    (sheafPushforwardContinuousId A J)

@[simp]
lemma conjugateEquiv_sheafPullbackId_hom :
    conjugateEquiv Adjunction.id ((𝟭 C).sheafAdjunctionContinuous A J J)
      (sheafPullbackId A J).hom = (sheafPushforwardContinuousId A J).inv :=
  Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _

@[simp]
lemma conjugateEquiv_sheafPullbackId_inv :
    conjugateEquiv ((𝟭 C).sheafAdjunctionContinuous A J J) Adjunction.id
      (sheafPullbackId A J).inv = (sheafPushforwardContinuousId A J).hom := by
  simp [sheafPullbackId, Adjunction.leftAdjointIdIso]

/-- If a continuous functor `u : C ⥤ C` is naturally isomorphic to `𝟭 C`, its sheaf pullback
identifies with the identity functor. -/
noncomputable def sheafPullbackId' {u : C ⥤ C} (e : u ≅ 𝟭 C)
    [u.IsContinuous J J] [(u.sheafPushforwardContinuous A J J).IsRightAdjoint] :
    u.sheafPullback A J J ≅ 𝟭 (Sheaf J A) :=
  sheafPullbackIso A J J e ≪≫ sheafPullbackId A J

lemma sheafPullbackId'_eq {u : C ⥤ C} (e : u ≅ 𝟭 C)
    [u.IsContinuous J J] [(u.sheafPushforwardContinuous A J J).IsRightAdjoint] :
    sheafPullbackId' A J e = sheafPullbackIso A J J e ≪≫ sheafPullbackId A J :=
  (rfl)

@[simp]
lemma sheafPullbackId'_refl :
    sheafPullbackId' A J (Iso.refl (𝟭 C)) = sheafPullbackId A J := by
  simp [sheafPullbackId'_eq]

/-- If `u : C ⥤ D` and `v : D ⥤ E` admit sheaf pullbacks, so does `u ⋙ v`. -/
lemma isRightAdjoint_sheafPushforwardContinuous_comp (u : C ⥤ D) (v : D ⥤ E)
    [u.IsContinuous J K] [v.IsContinuous K L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint] :
    letI := isContinuous_comp u v J K L
    ((u ⋙ v).sheafPushforwardContinuous A J L).IsRightAdjoint := by
  have := isContinuous_comp u v J K L
  exact isRightAdjoint_of_iso (sheafPushforwardContinuousComp u v A J K L)

/-- The sheaf pullback along a composite `u ⋙ v` of continuous functors identifies with the
composite of their sheaf pullbacks. -/
noncomputable def sheafPullbackComp (u : C ⥤ D) (v : D ⥤ E)
    [u.IsContinuous J K] [v.IsContinuous K L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint] :
    letI := isContinuous_comp u v J K L
    letI := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
    (u ⋙ v).sheafPullback A J L ≅ u.sheafPullback A J K ⋙ v.sheafPullback A K L :=
  letI := isContinuous_comp u v J K L
  letI := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
  (Adjunction.leftAdjointCompIso
    (u.sheafAdjunctionContinuous A J K) (v.sheafAdjunctionContinuous A K L)
    ((u ⋙ v).sheafAdjunctionContinuous A J L)
    (sheafPushforwardContinuousComp u v A J K L)).symm

@[simp]
lemma conjugateEquiv_sheafPullbackComp_hom (u : C ⥤ D) (v : D ⥤ E)
    [u.IsContinuous J K] [v.IsContinuous K L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint] :
    letI := isContinuous_comp u v J K L
    letI := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
    conjugateEquiv
      ((u.sheafAdjunctionContinuous A J K).comp (v.sheafAdjunctionContinuous A K L))
      ((u ⋙ v).sheafAdjunctionContinuous A J L)
      (sheafPullbackComp A J K L u v).hom =
      (sheafPushforwardContinuousComp u v A J K L).hom := by
  have := isContinuous_comp u v J K L
  have := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

@[simp]
lemma conjugateEquiv_sheafPullbackComp_inv (u : C ⥤ D) (v : D ⥤ E)
    [u.IsContinuous J K] [v.IsContinuous K L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint] :
    letI := isContinuous_comp u v J K L
    letI := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
    conjugateEquiv
      ((u ⋙ v).sheafAdjunctionContinuous A J L)
      ((u.sheafAdjunctionContinuous A J K).comp (v.sheafAdjunctionContinuous A K L))
      (sheafPullbackComp A J K L u v).inv =
      (sheafPushforwardContinuousComp u v A J K L).inv := by
  have := isContinuous_comp u v J K L
  have := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
  simp [sheafPullbackComp, Adjunction.leftAdjointCompIso]

/-- Left unitality of `sheafPullbackComp` with respect to `sheafPullbackId`. -/
lemma sheafPullbackComp_id_left (u : C ⥤ D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    sheafPullbackComp A J J K (𝟭 C) u =
      (Functor.leftUnitor (u.sheafPullback A J K)).symm ≪≫
        Functor.isoWhiskerRight (sheafPullbackId A J).symm (u.sheafPullback A J K) := by
  rw [← Iso.symm_eq_iff]
  refine (Adjunction.leftAdjointCompIso_id_comp
    ((𝟭 C).sheafAdjunctionContinuous A J J) (u.sheafAdjunctionContinuous A J K)
    (sheafPushforwardContinuousComp (𝟭 C) u A J J K)
    (sheafPushforwardContinuousId A J) ?_).trans ?_
  · ext
    simp only [comp_obj, sheafPushforwardContinuousComp_hom_app_hom_app, id_obj, Iso.trans_hom,
      isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app, rightUnitor_hom_app, Category.comp_id,
      sheafPushforwardContinuousId_hom_app_hom_app]
    exact rfl
  · rfl

/-- Right unitality of `sheafPullbackComp` with respect to `sheafPullbackId`. -/
lemma sheafPullbackComp_id_right (u : C ⥤ D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    sheafPullbackComp A J K K u (𝟭 D) =
      (Functor.rightUnitor (u.sheafPullback A J K)).symm ≪≫
        Functor.isoWhiskerLeft (u.sheafPullback A J K) (sheafPullbackId A K).symm := by
  rw [← Iso.symm_eq_iff]
  refine (Adjunction.leftAdjointCompIso_comp_id
    (u.sheafAdjunctionContinuous A J K) ((𝟭 D).sheafAdjunctionContinuous A K K)
    (sheafPushforwardContinuousComp u (𝟭 D) A J K K)
    (sheafPushforwardContinuousId A K) ?_).trans ?_
  · ext
    simp only [comp_obj, sheafPushforwardContinuousComp_hom_app_hom_app, id_obj, Iso.trans_hom,
      isoWhiskerRight_hom, NatTrans.comp_app, whiskerRight_app, leftUnitor_hom_app,
      Category.comp_id, sheafPushforwardContinuous_map_hom_app,
      sheafPushforwardContinuousId_hom_app_hom_app]
    exact rfl
  · rfl

/-- Associativity coherence of `sheafPullbackComp` along three composable continuous functors. -/
lemma sheafPullbackComp_assoc (u : C ⥤ D) (v : D ⥤ E) (w' : E ⥤ B)
    [u.IsContinuous J K] [v.IsContinuous K L] [w'.IsContinuous L M]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint]
    [(w'.sheafPushforwardContinuous A L M).IsRightAdjoint] :
    letI := isContinuous_comp u v J K L
    letI := isContinuous_comp v w' K L M
    letI := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
    letI := isRightAdjoint_sheafPushforwardContinuous_comp A K L M v w'
    sheafPullbackComp A J L M (u ⋙ v) w' ≪≫
      Functor.isoWhiskerRight (sheafPullbackComp A J K L u v) (w'.sheafPullback A L M) ≪≫
      Functor.associator _ _ _ =
    sheafPullbackComp A J K M u (v ⋙ w') ≪≫
      Functor.isoWhiskerLeft (u.sheafPullback A J K) (sheafPullbackComp A K L M v w') := by
  have := isContinuous_comp u v J K L
  have := isContinuous_comp v w' K L M
  have := isContinuous_comp u (v ⋙ w') J K M
  have := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
  have := isRightAdjoint_sheafPushforwardContinuous_comp A K L M v w'
  have := isRightAdjoint_sheafPushforwardContinuous_comp A J K M u (v ⋙ w')
  rw [← Iso.symm_eq_iff]
  simp only [sheafPullbackComp, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
    Functor.isoWhiskerLeft_symm, Functor.isoWhiskerRight_symm]
  exact (Adjunction.leftAdjointCompIso_assoc
    (u.sheafAdjunctionContinuous A J K) (v.sheafAdjunctionContinuous A K L)
    (w'.sheafAdjunctionContinuous A L M)
    ((u ⋙ v).sheafAdjunctionContinuous A J L)
    ((v ⋙ w').sheafAdjunctionContinuous A K M)
    ((u ⋙ v ⋙ w').sheafAdjunctionContinuous A J M)
    (sheafPushforwardContinuousComp u v A J K L)
    (sheafPushforwardContinuousComp v w' A K L M)
    (sheafPushforwardContinuousComp u (v ⋙ w') A J K M)
    (sheafPushforwardContinuousComp (u ⋙ v) w' A J L M) (by
      ext
      simp only [comp_obj, Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app,
        Iso.symm_hom, associator_inv_app, isoWhiskerRight_hom, whiskerRight_app, Category.id_comp]
      exact rfl)).symm

/-- Given an isomorphism `u ⋙ v ≅ uv` of continuous functors, the sheaf pullback along `uv`
identifies with the composite of the sheaf pullbacks along `u` and `v`. -/
noncomputable def sheafPullbackComp' {u : C ⥤ D} {v : D ⥤ E} {uv : C ⥤ E}
    (e : u ⋙ v ≅ uv)
    [u.IsContinuous J K] [v.IsContinuous K L] [uv.IsContinuous J L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint]
    [(uv.sheafPushforwardContinuous A J L).IsRightAdjoint] :
    uv.sheafPullback A J L ≅ u.sheafPullback A J K ⋙ v.sheafPullback A K L :=
  letI := isContinuous_comp u v J K L
  letI := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
  sheafPullbackIso A J L e.symm ≪≫ sheafPullbackComp A J K L u v

lemma sheafPullbackComp'_eq {u : C ⥤ D} {v : D ⥤ E} {uv : C ⥤ E}
    (e : u ⋙ v ≅ uv)
    [u.IsContinuous J K] [v.IsContinuous K L] [uv.IsContinuous J L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint]
    [(uv.sheafPushforwardContinuous A J L).IsRightAdjoint] :
    letI := isContinuous_comp u v J K L
    letI := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
    sheafPullbackComp' A J K L e =
      sheafPullbackIso A J L e.symm ≪≫ sheafPullbackComp A J K L u v :=
  (rfl)

@[simp]
lemma sheafPullbackComp'_refl (u : C ⥤ D) (v : D ⥤ E)
    [u.IsContinuous J K] [v.IsContinuous K L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint] :
    letI := isContinuous_comp u v J K L
    letI := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
    sheafPullbackComp' A J K L (Iso.refl (u ⋙ v)) = sheafPullbackComp A J K L u v := by
  have := isContinuous_comp u v J K L
  have := isRightAdjoint_sheafPushforwardContinuous_comp A J K L u v
  simp [sheafPullbackComp'_eq]

end Functoriality

end CategoryTheory.Functor
