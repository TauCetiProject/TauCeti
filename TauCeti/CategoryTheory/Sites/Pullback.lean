/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Sites.Continuous

/-!
# Existence, functoriality, and exactness of sheaf pullback

Mathlib's `CategoryTheory.Functor.sheafPullback` is the left adjoint of the pushforward of sheaves
`u.sheafPushforwardContinuous A J K` along a continuous functor `u : C ⥤ D` between sites `(C, J)`
and `(D, K)`.

This file supplies:
* existence of `sheafPullback` when `C` is `w`-essentially small, `D` is `w`-locally small, and
  `A` has `w`-small colimits and weak sheafification on `(D, K)`, as well as transport of existence
  across a continuous functor `ι : C₀ ⥤ C` whose sheaf pushforward is an equivalence (such as an
  essentially small dense subsite);
* additivity when `A` is preadditive and preservation of finite colimits for any coefficient
  category `A`;
* natural isomorphisms for `sheafPullback` along natural isomorphisms of continuous functors,
  identities, and compositions, obtained as conjugates of Mathlib's pushforward isomorphisms.

## Main declarations

* `CategoryTheory.Functor.isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall`:
  pushforward from a locally small site to an essentially small site has a left adjoint.
* `CategoryTheory.Functor.isRightAdjoint_sheafPushforwardContinuous_of_isEquivalence`:
  existence of `sheafPullback` descends along a continuous functor inducing an equivalence on
  sheaves.
* `CategoryTheory.Functor.sheafPullback_additive`: the pullback of sheaves with values in a
  preadditive category is additive.
* `CategoryTheory.Functor.preservesFiniteColimits_sheafPullback`: the pullback of sheaves
  preserves finite colimits.
* `CategoryTheory.Functor.sheafPullbackIso`, `CategoryTheory.Functor.sheafPullbackId`,
  `CategoryTheory.Functor.sheafPullbackId'`, `CategoryTheory.Functor.sheafPullbackComp`,
  `CategoryTheory.Functor.sheafPullbackComp'`: congruence, identity, and composition isomorphisms
  for `sheafPullback`.
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
  have : ∀ F : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension F := fun F ↦
    letI : u.op.HasPointwiseLeftKanExtension F := fun Y ↦
      letI := hasColimitsOfShape_of_essentiallySmall.{w} (CostructuredArrow u.op Y) A
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
  let e := (ι.sheafPushforwardContinuous A J₀ J).asEquivalence
  let adj := e.toAdjunction.comp
    (Adjunction.ofIsRightAdjoint ((ι ⋙ u).sheafPushforwardContinuous A J₀ K))
  exact (adj.ofNatIsoRight (Functor.isoWhiskerRight
    (sheafPushforwardContinuousComp ι u A J₀ J K).symm e.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.unitIso.symm ≪≫
    Functor.rightUnitor _)).isRightAdjoint

end Existence

section Exactness

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

/-- The pullback of sheaves along a continuous functor preserves finite colimits, as a left
adjoint. -/
instance preservesFiniteColimits_sheafPullback :
    PreservesFiniteColimits (u.sheafPullback A J K) :=
  letI := (u.sheafAdjunctionContinuous A J K).leftAdjoint_preservesColimits.{0, 0}
  inferInstance

end Exactness

section Functoriality

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)

/-- Naturally isomorphic continuous functors induce naturally isomorphic sheaf pullback functors,
conjugate to `sheafPushforwardContinuousIso`. -/
noncomputable def sheafPullbackIso {u u' : C ⥤ D} (e : u ≅ u')
    [u.IsContinuous J K] [u'.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u'.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    u.sheafPullback A J K ≅ u'.sheafPullback A J K :=
  (conjugateIsoEquiv (u'.sheafAdjunctionContinuous A J K)
    (u.sheafAdjunctionContinuous A J K)).symm (sheafPushforwardContinuousIso e.symm A J K)

instance isRightAdjoint_sheafPushforwardContinuous_id :
    ((𝟭 C).sheafPushforwardContinuous A J J).IsRightAdjoint :=
  (Adjunction.id.ofNatIsoRight (sheafPushforwardContinuousId A J).symm).isRightAdjoint

/-- The sheaf pullback along the identity functor identifies with the identity functor on
sheaves. -/
noncomputable def sheafPullbackId :
    (𝟭 C).sheafPullback A J J ≅ 𝟭 (Sheaf J A) :=
  (conjugateIsoEquiv Adjunction.id ((𝟭 C).sheafAdjunctionContinuous A J J)).symm
    (sheafPushforwardContinuousId A J).symm

/-- If a continuous functor `u : C ⥤ C` is naturally isomorphic to `𝟭 C`, its sheaf pullback
identifies with the identity functor. -/
noncomputable def sheafPullbackId' {u : C ⥤ C} (e : u ≅ 𝟭 C)
    [u.IsContinuous J J] [(u.sheafPushforwardContinuous A J J).IsRightAdjoint] :
    u.sheafPullback A J J ≅ 𝟭 (Sheaf J A) :=
  sheafPullbackIso A J J e ≪≫ sheafPullbackId A J

/-- If `u : C ⥤ D` and `v : D ⥤ E` admit sheaf pullbacks, so does `u ⋙ v`. -/
lemma isRightAdjoint_sheafPushforwardContinuous_comp (u : C ⥤ D) (v : D ⥤ E)
    [u.IsContinuous J K] [v.IsContinuous K L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint] :
    letI := isContinuous_comp u v J K L
    ((u ⋙ v).sheafPushforwardContinuous A J L).IsRightAdjoint := by
  have := isContinuous_comp u v J K L
  exact (((u.sheafAdjunctionContinuous A J K).comp
    (v.sheafAdjunctionContinuous A K L)).ofNatIsoRight
      (sheafPushforwardContinuousComp u v A J K L)).isRightAdjoint

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
  (conjugateIsoEquiv
    ((u.sheafAdjunctionContinuous A J K).comp (v.sheafAdjunctionContinuous A K L))
    ((u ⋙ v).sheafAdjunctionContinuous A J L)).symm
    (sheafPushforwardContinuousComp u v A J K L)

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

end Functoriality

end CategoryTheory.Functor
