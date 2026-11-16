/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Sites.Continuous

/-!
# Functoriality, exactness, and existence of sheaf pullback

Mathlib's `CategoryTheory.Functor.sheafPullback` is the left adjoint of the pushforward of sheaves
`u.sheafPushforwardContinuous A J K` along a continuous functor `u : C ⥤ D`, when this left adjoint
exists.

This file develops the basic properties of `sheafPullback`:

* **Colimits and additivity**: `u.sheafPullback A J K` is registered as `IsLeftAdjoint`
  (`isLeftAdjoint_sheafPullback`), so Mathlib's adjunction instances automatically synthesize
  `PreservesColimitsOfSize`, `PreservesColimitsOfShape`, and `PreservesFiniteColimits`, and it is
  additive whenever `A` is preadditive.
* **Functoriality**: from the identity, composition, and natural isomorphism compatibilities of
  `sheafPushforwardContinuous`, mate transport produces `sheafPullbackId`, `sheafPullbackComp`,
  `sheafPullbackIso`, `sheafPullbackId'`, and `sheafPullbackComp'`, together with the
  pseudofunctor coherence laws `sheafPullback_id_comp`, `sheafPullback_comp_id`, and
  `sheafPullback_assoc`.
* **Adjoint continuous functors**: when `adj : F ⊣ G` is an adjunction between continuous functors,
  `G.sheafPullback A K J` is naturally isomorphic to `F.sheafPushforwardContinuous A J K`
  (`CategoryTheory.Adjunction.sheafPullbackIso`), since `adj.sheafPushforwardContinuous J K` already
  exhibits `F.sheafPushforwardContinuous A J K` as left adjoint to
  `G.sheafPushforwardContinuous A K J`.
* **Existence via essentially small subsites**: when `C` is `w`-essentially small, `D` is
  `w`-locally small, `A` has `w`-small colimits, and `(D, K)` has weak sheafification in `A`,
  pointwise left Kan extensions along `u.op` exist and supply `(u.sheafPushforwardContinuous A J
  K).IsRightAdjoint`. More generally, if `H : C₀ ⥤ C` is a continuous functor whose sheaf
  pushforward is an equivalence (such as the inclusion of an essentially small dense subsite like
  the affine étale site), existence of the sheaf pullback along `H ⋙ u` descends to `u`.
-/

public section

universe w

namespace CategoryTheory

open Limits

namespace Functor

noncomputable section

section Exactness

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  (u : C ⥤ D) [u.IsContinuous J K]
  {A : Type*} [Category* A] [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- The pullback of sheaves along a continuous functor is a left adjoint (in particular it
preserves colimits of any size and finite colimits). -/
instance isLeftAdjoint_sheafPullback : (u.sheafPullback A J K).IsLeftAdjoint :=
  (u.sheafAdjunctionContinuous A J K).isLeftAdjoint

/-- The pullback of sheaves along a continuous functor into a preadditive category is additive. -/
instance sheafPullback_additive [Preadditive A] : (u.sheafPullback A J K).Additive :=
  (u.sheafAdjunctionContinuous A J K).left_adjoint_additive

end Exactness

section Functoriality

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]

instance isRightAdjoint_sheafPushforwardContinuous_id
    (A : Type*) [Category* A] (J : GrothendieckTopology C) :
    ((𝟭 C).sheafPushforwardContinuous A J J).IsRightAdjoint :=
  isRightAdjoint_of_iso (sheafPushforwardContinuousId A J).symm

/-- The sheaf pullback along the identity functor identifies with the identity functor. -/
def sheafPullbackId (A : Type*) [Category* A] (J : GrothendieckTopology C) :
    (𝟭 C).sheafPullback A J J ≅ 𝟭 (Sheaf J A) :=
  ((𝟭 C).sheafAdjunctionContinuous A J J).leftAdjointIdIso (sheafPushforwardContinuousId A J)

@[simp]
lemma conjugateEquiv_sheafPullbackId_hom (A : Type*) [Category* A] (J : GrothendieckTopology C) :
    conjugateEquiv .id ((𝟭 C).sheafAdjunctionContinuous A J J) (sheafPullbackId A J).hom =
      (sheafPushforwardContinuousId A J).inv := by
  simp [sheafPullbackId]

/-- Existence of the sheaf pullback is invariant under natural isomorphism of continuous
functors. -/
lemma isRightAdjoint_sheafPushforwardContinuous_of_iso {u u' : C ⥤ D} (e : u ≅ u')
    (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [u'.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    (u'.sheafPushforwardContinuous A J K).IsRightAdjoint :=
  isRightAdjoint_of_iso (sheafPushforwardContinuousIso e A J K)

/-- Naturally isomorphic continuous functors induce naturally isomorphic sheaf pullbacks. -/
def sheafPullbackIso {u u' : C ⥤ D} (e : u ≅ u')
    (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [u'.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u'.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    u.sheafPullback A J K ≅ u'.sheafPullback A J K :=
  (conjugateIsoEquiv (u'.sheafAdjunctionContinuous A J K)
    (u.sheafAdjunctionContinuous A J K)).symm (sheafPushforwardContinuousIso e.symm A J K)

@[simp]
lemma conjugateEquiv_sheafPullbackIso_hom {u u' : C ⥤ D} (e : u ≅ u')
    (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [u'.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u'.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    conjugateEquiv (u'.sheafAdjunctionContinuous A J K) (u.sheafAdjunctionContinuous A J K)
      (sheafPullbackIso e A J K).hom = (sheafPushforwardContinuousIso e.symm A J K).hom := by
  simp [sheafPullbackIso]

@[simp]
lemma conjugateEquiv_sheafPullbackIso_inv {u u' : C ⥤ D} (e : u ≅ u')
    (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [u'.IsContinuous J K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u'.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    conjugateEquiv (u.sheafAdjunctionContinuous A J K) (u'.sheafAdjunctionContinuous A J K)
      (sheafPullbackIso e A J K).inv = (sheafPushforwardContinuousIso e.symm A J K).inv := by
  simp [sheafPullbackIso]

@[simp]
lemma sheafPullbackIso_refl (u : C ⥤ D) (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [(u.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    sheafPullbackIso (Iso.refl u) A J K = Iso.refl _ := by
  apply Iso.ext
  apply (conjugateEquiv (u.sheafAdjunctionContinuous A J K)
    (u.sheafAdjunctionContinuous A J K)).injective
  ext F X
  simp only [conjugateEquiv_sheafPullbackIso_hom, Iso.refl_symm,
    sheafPushforwardContinuousIso_hom, sheafPushforwardContinuousNatTrans_app_hom,
    Iso.refl_inv, NatTrans.op_id, whiskerRight_id', Iso.refl_hom, conjugateEquiv_id,
    NatTrans.id_app]
  rfl

/-- If a continuous endofunctor is naturally isomorphic to the identity, so is its sheaf
pullback. -/
def sheafPullbackId' {u₀ : C ⥤ C} (e : u₀ ≅ 𝟭 C)
    (A : Type*) [Category* A] (J : GrothendieckTopology C)
    [u₀.IsContinuous J J] [(u₀.sheafPushforwardContinuous A J J).IsRightAdjoint] :
    u₀.sheafPullback A J J ≅ 𝟭 (Sheaf J A) :=
  (u₀.sheafAdjunctionContinuous A J J).leftAdjointIdIso (sheafPushforwardContinuousId' e A J)

@[simp]
lemma conjugateEquiv_sheafPullbackId'_hom {u₀ : C ⥤ C} (e : u₀ ≅ 𝟭 C)
    (A : Type*) [Category* A] (J : GrothendieckTopology C)
    [u₀.IsContinuous J J] [(u₀.sheafPushforwardContinuous A J J).IsRightAdjoint] :
    conjugateEquiv .id (u₀.sheafAdjunctionContinuous A J J) (sheafPullbackId' e A J).hom =
      (sheafPushforwardContinuousId' e A J).inv := by
  simp [sheafPullbackId']

lemma isRightAdjoint_sheafPushforwardContinuous_comp (u : C ⥤ D) (v : D ⥤ E)
    (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [u.IsContinuous J K] [v.IsContinuous K L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint] :
    let := isContinuous_comp u v J K L
    ((u ⋙ v).sheafPushforwardContinuous A J L).IsRightAdjoint :=
  let := isContinuous_comp u v J K L
  isRightAdjoint_of_iso (sheafPushforwardContinuousComp u v A J K L)

/-- The composition of two sheaf pullbacks identifies with the sheaf pullback of the composite
functor. -/
def sheafPullbackComp (u : C ⥤ D) (v : D ⥤ E)
    (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [u.IsContinuous J K] [v.IsContinuous K L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint] :
    letI := isContinuous_comp u v J K L
    haveI := isRightAdjoint_sheafPushforwardContinuous_comp u v A J K L
    u.sheafPullback A J K ⋙ v.sheafPullback A K L ≅ (u ⋙ v).sheafPullback A J L :=
  letI := isContinuous_comp u v J K L
  haveI := isRightAdjoint_sheafPushforwardContinuous_comp u v A J K L
  Adjunction.leftAdjointCompIso
    (u.sheafAdjunctionContinuous A J K) (v.sheafAdjunctionContinuous A K L)
    ((u ⋙ v).sheafAdjunctionContinuous A J L)
    (sheafPushforwardContinuousComp u v A J K L)

@[simp]
lemma conjugateEquiv_sheafPullbackComp_inv (u : C ⥤ D) (v : D ⥤ E)
    (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [u.IsContinuous J K] [v.IsContinuous K L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint] :
    let := isContinuous_comp u v J K L
    have := isRightAdjoint_sheafPushforwardContinuous_comp u v A J K L
    conjugateEquiv ((u.sheafAdjunctionContinuous A J K).comp (v.sheafAdjunctionContinuous A K L))
      ((u ⋙ v).sheafAdjunctionContinuous A J L) (sheafPullbackComp u v A J K L).inv =
      (sheafPushforwardContinuousComp u v A J K L).hom := by
  let := isContinuous_comp u v J K L
  have := isRightAdjoint_sheafPushforwardContinuous_comp u v A J K L
  simp [sheafPullbackComp]

lemma sheafPullback_id_comp (u : C ⥤ D) (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [(u.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    sheafPullbackComp (𝟭 C) u A J J K =
      Functor.isoWhiskerRight (sheafPullbackId A J) (u.sheafPullback A J K) ≪≫
        Functor.leftUnitor (u.sheafPullback A J K) :=
  Adjunction.leftAdjointCompIso_id_comp _ _ _ _ (by
    ext : 3
    simp only [comp_obj, Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app, id_obj,
      whiskerLeft_app, rightUnitor_hom_app, Category.comp_id]
    rfl)

lemma sheafPullback_comp_id (u : C ⥤ D) (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [(u.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    sheafPullbackComp u (𝟭 D) A J K K =
      Functor.isoWhiskerLeft (u.sheafPullback A J K) (sheafPullbackId A K) ≪≫
        Functor.rightUnitor (u.sheafPullback A J K) :=
  Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (by
    ext : 3
    simp only [comp_obj, Iso.trans_hom, isoWhiskerRight_hom, NatTrans.comp_app, id_obj,
      whiskerRight_app, leftUnitor_hom_app, Category.comp_id]
    exact (Functor.map_id _ _).symm)

lemma sheafPullback_assoc {E' : Type*} [Category* E']
    (u : C ⥤ D) (v : D ⥤ E) (w : E ⥤ E') (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (M : GrothendieckTopology E')
    [u.IsContinuous J K] [v.IsContinuous K L] [w.IsContinuous L M]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint]
    [(w.sheafPushforwardContinuous A L M).IsRightAdjoint] :
    let := isContinuous_comp u v J K L
    let := isContinuous_comp v w K L M
    let := isContinuous_comp u (v ⋙ w) J K M
    have := isRightAdjoint_sheafPushforwardContinuous_comp u v A J K L
    have := isRightAdjoint_sheafPushforwardContinuous_comp v w A K L M
    Functor.isoWhiskerLeft (u.sheafPullback A J K) (sheafPullbackComp v w A K L M) ≪≫
        sheafPullbackComp u (v ⋙ w) A J K M =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (sheafPullbackComp u v A J K L) (w.sheafPullback A L M) ≪≫
          sheafPullbackComp (u ⋙ v) w A J L M := by
  let := isContinuous_comp u v J K L
  let := isContinuous_comp v w K L M
  let := isContinuous_comp u (v ⋙ w) J K M
  have := isRightAdjoint_sheafPushforwardContinuous_comp u v A J K L
  have := isRightAdjoint_sheafPushforwardContinuous_comp v w A K L M
  exact Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (by
    ext : 3
    simp only [comp_obj, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom,
      NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_inv_app, Category.id_comp]
    exact (congrArg (· ≫ _) (Functor.map_id _ _)).symm)

/-- When `u ⋙ v ≅ uv` is an isomorphism of continuous functors, the composite of the sheaf
pullbacks along `u` and `v` identifies with the sheaf pullback along `uv`. -/
def sheafPullbackComp' {u : C ⥤ D} {v : D ⥤ E} {uv : C ⥤ E} (e : u ⋙ v ≅ uv)
    (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [u.IsContinuous J K] [v.IsContinuous K L] [uv.IsContinuous J L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint]
    [(uv.sheafPushforwardContinuous A J L).IsRightAdjoint] :
    u.sheafPullback A J K ⋙ v.sheafPullback A K L ≅ uv.sheafPullback A J L :=
  Adjunction.leftAdjointCompIso
    (u.sheafAdjunctionContinuous A J K) (v.sheafAdjunctionContinuous A K L)
    (uv.sheafAdjunctionContinuous A J L)
    (sheafPushforwardContinuousComp' e A J K L)

@[simp]
lemma conjugateEquiv_sheafPullbackComp'_inv {u : C ⥤ D} {v : D ⥤ E} {uv : C ⥤ E} (e : u ⋙ v ≅ uv)
    (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [u.IsContinuous J K] [v.IsContinuous K L] [uv.IsContinuous J L]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint]
    [(uv.sheafPushforwardContinuous A J L).IsRightAdjoint] :
    conjugateEquiv ((u.sheafAdjunctionContinuous A J K).comp (v.sheafAdjunctionContinuous A K L))
      (uv.sheafAdjunctionContinuous A J L) (sheafPullbackComp' e A J K L).inv =
      (sheafPushforwardContinuousComp' e A J K L).hom := by
  simp [sheafPullbackComp']

end Functoriality

section Existence

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  (u : C ⥤ D) (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [u.IsContinuous J K]

/-- If `C` is `w`-essentially small, `D` is `w`-locally small, `A` has `w`-small colimits, and
`(D, K)` admits weak sheafification in `A`, then `u.sheafPushforwardContinuous A J K` is a right
adjoint. -/
lemma isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall
    [EssentiallySmall.{w} C] [LocallySmall.{w} D]
    [HasColimitsOfSize.{w, w} A] [HasWeakSheafify K A] :
    (u.sheafPushforwardContinuous A J K).IsRightAdjoint := by
  have (F : Cᵒᵖ ⥤ A) : u.op.HasPointwiseLeftKanExtension F := fun Y ↦ by
    have := hasColimitsOfShape_of_essentiallySmall.{w} (CostructuredArrow u.op Y) A
    infer_instance
  infer_instance

/-- If `H : C₀ ⥤ C` is a continuous functor whose sheaf pushforward is an equivalence, and the
composite `H ⋙ u` admits a sheaf pullback, then `u` also admits a sheaf pullback. -/
lemma isRightAdjoint_sheafPushforwardContinuous_of_isEquivalence
    {C₀ : Type*} [Category* C₀] (J₀ : GrothendieckTopology C₀)
    (H : C₀ ⥤ C) [H.IsContinuous J₀ J]
    [(H.sheafPushforwardContinuous A J₀ J).IsEquivalence]
    [(H ⋙ u).IsContinuous J₀ K]
    [((H ⋙ u).sheafPushforwardContinuous A J₀ K).IsRightAdjoint] :
    (u.sheafPushforwardContinuous A J K).IsRightAdjoint :=
  (isRightAdjoint_comp_iff_left (u.sheafPushforwardContinuous A J K)
    (H.sheafPushforwardContinuous A J₀ J)).mp
    (isRightAdjoint_of_iso (sheafPushforwardContinuousComp H u A J₀ J K).symm)

end Existence

end

end Functor

namespace Adjunction

noncomputable section

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- When `F ⊣ G` is an adjunction between continuous functors, `G.sheafPushforwardContinuous A K J`
is a right adjoint. -/
lemma isRightAdjoint_sheafPushforwardContinuous (adj : F ⊣ G)
    (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [G.IsContinuous K J] :
    (G.sheafPushforwardContinuous A K J).IsRightAdjoint :=
  (adj.sheafPushforwardContinuous J K :
    F.sheafPushforwardContinuous A J K ⊣ G.sheafPushforwardContinuous A K J).isRightAdjoint

variable (adj : F ⊣ G) (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [G.IsContinuous K J]

/-- When `F ⊣ G` is an adjunction between continuous functors, the sheaf pullback along `G` is
naturally isomorphic to the sheaf pushforward along `F`. -/
def sheafPullbackIso [(G.sheafPushforwardContinuous A K J).IsRightAdjoint] :
    G.sheafPullback A K J ≅ F.sheafPushforwardContinuous A J K :=
  leftAdjointUniq (G.sheafAdjunctionContinuous A K J) (adj.sheafPushforwardContinuous J K)

@[reassoc (attr := simp)]
lemma unit_sheafPullbackIso_hom [(G.sheafPushforwardContinuous A K J).IsRightAdjoint] :
    (G.sheafAdjunctionContinuous A K J).unit ≫
      Functor.whiskerRight (adj.sheafPullbackIso A J K).hom (G.sheafPushforwardContinuous A K J) =
      (adj.sheafPushforwardContinuous J K).unit :=
  unit_leftAdjointUniq_hom _ _

@[reassoc (attr := simp)]
lemma unit_sheafPullbackIso_hom_app [(G.sheafPushforwardContinuous A K J).IsRightAdjoint]
    (X : Sheaf K A) :
    (G.sheafAdjunctionContinuous A K J).unit.app X ≫
        (G.sheafPushforwardContinuous A K J).map ((adj.sheafPullbackIso A J K).hom.app X) =
      (adj.sheafPushforwardContinuous J K).unit.app X :=
  unit_leftAdjointUniq_hom_app _ _ X

@[reassoc (attr := simp)]
lemma sheafPullbackIso_hom_counit [(G.sheafPushforwardContinuous A K J).IsRightAdjoint] :
    Functor.whiskerLeft (G.sheafPushforwardContinuous A K J) (adj.sheafPullbackIso A J K).hom ≫
      (adj.sheafPushforwardContinuous J K).counit =
      (G.sheafAdjunctionContinuous A K J).counit :=
  leftAdjointUniq_hom_counit _ _

@[reassoc (attr := simp)]
lemma sheafPullbackIso_hom_app_counit [(G.sheafPushforwardContinuous A K J).IsRightAdjoint]
    (Y : Sheaf J A) :
    (adj.sheafPullbackIso A J K).hom.app ((G.sheafPushforwardContinuous A K J).obj Y) ≫
        (adj.sheafPushforwardContinuous J K).counit.app Y =
      (G.sheafAdjunctionContinuous A K J).counit.app Y :=
  leftAdjointUniq_hom_app_counit _ _ Y

end

end Adjunction

end CategoryTheory
