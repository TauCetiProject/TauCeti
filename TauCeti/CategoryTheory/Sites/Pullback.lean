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

This file develops basic properties of Mathlib's `CategoryTheory.Functor.sheafPullback`:

* **Colimits and additivity**: `isLeftAdjoint_sheafPullback` and `sheafPullback_additive`.
* **Functoriality**: mate transport yields `sheafPullbackId`, `sheafPullbackComp`,
  `sheafPullbackIso`, `sheafPullbackId'`, `sheafPullbackComp'`, and the coherence laws
  `sheafPullback_id_comp`, `sheafPullback_comp_id`, and `sheafPullback_assoc`, with
  `sheafPullbackComp'_assoc` and `sheafPullbackComp'_eq_isoWhiskerLeft_sheafPullbackId'` for
  arbitrary composites;
  `sheafAdjunctionContinuous_comp_unit_app` writes the unit of the adjunction for a composite
  through `sheafPullbackComp`.
* **Adjoint continuous functors**: an adjunction `adj : F ⊣ G` between continuous functors yields
  `CategoryTheory.Adjunction.sheafPullbackIso : G.sheafPullback A K J ≅
  F.sheafPushforwardContinuous A J K`.
* **Existence via essentially small subsites**: `u.sheafPushforwardContinuous A J K` is a right
  adjoint when `C` is `w`-essentially small, `D` is `w`-locally small, `A` has `w`-small colimits,
  and `(D, K)` has weak sheafification, and existence descends along continuous functors whose
  sheaf pushforward is an equivalence.
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

section Id

variable (A : Type*) [Category* A] (J : GrothendieckTopology C)

instance isRightAdjoint_sheafPushforwardContinuous_id :
    ((𝟭 C).sheafPushforwardContinuous A J J).IsRightAdjoint :=
  isRightAdjoint_of_iso (sheafPushforwardContinuousId A J).symm

/-- The sheaf pullback along the identity functor identifies with the identity functor. -/
def sheafPullbackId : (𝟭 C).sheafPullback A J J ≅ 𝟭 (Sheaf J A) :=
  ((𝟭 C).sheafAdjunctionContinuous A J J).leftAdjointIdIso (sheafPushforwardContinuousId A J)

@[simp]
lemma conjugateEquiv_sheafPullbackId_hom :
    conjugateEquiv .id ((𝟭 C).sheafAdjunctionContinuous A J J) (sheafPullbackId A J).hom =
      (sheafPushforwardContinuousId A J).inv := by
  simp [sheafPullbackId]

end Id

section Iso

variable {u u' : C ⥤ D} (e : u ≅ u') (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [hu : u.IsContinuous J K] [u'.IsContinuous J K]
  [hRadj : (u.sheafPushforwardContinuous A J K).IsRightAdjoint]

include e hu hRadj in
/-- Existence of the sheaf pullback is invariant under natural isomorphism of continuous
functors. -/
lemma isRightAdjoint_sheafPushforwardContinuous_of_iso :
    (u'.sheafPushforwardContinuous A J K).IsRightAdjoint :=
  isRightAdjoint_of_iso (sheafPushforwardContinuousIso e A J K)

variable [(u'.sheafPushforwardContinuous A J K).IsRightAdjoint]

include e in
/-- Naturally isomorphic continuous functors induce naturally isomorphic sheaf pullbacks. -/
def sheafPullbackIso : u.sheafPullback A J K ≅ u'.sheafPullback A J K :=
  (conjugateIsoEquiv (u'.sheafAdjunctionContinuous A J K)
    (u.sheafAdjunctionContinuous A J K)).symm (sheafPushforwardContinuousIso e.symm A J K)

@[simp]
lemma conjugateEquiv_sheafPullbackIso_hom :
    conjugateEquiv (u'.sheafAdjunctionContinuous A J K) (u.sheafAdjunctionContinuous A J K)
      (sheafPullbackIso e A J K).hom = (sheafPushforwardContinuousIso e.symm A J K).hom := by
  simp [sheafPullbackIso]

@[simp]
lemma conjugateEquiv_sheafPullbackIso_inv :
    conjugateEquiv (u.sheafAdjunctionContinuous A J K) (u'.sheafAdjunctionContinuous A J K)
      (sheafPullbackIso e A J K).inv = (sheafPushforwardContinuousIso e.symm A J K).inv := by
  simp [sheafPullbackIso]

end Iso

section Id'

variable {u₀ : C ⥤ C} (e : u₀ ≅ 𝟭 C) (A : Type*) [Category* A] (J : GrothendieckTopology C)
  [u₀.IsContinuous J J] [(u₀.sheafPushforwardContinuous A J J).IsRightAdjoint]

include e in
/-- If a continuous endofunctor is naturally isomorphic to the identity, so is its sheaf
pullback. -/
def sheafPullbackId' : u₀.sheafPullback A J J ≅ 𝟭 (Sheaf J A) :=
  (u₀.sheafAdjunctionContinuous A J J).leftAdjointIdIso (sheafPushforwardContinuousId' e A J)

@[simp]
lemma conjugateEquiv_sheafPullbackId'_hom :
    conjugateEquiv .id (u₀.sheafAdjunctionContinuous A J J) (sheafPullbackId' e A J).hom =
      (sheafPushforwardContinuousId' e A J).inv := by
  simp [sheafPullbackId']

end Id'

section Comp

variable (u : C ⥤ D) (v : D ⥤ E) (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  [u.IsContinuous J K] [v.IsContinuous K L]
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [(v.sheafPushforwardContinuous A K L).IsRightAdjoint]

/-- Continuous functors admitting sheaf pullbacks compose to one admitting a sheaf pullback. -/
lemma isRightAdjoint_sheafPushforwardContinuous_comp :
    let := isContinuous_comp u v J K L
    ((u ⋙ v).sheafPushforwardContinuous A J L).IsRightAdjoint :=
  let := isContinuous_comp u v J K L
  isRightAdjoint_of_iso (sheafPushforwardContinuousComp u v A J K L)

/-- The composition of two sheaf pullbacks identifies with the sheaf pullback of the composite
functor. -/
def sheafPullbackComp :
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
lemma conjugateEquiv_sheafPullbackComp_inv :
    let := isContinuous_comp u v J K L
    have := isRightAdjoint_sheafPushforwardContinuous_comp u v A J K L
    conjugateEquiv ((u.sheafAdjunctionContinuous A J K).comp (v.sheafAdjunctionContinuous A K L))
      ((u ⋙ v).sheafAdjunctionContinuous A J L) (sheafPullbackComp u v A J K L).inv =
      (sheafPushforwardContinuousComp u v A J K L).hom := by
  let := isContinuous_comp u v J K L
  have := isRightAdjoint_sheafPushforwardContinuous_comp u v A J K L
  simp [sheafPullbackComp]

/-- The unit of `(u ⋙ v)^* ⊣ (u ⋙ v)_*` is the unit of `u^* ⊣ u_*`, followed by the unit of
`v^* ⊣ v_*` and the isomorphism `v^* u^* ≅ (u ⋙ v)^*` of `sheafPullbackComp`. -/
lemma sheafAdjunctionContinuous_comp_unit_app (G : Sheaf J A) :
    let := isContinuous_comp u v J K L
    have := isRightAdjoint_sheafPushforwardContinuous_comp u v A J K L
    ((u ⋙ v).sheafAdjunctionContinuous A J L).unit.app G =
      (u.sheafAdjunctionContinuous A J K).unit.app G ≫
        (u.sheafPushforwardContinuous A J K).map
          ((v.sheafAdjunctionContinuous A K L).unit.app _ ≫
            (v.sheafPushforwardContinuous A K L).map
              ((sheafPullbackComp u v A J K L).hom.app G)) := by
  intro _ _
  have h := unit_conjugateEquiv ((u.sheafAdjunctionContinuous A J K).comp
    (v.sheafAdjunctionContinuous A K L)) ((u ⋙ v).sheafAdjunctionContinuous A J L)
    (sheafPullbackComp u v A J K L).inv G
  rw [conjugateEquiv_sheafPullbackComp_inv, Adjunction.comp_unit_app] at h
  -- The isomorphism of pushforwards in `sheafPullbackComp` is the identity.
  have h' := congrArg (· ≫ ((u ⋙ v).sheafPushforwardContinuous A J L).map
    ((sheafPullbackComp u v A J K L).hom.app G)) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id] at h'
  refine (Category.comp_id _).symm.trans (h'.symm.trans ?_)
  rw [Functor.map_comp]
  simp only [sheafPushforwardContinuousComp, Iso.refl_hom, NatTrans.id_app]
  exact congrArg (fun φ ↦ _ ≫ _ ≫ φ) (Category.id_comp _)

end Comp

section Coherence

variable (u : C ⥤ D) (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsContinuous J K] [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]

@[simp]
lemma sheafPullbackIso_refl : sheafPullbackIso (Iso.refl u) A J K = Iso.refl _ := by
  refine Iso.ext ((conjugateEquiv (u.sheafAdjunctionContinuous A J K)
    (u.sheafAdjunctionContinuous A J K)).injective ?_)
  ext F X
  simp only [conjugateEquiv_sheafPullbackIso_hom, Iso.refl_symm,
    sheafPushforwardContinuousIso_hom, sheafPushforwardContinuousNatTrans_app_hom,
    Iso.refl_inv, NatTrans.op_id, whiskerRight_id', Iso.refl_hom, conjugateEquiv_id,
    NatTrans.id_app]
  rfl

/-- Left-unit coherence for `sheafPullbackComp (𝟭 C) u`, `sheafPullbackId`, and `leftUnitor`. -/
lemma sheafPullback_id_comp :
    sheafPullbackComp (𝟭 C) u A J J K =
      Functor.isoWhiskerRight (sheafPullbackId A J) (u.sheafPullback A J K) ≪≫
        Functor.leftUnitor (u.sheafPullback A J K) :=
  Adjunction.leftAdjointCompIso_id_comp _ _ _ _ (by
    ext : 3
    simp only [comp_obj, Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app, id_obj,
      whiskerLeft_app, rightUnitor_hom_app, Category.comp_id]
    rfl)

/-- Right-unit coherence for `sheafPullbackComp u (𝟭 D)`, `sheafPullbackId`, and `rightUnitor`. -/
lemma sheafPullback_comp_id :
    sheafPullbackComp u (𝟭 D) A J K K =
      Functor.isoWhiskerLeft (u.sheafPullback A J K) (sheafPullbackId A K) ≪≫
        Functor.rightUnitor (u.sheafPullback A J K) :=
  Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (by
    ext : 3
    simp only [comp_obj, Iso.trans_hom, isoWhiskerRight_hom, NatTrans.comp_app, id_obj,
      whiskerRight_app, leftUnitor_hom_app, Category.comp_id]
    exact (Functor.map_id _ _).symm)

end Coherence

/-- Associativity coherence for `sheafPullbackComp` with respect to `Functor.associator`. -/
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

section Comp'

variable {u : C ⥤ D} {v : D ⥤ E} {uv : C ⥤ E} (e : u ⋙ v ≅ uv) (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  [u.IsContinuous J K] [v.IsContinuous K L] [uv.IsContinuous J L]
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [(v.sheafPushforwardContinuous A K L).IsRightAdjoint]
  [(uv.sheafPushforwardContinuous A J L).IsRightAdjoint]

include e in
/-- When `u ⋙ v ≅ uv` is an isomorphism of continuous functors, the composite of the sheaf
pullbacks along `u` and `v` identifies with the sheaf pullback along `uv`. -/
def sheafPullbackComp' :
    u.sheafPullback A J K ⋙ v.sheafPullback A K L ≅ uv.sheafPullback A J L :=
  Adjunction.leftAdjointCompIso
    (u.sheafAdjunctionContinuous A J K) (v.sheafAdjunctionContinuous A K L)
    (uv.sheafAdjunctionContinuous A J L)
    (sheafPushforwardContinuousComp' e A J K L)

@[simp]
lemma conjugateEquiv_sheafPullbackComp'_inv :
    conjugateEquiv ((u.sheafAdjunctionContinuous A J K).comp (v.sheafAdjunctionContinuous A K L))
      (uv.sheafAdjunctionContinuous A J L) (sheafPullbackComp' e A J K L).inv =
      (sheafPushforwardContinuousComp' e A J K L).hom := by
  simp [sheafPullbackComp']

end Comp'

/-- Associativity coherence for `sheafPullbackComp'` along arbitrary composites: if the two
isomorphisms `u ⋙ v ⋙ w ≅ uvw` built from `e₁₂, e₁₃` and from `e₂₃, e₀` agree, so do the two
isomorphisms `u^* ⋙ v^* ⋙ w^* ≅ uvw^*` built from the corresponding `sheafPullbackComp'`. -/
lemma sheafPullbackComp'_assoc {E' : Type*} [Category* E']
    {u : C ⥤ D} {v : D ⥤ E} {w : E ⥤ E'} {uv : C ⥤ E} {vw : D ⥤ E'} {uvw : C ⥤ E'}
    (e₁₂ : u ⋙ v ≅ uv) (e₂₃ : v ⋙ w ≅ vw) (e₁₃ : uv ⋙ w ≅ uvw) (e₀ : u ⋙ vw ≅ uvw)
    (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (M : GrothendieckTopology E')
    [u.IsContinuous J K] [v.IsContinuous K L] [w.IsContinuous L M]
    [uv.IsContinuous J L] [vw.IsContinuous K M] [uvw.IsContinuous J M]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K L).IsRightAdjoint]
    [(w.sheafPushforwardContinuous A L M).IsRightAdjoint]
    [(uv.sheafPushforwardContinuous A J L).IsRightAdjoint]
    [(vw.sheafPushforwardContinuous A K M).IsRightAdjoint]
    [(uvw.sheafPushforwardContinuous A J M).IsRightAdjoint]
    (h : ∀ X : C,
      e₁₃.inv.app X ≫ w.map (e₁₂.inv.app X) = e₀.inv.app X ≫ e₂₃.inv.app (u.obj X)) :
    isoWhiskerLeft (u.sheafPullback A J K) (sheafPullbackComp' e₂₃ A K L M) ≪≫
        sheafPullbackComp' e₀ A J K M =
      (associator _ _ _).symm ≪≫
        isoWhiskerRight (sheafPullbackComp' e₁₂ A J K L) (w.sheafPullback A L M) ≪≫
          sheafPullbackComp' e₁₃ A J L M :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (by
    ext F X
    simp only [comp_obj, Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app,
      ObjectProperty.FullSubcategory.comp_hom, sheafPushforwardContinuousComp'_hom_app_hom_app,
      sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op, Iso.symm_hom,
      isoWhiskerRight_hom, associator_inv_app, whiskerRight_app, Category.id_comp,
      sheafPushforwardContinuous_map_hom_app]
    have h' := congrArg (fun f ↦ F.obj.map f.op) (h X.unop)
    simp only [op_comp, Functor.map_comp] at h'
    exact h')

/-- Right-unit coherence for `sheafPullbackComp'`: if `e : u ⋙ v ≅ u` is induced by an
isomorphism `e' : v ≅ 𝟭 D`, then `sheafPullbackComp' e` is induced by `sheafPullbackId' e'`. -/
lemma sheafPullbackComp'_eq_isoWhiskerLeft_sheafPullbackId' {u : C ⥤ D} {v : D ⥤ D}
    (e : u ⋙ v ≅ u) (e' : v ≅ 𝟭 D) (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [v.IsContinuous K K]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K K).IsRightAdjoint]
    (h : ∀ X : C, e.inv.app X ≫ e'.hom.app (u.obj X) = 𝟙 _) :
    sheafPullbackComp' e A J K K =
      isoWhiskerLeft (u.sheafPullback A J K) (sheafPullbackId' e' A K) ≪≫ rightUnitor _ :=
  Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (by
    ext F X
    simp only [comp_obj, sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.trans_hom,
      isoWhiskerRight_hom, NatTrans.comp_app, id_obj, whiskerRight_app, leftUnitor_hom_app,
      Category.comp_id, sheafPushforwardContinuous_map_hom_app,
      sheafPushforwardContinuousId'_hom_app_hom_app]
    rw [(Iso.comp_hom_eq_id (e'.app _)).mp (h X.unop), Iso.app_inv])

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

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G) (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [hF : F.IsContinuous J K] [G.IsContinuous K J]

include adj hF in
/-- When `F ⊣ G` is an adjunction between continuous functors, `G.sheafPushforwardContinuous A K J`
is a right adjoint. -/
lemma isRightAdjoint_sheafPushforwardContinuous :
    (G.sheafPushforwardContinuous A K J).IsRightAdjoint :=
  (adj.sheafPushforwardContinuous J K :
    F.sheafPushforwardContinuous A J K ⊣ G.sheafPushforwardContinuous A K J).isRightAdjoint

variable [(G.sheafPushforwardContinuous A K J).IsRightAdjoint]

include adj in
/-- When `F ⊣ G` is an adjunction between continuous functors, the sheaf pullback along `G` is
naturally isomorphic to the sheaf pushforward along `F`. -/
def sheafPullbackIso : G.sheafPullback A K J ≅ F.sheafPushforwardContinuous A J K :=
  leftAdjointUniq (G.sheafAdjunctionContinuous A K J) (adj.sheafPushforwardContinuous J K)

@[reassoc (attr := simp)]
lemma unit_sheafPullbackIso_hom :
    (G.sheafAdjunctionContinuous A K J).unit ≫
      Functor.whiskerRight (adj.sheafPullbackIso A J K).hom (G.sheafPushforwardContinuous A K J) =
      (adj.sheafPushforwardContinuous J K).unit :=
  unit_leftAdjointUniq_hom _ _

@[reassoc (attr := simp)]
lemma unit_sheafPullbackIso_hom_app (X : Sheaf K A) :
    (G.sheafAdjunctionContinuous A K J).unit.app X ≫
        (G.sheafPushforwardContinuous A K J).map ((adj.sheafPullbackIso A J K).hom.app X) =
      (adj.sheafPushforwardContinuous J K).unit.app X :=
  unit_leftAdjointUniq_hom_app _ _ X

@[reassoc (attr := simp)]
lemma sheafPullbackIso_hom_counit :
    Functor.whiskerLeft (G.sheafPushforwardContinuous A K J) (adj.sheafPullbackIso A J K).hom ≫
      (adj.sheafPushforwardContinuous J K).counit =
      (G.sheafAdjunctionContinuous A K J).counit :=
  leftAdjointUniq_hom_counit _ _

@[reassoc (attr := simp)]
lemma sheafPullbackIso_hom_app_counit (Y : Sheaf J A) :
    (adj.sheafPullbackIso A J K).hom.app ((G.sheafPushforwardContinuous A K J).obj Y) ≫
        (adj.sheafPushforwardContinuous J K).counit.app Y =
      (G.sheafAdjunctionContinuous A K J).counit.app Y :=
  leftAdjointUniq_hom_app_counit _ _ Y

end

end Adjunction

end CategoryTheory
