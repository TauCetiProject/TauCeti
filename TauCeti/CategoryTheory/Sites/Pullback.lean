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
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import TauCeti.CategoryTheory.Sites.Continuous

/-!
# Functoriality, exactness, and existence of sheaf pullback

This file develops basic properties of Mathlib's `CategoryTheory.Functor.sheafPullback`:

* **Colimits and additivity**: `isLeftAdjoint_sheafPullback` and `sheafPullback_additive`.
* **Functoriality**: mate transport yields `sheafPullbackId`, `sheafPullbackComp`,
  `sheafPullbackIso`, `sheafPullbackId'`, `sheafPullbackComp'`, and the coherence laws
  `sheafPullback_id_comp`, `sheafPullback_comp_id`, and `sheafPullback_assoc`;
  `sheafAdjunctionContinuous_comp_unit_app` writes the unit of the adjunction for a composite
  through `sheafPullbackComp`.
* **Representables**: for a continuous functor `u : C ⥤ D` between subcanonical sites whose
  sheaf pushforward `u.sheafPushforwardContinuous (Type v) J K` admits a left adjoint
  (so `u.sheafPullback (Type v) J K` exists), `yonedaCompSheafPullbackIso` identifies
  `J.yoneda ⋙ u.sheafPullback (Type v) J K` with `u ⋙ K.yoneda`.
* **Adjoint continuous functors**: an adjunction `adj : F ⊣ G` between continuous functors yields
  `CategoryTheory.Adjunction.sheafPullbackIso : G.sheafPullback A K J ≅
  F.sheafPushforwardContinuous A J K`, and on representable sheaves of sets this reduces to
  `adj.homEquiv`.
* **Existence via essentially small subsites**: `u.sheafPushforwardContinuous A J K` is a right
  adjoint when `C` is `w`-essentially small, `D` is `w`-locally small, `A` has `w`-small colimits,
  and `(D, K)` has weak sheafification, and existence descends along continuous functors whose
  sheaf pushforward is an equivalence.
-/

public section

universe w v

namespace CategoryTheory

open Limits Opposite

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

section Yoneda

variable {C : Type*} [Category.{v} C] {D : Type*} [Category.{v} D]
  (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.Subcanonical] [K.Subcanonical] [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous (Type v) J K).IsRightAdjoint]

private noncomputable def sheafPullbackYonedaCorepresentableBy (X : C) :
    (sheafToPresheaf K (Type v) ⋙
        (evaluation Dᵒᵖ (Type v)).obj (Opposite.op (u.obj X))).CorepresentableBy
      ((u.sheafPullback (Type v) J K).obj (J.yoneda.obj X)) where
  homEquiv {G} :=
    ((u.sheafAdjunctionContinuous (Type v) J K).homEquiv (J.yoneda.obj X) G).trans J.yonedaEquiv
  homEquiv_comp {G G'} g f := by
    -- `(u.sheafPushforwardContinuous ..).obj G` is definitionally `G.obj ⋙ u.op`.
    change J.yonedaEquiv ((u.sheafAdjunctionContinuous (Type v) J K).homEquiv _ _ (f ≫ g)) =
      g.hom.app (Opposite.op (u.obj X))
        (J.yonedaEquiv ((u.sheafAdjunctionContinuous (Type v) J K).homEquiv _ _ f))
    rw [Adjunction.homEquiv_naturality_right, J.yonedaEquiv_comp]
    -- `J.yonedaEquiv_comp` evaluates the pushed-forward morphism via `whiskerLeft u.op`.
    rfl

private noncomputable def yonedaCompCorepresentableBy (X : C) :
    (sheafToPresheaf K (Type v) ⋙
        (evaluation Dᵒᵖ (Type v)).obj (Opposite.op (u.obj X))).CorepresentableBy
      (K.yoneda.obj (u.obj X)) where
  homEquiv {_} := K.yonedaEquiv
  homEquiv_comp {_ _} g f := K.yonedaEquiv_comp f g

private noncomputable def yonedaCompSheafPullbackIsoComponent (X : C) :
    (u.sheafPullback (Type v) J K).obj (J.yoneda.obj X) ≅ K.yoneda.obj (u.obj X) :=
  (sheafPullbackYonedaCorepresentableBy u J K X).uniqueUpToIso
    (yonedaCompCorepresentableBy u K X)

private lemma homEquiv_yonedaCompSheafPullbackIsoComponent_hom (X : C) :
    (u.sheafAdjunctionContinuous (Type v) J K).homEquiv (J.yoneda.obj X)
        (K.yoneda.obj (u.obj X)) (yonedaCompSheafPullbackIsoComponent u J K X).hom =
      (J.yonedaEquiv (F := (u.sheafPushforwardContinuous (Type v) J K).obj
        (K.yoneda.obj (u.obj X)))).symm (𝟙 (u.obj X)) := by
  have h0 : (sheafPullbackYonedaCorepresentableBy u J K X).homEquiv
        (yonedaCompSheafPullbackIsoComponent u J K X).hom =
      (yonedaCompCorepresentableBy u K X).homEquiv (𝟙 (K.yoneda.obj (u.obj X))) := by
    rw [yonedaCompSheafPullbackIsoComponent, Functor.CorepresentableBy.uniqueUpToIso_hom]
    dsimp only [Coyoneda.fullyFaithful_preimage, NatIso.ofComponents_hom_app, unop_op,
      Functor.CorepresentableBy.homEquiv_eq]
    exact Equiv.apply_symm_apply _ _
  -- `(sheafPullbackYonedaCorepresentableBy ..).homEquiv` is `J.yonedaEquiv ∘ adj.homEquiv`.
  refine (Equiv.symm_apply_apply J.yonedaEquiv _).symm.trans ?_
  refine (congrArg J.yonedaEquiv.symm h0).trans ?_
  exact congrArg J.yonedaEquiv.symm (K.yonedaEquiv_apply (𝟙 (K.yoneda.obj (u.obj X))))

/-- When `u : C ⥤ D` is a continuous functor between subcanonical sites such that
`u.sheafPushforwardContinuous (Type v) J K` admits a left adjoint, pulling back a representable
sheaf of sets along `u` commutes with `u`:
`J.yoneda ⋙ u.sheafPullback (Type v) J K ≅ u ⋙ K.yoneda`. -/
def yonedaCompSheafPullbackIso :
    J.yoneda ⋙ u.sheafPullback (Type v) J K ≅ u ⋙ K.yoneda :=
  NatIso.ofComponents (yonedaCompSheafPullbackIsoComponent u J K) fun {X Y} g ↦ by
    dsimp only [Functor.comp_map]
    apply ((u.sheafAdjunctionContinuous (Type v) J K).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    dsimp only [Functor.comp_obj]
    rw [homEquiv_yonedaCompSheafPullbackIsoComponent_hom,
      homEquiv_yonedaCompSheafPullbackIsoComponent_hom]
    have hL := (J.yonedaEquiv_symm_naturality_left g
      ((u.sheafPushforwardContinuous (Type v) J K).obj (K.yoneda.obj (u.obj Y)))
      (𝟙 (u.obj Y))).trans (congrArg J.yonedaEquiv.symm (Category.comp_id (u.map g)))
    have hR := (J.yonedaEquiv_symm_naturality_right X
      ((u.sheafPushforwardContinuous (Type v) J K).map (K.yoneda.map (u.map g)))
      (𝟙 (u.obj X))).trans (congrArg J.yonedaEquiv.symm (Category.id_comp (u.map g)))
    exact hL.trans hR.symm

/-- The forward component of `yonedaCompSheafPullbackIso` is the adjunction transpose of the
identity section at `u.obj X`. -/
@[simp]
lemma yonedaCompSheafPullbackIso_hom_app (X : C) :
    (yonedaCompSheafPullbackIso u J K).hom.app X =
      ((u.sheafAdjunctionContinuous (Type v) J K).homEquiv (J.yoneda.obj X)
        (K.yoneda.obj (u.obj X))).symm
        ((J.yonedaEquiv (F := (u.sheafPushforwardContinuous (Type v) J K).obj
          (K.yoneda.obj (u.obj X)))).symm (𝟙 (u.obj X))) := by
  apply ((u.sheafAdjunctionContinuous (Type v) J K).homEquiv _ _).injective
  dsimp only [yonedaCompSheafPullbackIso, NatIso.ofComponents_hom_app, Functor.comp_obj]
  rw [homEquiv_yonedaCompSheafPullbackIsoComponent_hom, Equiv.apply_symm_apply]

/-- The inverse component of `yonedaCompSheafPullbackIso` classifies the Yoneda-unit section at
`u.obj X`. -/
@[simp]
lemma yonedaCompSheafPullbackIso_inv_app (X : C) :
    (yonedaCompSheafPullbackIso u J K).inv.app X =
      K.yonedaEquiv.symm (J.yonedaEquiv
        ((u.sheafAdjunctionContinuous (Type v) J K).unit.app (J.yoneda.obj X))) := by
  dsimp only [yonedaCompSheafPullbackIso, NatIso.ofComponents_inv_app, Functor.comp_obj,
    yonedaCompSheafPullbackIsoComponent]
  rw [Functor.CorepresentableBy.uniqueUpToIso_inv]
  dsimp only [Coyoneda.fullyFaithful_preimage, NatIso.ofComponents_inv_app, unop_op,
    sheafPullbackYonedaCorepresentableBy, yonedaCompCorepresentableBy, Equiv.trans_apply]
  have hunit : (u.sheafAdjunctionContinuous (Type v) J K).homEquiv (J.yoneda.obj X)
        ((u.sheafPullback (Type v) J K).obj (J.yoneda.obj X))
        (𝟙 ((u.sheafPullback (Type v) J K).obj (J.yoneda.obj X))) =
      (u.sheafAdjunctionContinuous (Type v) J K).unit.app (J.yoneda.obj X) := by
    simp [Adjunction.homEquiv_unit]
  exact congrArg (fun f ↦ K.yonedaEquiv.symm (J.yonedaEquiv f)) hunit

end Yoneda

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

section Yoneda

variable {C' : Type*} [Category.{v} C'] {D' : Type*} [Category.{v} D']
  {F' : C' ⥤ D'} {G' : D' ⥤ C'} (adj' : F' ⊣ G')
  (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
  [J'.Subcanonical] [K'.Subcanonical]
  [hF' : F'.IsContinuous J' K'] [hG' : G'.IsContinuous K' J']
  [(G'.sheafPushforwardContinuous (Type v) K' J').IsRightAdjoint]

omit [J'.Subcanonical] [(G'.sheafPushforwardContinuous (Type v) K' J').IsRightAdjoint] in
include adj' hF' in
private lemma sheafPushforwardContinuous_unit_app_yoneda_hom_app_id (X : D') :
    (((adj'.sheafPushforwardContinuous J' K').unit.app (K'.yoneda.obj X)).hom.app
        (Opposite.op X)) (𝟙 X) =
      adj'.counit.app X := by
  simp only [Functor.comp_obj, Functor.id_obj, GrothendieckTopology.yoneda_obj_obj,
    sheafPushforwardContinuous_unit_app_hom_app, yoneda_obj_map, Quiver.Hom.unop_op, yoneda_obj_obj]
  exact Category.comp_id _

include adj' hF' in
private lemma homEquiv_sheafPullbackIso_inv_comp_yonedaCompSheafPullbackIso_hom (X : D') :
    (adj'.sheafPushforwardContinuous J' K').homEquiv (K'.yoneda.obj X) (J'.yoneda.obj (G'.obj X))
        ((adj'.sheafPullbackIso (Type v) J' K').inv.app (K'.yoneda.obj X) ≫
          (Functor.yonedaCompSheafPullbackIso G' K' J').hom.app X) =
      (K'.yonedaEquiv
        (F := (G'.sheafPushforwardContinuous (Type v) K' J').obj (J'.yoneda.obj (G'.obj X)))).symm
        (𝟙 (G'.obj X)) := by
  let adj₁ := G'.sheafAdjunctionContinuous (Type v) K' J'
  let adj₂ : F'.sheafPushforwardContinuous (Type v) J' K' ⊣
      G'.sheafPushforwardContinuous (Type v) K' J' :=
    adj'.sheafPushforwardContinuous J' K'
  rw [adj₂.homEquiv_unit]
  have hunit := adj'.unit_sheafPullbackIso_hom_app (Type v) J' K' (K'.yoneda.obj X)
  have hG := Functor.map_comp (G'.sheafPushforwardContinuous (Type v) K' J')
    ((adj'.sheafPullbackIso (Type v) J' K').inv.app (K'.yoneda.obj X))
    ((Functor.yonedaCompSheafPullbackIso G' K' J').hom.app X)
  calc adj₂.unit.app (K'.yoneda.obj X) ≫
        (G'.sheafPushforwardContinuous (Type v) K' J').map
          ((adj'.sheafPullbackIso (Type v) J' K').inv.app (K'.yoneda.obj X) ≫
            (Functor.yonedaCompSheafPullbackIso G' K' J').hom.app X)
    _ = (adj₁.unit.app (K'.yoneda.obj X) ≫
          (G'.sheafPushforwardContinuous (Type v) K' J').map
            ((adj'.sheafPullbackIso (Type v) J' K').hom.app (K'.yoneda.obj X))) ≫
          (G'.sheafPushforwardContinuous (Type v) K' J').map
            ((adj'.sheafPullbackIso (Type v) J' K').inv.app (K'.yoneda.obj X)) ≫
          (G'.sheafPushforwardContinuous (Type v) K' J').map
            ((Functor.yonedaCompSheafPullbackIso G' K' J').hom.app X) := by
          rw [hunit, hG]
    _ = adj₁.unit.app (K'.yoneda.obj X) ≫
          (G'.sheafPushforwardContinuous (Type v) K' J').map
            ((Functor.yonedaCompSheafPullbackIso G' K' J').hom.app X) := by
          rw [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id,
            Category.id_comp]
    _ = adj₁.homEquiv _ _ ((Functor.yonedaCompSheafPullbackIso G' K' J').hom.app X) :=
          (adj₁.homEquiv_unit _ _ _).symm
    _ = (K'.yonedaEquiv
          (F := (G'.sheafPushforwardContinuous (Type v) K' J').obj
            (J'.yoneda.obj (G'.obj X)))).symm (𝟙 (G'.obj X)) := by
          dsimp only [adj₁, Functor.comp_obj]
          rw [Functor.yonedaCompSheafPullbackIso_hom_app, Equiv.apply_symm_apply]

omit [(G'.sheafPushforwardContinuous (Type v) K' J').IsRightAdjoint] in
include adj' hF' in
private lemma homEquiv_preimageIso_compYonedaIso_symm_hom (X : D') :
    (adj'.sheafPushforwardContinuous J' K').homEquiv (K'.yoneda.obj X) (J'.yoneda.obj (G'.obj X))
        ((fullyFaithfulSheafToPresheaf J' (Type v)).preimageIso
          (X := (F'.sheafPushforwardContinuous (Type v) J' K').obj (K'.yoneda.obj X))
          (Y := J'.yoneda.obj (G'.obj X))
          (adj'.compYonedaIso.app X).symm).hom =
      (K'.yonedaEquiv
        (F := (G'.sheafPushforwardContinuous (Type v) K' J').obj (J'.yoneda.obj (G'.obj X)))).symm
        (𝟙 (G'.obj X)) := by
  let adj₂ : F'.sheafPushforwardContinuous (Type v) J' K' ⊣
      G'.sheafPushforwardContinuous (Type v) K' J' :=
    adj'.sheafPushforwardContinuous J' K'
  let e : (sheafToPresheaf J' (Type v)).obj
        ((F'.sheafPushforwardContinuous (Type v) J' K').obj (K'.yoneda.obj X)) ≅
      (sheafToPresheaf J' (Type v)).obj (J'.yoneda.obj (G'.obj X)) :=
    (adj'.compYonedaIso.app X).symm
  let φ : (F'.sheafPushforwardContinuous (Type v) J' K').obj (K'.yoneda.obj X) ⟶
      J'.yoneda.obj (G'.obj X) :=
    ((fullyFaithfulSheafToPresheaf J' (Type v)).preimageIso e).hom
  have hφ : φ.hom = e.hom :=
    (fullyFaithfulSheafToPresheaf J' (Type v)).map_preimage e.hom
  apply K'.yonedaEquiv.injective
  refine .trans ?_ (Equiv.apply_symm_apply _ _).symm
  rw [adj₂.homEquiv_unit, K'.yonedaEquiv_comp, K'.yonedaEquiv_apply,
    Functor.sheafPushforwardContinuous_map_hom_app,
    sheafPushforwardContinuous_unit_app_yoneda_hom_app_id adj' J' K' X]
  change (φ.hom.app (Opposite.op (G'.obj X))) (adj'.counit.app X) = 𝟙 (G'.obj X)
  rw [hφ]
  have he : ((adj'.compYonedaIso.app X).inv.app (Opposite.op (G'.obj X))) (adj'.counit.app X) =
      adj'.homEquiv (G'.obj X) X (adj'.counit.app X) := by
    simp [Adjunction.compYonedaIso]
  exact he.trans ((adj'.homEquiv_unit _ _ _).trans (adj'.right_triangle_components X))

include adj' hF' in
private lemma sheafPullbackIso_symm_trans_yonedaCompSheafPullbackIso_eq (X : D') :
    ((adj'.sheafPullbackIso (Type v) J' K').app (K'.yoneda.obj X)).symm ≪≫
        (Functor.yonedaCompSheafPullbackIso G' K' J').app X =
      (fullyFaithfulSheafToPresheaf J' (Type v)).preimageIso
        (X := (F'.sheafPushforwardContinuous (Type v) J' K').obj (K'.yoneda.obj X))
        (Y := J'.yoneda.obj (G'.obj X))
        (adj'.compYonedaIso.app X).symm := by
  -- Both sides represent the same adjunction transpose under `adj'.sheafPushforwardContinuous`.
  refine Iso.ext (((adj'.sheafPushforwardContinuous J' K').homEquiv
    (K'.yoneda.obj X) (J'.yoneda.obj (G'.obj X))).injective ?_)
  exact (homEquiv_sheafPullbackIso_inv_comp_yonedaCompSheafPullbackIso_hom adj' J' K' X).trans
    (homEquiv_preimageIso_compYonedaIso_symm_hom adj' J' K' X).symm

include adj' hF' in
/-- Under `adj' : F' ⊣ G'`, transferring a section of `(F'.sheafPushforwardContinuous ...).obj
(K'.yoneda.obj X)` along `(adj'.sheafPullbackIso (Type v) J' K').inv` and
`(Functor.yonedaCompSheafPullbackIso G' K' J').hom` applies `adj'.homEquiv`. -/
lemma sheafPullbackIso_inv_comp_yonedaCompSheafPullbackIso_hom_app_apply
    (X : D') (W : C') (s : F'.obj W ⟶ X) :
    (((adj'.sheafPullbackIso (Type v) J' K').inv.app (K'.yoneda.obj X) ≫
        (Functor.yonedaCompSheafPullbackIso G' K' J').hom.app X).hom.app (Opposite.op W)) s =
      adj'.homEquiv W X s :=
  congrArg (fun e ↦ (e.hom.hom.app (Opposite.op W)) s)
    (sheafPullbackIso_symm_trans_yonedaCompSheafPullbackIso_eq adj' J' K' X)

include adj' hF' in
/-- Inverse of `sheafPullbackIso_inv_comp_yonedaCompSheafPullbackIso_hom_app_apply`. -/
lemma yonedaCompSheafPullbackIso_inv_comp_sheafPullbackIso_hom_app_apply
    (X : D') (W : C') (t : W ⟶ G'.obj X) :
    (((Functor.yonedaCompSheafPullbackIso G' K' J').inv.app X ≫
        (adj'.sheafPullbackIso (Type v) J' K').hom.app (K'.yoneda.obj X)).hom.app
      (Opposite.op W)) t =
      (adj'.homEquiv W X).symm t :=
  congrArg (fun e ↦ (e.inv.hom.app (Opposite.op W)) t)
    (sheafPullbackIso_symm_trans_yonedaCompSheafPullbackIso_eq adj' J' K' X)

end Yoneda

end

end Adjunction

end CategoryTheory
