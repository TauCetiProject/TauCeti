/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Triangulation

/-!
# Rotation of triangles in a Frobenius stable category

The cone sequence of a morphism `f : X ⟶ Y` is the conflation

`Y ⟶ cone(f) ⟶ ΣX`.

Its connecting morphism is the negative of the suspension of `f`. Consequently the rotation of
the stable cone triangle of `f` is isomorphic to the stable conflation triangle of this cone
sequence. Since every distinguished stable triangle is isomorphic to a conflation triangle and
every such triangle is isomorphic to a cone triangle, distinguished stable triangles are closed
under forward rotation.

Conversely, a triangle whose rotation is distinguished is itself distinguished. For a conflation
`X ⟶ Y ⟶ Z`, pull the chosen loop conflation `ΩZ ⟶ P(Z) ⟶ Z` back along `Y ⟶ Z`. This gives a
conflation `ΩZ ⟶ W ⟶ Y` whose middle term `W` is stably isomorphic to `X`, because `P(Z)` is
projective. The rotation of its standard triangle is isomorphic to the standard triangle of
`X ⟶ Y ⟶ Z`, through the stable isomorphism `Z ≅ ΣΩZ` given by the connecting map of the loop
conflation. Since rotation is an autoequivalence of the category of triangles, the backward
direction follows.

This is the rotation construction in Happel, *Triangulated Categories in the Representation
Theory of Finite Dimensional Algebras*, Chapter I, Section 2.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.ExactStructure.IsFrobenius

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} (hE : E.IsFrobenius)
  {X Y : C}

/-- The extension from `cone(f)` to the chosen injective for `Y` used to compute the connecting
morphism of the cone sequence. -/
private noncomputable def coneSequenceMiddleMap (f : X ⟶ Y) :
    hE.coneObj f ⟶ hE.suspensionInjective Y :=
  (hE.isPushout_cone f).desc
    (-((hE.suspensionPresentation X).middleMap (hE.suspensionPresentation Y) f))
    (hE.suspensionInflation Y) (by simp)

@[reassoc (attr := simp)]
private theorem coneInclusion_comp_coneSequenceMiddleMap (f : X ⟶ Y) :
    hE.coneInclusion f ≫ hE.coneSequenceMiddleMap f = hE.suspensionInflation Y :=
  (hE.isPushout_cone f).inr_desc _ _ _

@[reassoc]
private theorem coneConnectingMap_comp_neg_cokernelMap (f : X ⟶ Y) :
    hE.coneConnectingMap f ≫
        (-((hE.suspensionPresentation X).cokernelMap (hE.suspensionPresentation Y) f)) =
      hE.coneSequenceMiddleMap f ≫ hE.suspensionDeflation Y := by
  apply (hE.isPushout_cone f).hom_ext
  · simp [coneSequenceMiddleMap, InjectivePresentation.p_comp_cokernelMap]
  · rw [hE.coneInclusion_comp_coneConnectingMap_assoc,
      coneInclusion_comp_coneSequenceMiddleMap_assoc hE,
      (hE.suspensionPresentation Y).zero]
    simp

/-- The connecting morphism of the cone sequence is the negative of the map induced by `f` on
the chosen suspension objects, after passing to the stable category. -/
@[simp]
theorem projectiveStableFunctor_map_connectingMap_coneSequence (f : X ⟶ Y) :
    E.projectiveStableFunctor.map
        (hE.connectingMap (hE.conflation_coneSequence f)) =
      -E.projectiveStableFunctor.map
        ((hE.suspensionPresentation X).cokernelMap (hE.suspensionPresentation Y) f) := by
  let hS := hE.conflation_coneSequence f
  have h := hE.projectiveStableFunctor_map_connectingMap_eq hS
    (hE.coneSequenceMiddleMap f)
    (-((hE.suspensionPresentation X).cokernelMap (hE.suspensionPresentation Y) f))
    (hE.coneInclusion_comp_coneSequenceMiddleMap f)
    (hE.coneConnectingMap_comp_neg_cokernelMap f)
  simpa only [Functor.map_neg] using h

/-- Rotating a stable cone triangle gives the stable conflation triangle of its cone sequence. -/
noncomputable def stableConeTriangleRotateIso (f : X ⟶ Y) :
    letI := hE.stableHasShift
    (hE.stableConeTriangle f).rotate ≅
      hE.stableConflationTriangle (hE.coneSequence f) (hE.conflation_coneSequence f) := by
  letI := hE.stableHasShift
  let q := E.projectiveStableFunctor
  let JX := (hE.stableSuspensionObjIsoShift X).hom
  let JY := (hE.stableSuspensionObjIsoShift Y).hom
  let T₀ : Triangle E.ProjectiveStableCategory := Triangle.mk
    (q.map f)
    (q.map (hE.coneInclusion f))
    (q.map (hE.coneConnectingMap f) ≫ JX)
  let T₁ : Triangle E.ProjectiveStableCategory := Triangle.mk
    (q.map (hE.coneInclusion f))
    (q.map (hE.coneConnectingMap f) ≫ JX)
    (-(q.map f)⟦(1 : ℤ)⟧')
  let T₂ : Triangle E.ProjectiveStableCategory := Triangle.mk
    (q.map (hE.coneInclusion f))
    (q.map (hE.coneConnectingMap f))
    (q.map (hE.connectingMap (hE.conflation_coneSequence f)) ≫ JY)
  have hT₀ : T₀ = hE.stableConeTriangle f := by
    simpa only [T₀, q, JX] using
      (hE.stableConeTriangle_eq_mk f).symm
  have hT₁ : T₁ = (hE.stableConeTriangle f).rotate := by
    -- `Triangle.rotate` has no constructor theorem; `T₁` is its constructor normal form.
    change T₀.rotate = (hE.stableConeTriangle f).rotate
    rw [hT₀]
  have hT₂ : T₂ =
      hE.stableConflationTriangle (hE.coneSequence f) (hE.conflation_coneSequence f) := by
    simpa only [T₂, JY, q, stableSuspensionObjIsoShift_hom] using
      (hE.stableConflationTriangle_eq_mk
        (hE.coneSequence f) (hE.conflation_coneSequence f)).symm
  have hIso : T₁ ≅ T₂ := by
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (hE.stableSuspensionObjIsoShift X).symm ?_ ?_ ?_
    · simp [T₁, T₂]
    · simp [T₁, T₂, JX]
    · dsimp [T₁, T₂, JY]
      rw [hE.projectiveStableFunctor_map_connectingMap_coneSequence]
      simp only [Preadditive.comp_neg, Preadditive.neg_comp]
      rw [hE.stableSuspensionObjIsoShift_hom_naturality]
      simp [q]
  simpa only [hT₁, hT₂] using hIso

/-- The rotation of a stable cone triangle is distinguished. -/
theorem stableConeTriangle_rotate_mem (f : X ⟶ Y) :
    letI := hE.stableHasShift
    (hE.stableConeTriangle f).rotate ∈ hE.stableDistinguishedTriangles := by
  let _ := hE.stableHasShift
  exact hE.stableDistinguishedTriangles_isomorphic
    (hE.stableConflationTriangle_mem (hE.coneSequence f) (hE.conflation_coneSequence f))
    (hE.stableConeTriangleRotateIso f).symm

/-- Distinguished stable triangles are closed under forward rotation. -/
theorem rotate_stable_distinguished_triangle
    (T : (letI := hE.stableHasShift; Triangle E.ProjectiveStableCategory))
    (hT : (letI := hE.stableHasShift; T ∈ hE.stableDistinguishedTriangles)) :
    (letI := hE.stableHasShift; T.rotate ∈ hE.stableDistinguishedTriangles) := by
  let _ := hE.stableHasShift
  obtain ⟨S, hS, ⟨e⟩⟩ := (hE.mem_stableDistinguishedTriangles_iff T).1 hT
  let i := (rotate E.ProjectiveStableCategory).mapIso
    (e.trans (hE.stableConeTriangleIsoStableConflation S hS).symm)
  exact hE.stableDistinguishedTriangles_isomorphic
    (hE.stableConeTriangle_rotate_mem S.f) i.symm

/-! ### Every standard triangle is a rotation -/

section LoopBaseChange

variable {S : ShortComplex C} (hS : E.Conflation S)

/-- The chosen loop conflation `ΩZ ⟶ P(Z) ⟶ Z`, as a short complex. -/
private noncomputable abbrev loopSequence (Z : C) : ShortComplex C :=
  ShortComplex.mk (hE.enoughProjectives.loopInflation Z) (hE.enoughProjectives.loopDeflation Z)
    (hE.enoughProjectives.loopInflation_comp_loopDeflation Z)

/-- A lift `P(Z) ⟶ Y` of the loop deflation along the deflation `Y ⟶ Z`. -/
private noncomputable def loopLift : hE.enoughProjectives.loopProjective S.X₃ ⟶ S.X₂ :=
  (hE.enoughProjectives.isProjective_loopProjective S.X₃).factorThru (E.isDeflation_g hS)
    (hE.enoughProjectives.loopDeflation S.X₃)

@[reassoc (attr := simp)]
private theorem loopLift_comp_g :
    hE.loopLift hS ≫ S.g = hE.enoughProjectives.loopDeflation S.X₃ :=
  isProjective.factorThru_comp _ _ _

/-- The map `ΩZ ⟶ X` induced on kernels by the lift `P(Z) ⟶ Y`. -/
private noncomputable def loopToX₁ : hE.enoughProjectives.loopObj S.X₃ ⟶ S.X₁ :=
  (E.isKernelCokernelPair S hS).lift
    (hE.enoughProjectives.loopInflation S.X₃ ≫ hE.loopLift hS) (by simp)

@[reassoc (attr := simp)]
private theorem loopToX₁_f : hE.loopToX₁ hS ≫ S.f =
    hE.enoughProjectives.loopInflation S.X₃ ≫ hE.loopLift hS :=
  (E.isKernelCokernelPair S hS).lift_f _ _

/-- The morphism from the loop conflation of `Z` to `X ⟶ Y ⟶ Z`, the identity on `Z`. -/
private noncomputable def loopSequenceHom : hE.loopSequence S.X₃ ⟶ S where
  τ₁ := hE.loopToX₁ hS
  τ₂ := hE.loopLift hS
  τ₃ := 𝟙 _
  comm₁₂ := by simp
  comm₂₃ := by simp

/- In the rest of the section, `W` is a pullback of the loop deflation `P(Z) ⟶ Z` along the
deflation `Y ⟶ Z`. -/
variable {W : C} {v : W ⟶ hE.enoughProjectives.loopProjective S.X₃} {w : W ⟶ S.X₂}
  (sq : IsPullback v w (hE.enoughProjectives.loopDeflation S.X₃) S.g)

/-- The base change `ΩZ ⟶ W ⟶ Y` of the loop conflation of `Z` along `Y ⟶ Z`. -/
private noncomputable abbrev loopBaseChange : ShortComplex C :=
  ShortComplex.mk (baseChangeι (hE.loopSequence S.X₃) sq) w (by simp)

private theorem conflation_loopBaseChange : E.Conflation (hE.loopBaseChange sq) := by
  have h := E.conflation_baseChange
    (hE.enoughProjectives.conflation_loopInflation_loopDeflation S.X₃) sq
  rwa [baseChange_def] at h

/-- The morphism from the base-changed conflation to the loop conflation of `Z`. -/
private noncomputable def loopBaseChangeHom :
    hE.loopBaseChange sq ⟶ hE.loopSequence S.X₃ where
  τ₁ := 𝟙 _
  τ₂ := v
  τ₃ := S.g
  comm₁₂ := by simp
  comm₂₃ := sq.w

/-- The map `X ⟶ W` with components `0` and `X ⟶ Y`. -/
private noncomputable def toLoopPullback : S.X₁ ⟶ W :=
  sq.lift 0 S.f (by simp)

@[reassoc (attr := simp)]
private theorem toLoopPullback_fst : hE.toLoopPullback sq ≫ v = 0 :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
private theorem toLoopPullback_snd : hE.toLoopPullback sq ≫ w = S.f :=
  IsPullback.lift_snd _ _ _ _

/-- The section `P(Z) ⟶ W` with components the identity and the chosen lift. -/
private noncomputable def loopPullbackSection :
    hE.enoughProjectives.loopProjective S.X₃ ⟶ W :=
  sq.lift (𝟙 _) (hE.loopLift hS) (by simp)

@[reassoc (attr := simp)]
private theorem loopPullbackSection_fst : hE.loopPullbackSection hS sq ≫ v = 𝟙 _ :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
private theorem loopPullbackSection_snd : hE.loopPullbackSection hS sq ≫ w = hE.loopLift hS :=
  IsPullback.lift_snd _ _ _ _

/-- The retraction `W ⟶ X`, induced by `W ⟶ Y` minus the part through `P(Z)`. -/
private noncomputable def fromLoopPullback : W ⟶ S.X₁ :=
  (E.isKernelCokernelPair S hS).lift (w - v ≫ hE.loopLift hS) (by
    rw [Preadditive.sub_comp, Category.assoc, loopLift_comp_g, ← sq.w, sub_self])

@[reassoc (attr := simp)]
private theorem fromLoopPullback_f :
    hE.fromLoopPullback hS sq ≫ S.f = w - v ≫ hE.loopLift hS :=
  (E.isKernelCokernelPair S hS).lift_f _ _

private theorem toLoopPullback_comp_fromLoopPullback :
    hE.toLoopPullback sq ≫ hE.fromLoopPullback hS sq = 𝟙 _ := by
  have := (E.isKernelCokernelPair S hS).mono_f
  simp [← cancel_mono S.f]

private theorem fromLoopPullback_comp_toLoopPullback :
    hE.fromLoopPullback hS sq ≫ hE.toLoopPullback sq = 𝟙 _ - v ≫ hE.loopPullbackSection hS sq := by
  apply sq.hom_ext <;> simp

include hS in
/-- The map `X ⟶ W` becomes an isomorphism in the stable category. -/
private theorem isIso_projectiveStableFunctor_map_toLoopPullback :
    IsIso (E.projectiveStableFunctor.map (hE.toLoopPullback sq)) := by
  refine ⟨⟨E.projectiveStableFunctor.map (hE.fromLoopPullback hS sq), ?_, ?_⟩⟩
  · rw [← Functor.map_comp, toLoopPullback_comp_fromLoopPullback,
      CategoryTheory.Functor.map_id]
  · rw [← Functor.map_comp, fromLoopPullback_comp_toLoopPullback, Functor.map_sub,
      CategoryTheory.Functor.map_id, sub_eq_self,
      ExactStructure.projectiveStableFunctor_map_eq_zero_iff]
    exact ObjectProperty.factorsThrough_comp _
      (hE.enoughProjectives.isProjective_loopProjective S.X₃) _ _

/-- In the stable category, the inflation `ΩZ ⟶ W` is the negative of `ΩZ ⟶ X ⟶ W`. -/
private theorem projectiveStableFunctor_map_loopBaseChange_f :
    E.projectiveStableFunctor.map (hE.loopBaseChange sq).f =
      -E.projectiveStableFunctor.map (hE.loopToX₁ hS ≫ hE.toLoopPullback sq) := by
  have h : (hE.loopBaseChange sq).f + hE.loopToX₁ hS ≫ hE.toLoopPullback sq =
      hE.enoughProjectives.loopInflation S.X₃ ≫ hE.loopPullbackSection hS sq := by
    apply sq.hom_ext <;> simp
  rw [eq_neg_iff_add_eq_zero, ← Functor.map_add, h,
    ExactStructure.projectiveStableFunctor_map_eq_zero_iff]
  exact ObjectProperty.factorsThrough_comp _
    (hE.enoughProjectives.isProjective_loopProjective S.X₃) _ _

/-- The standard triangle of a conflation `X ⟶ Y ⟶ Z` is isomorphic to the rotation of the
standard triangle of its base change `ΩZ ⟶ W ⟶ Y` of the loop conflation of `Z`. -/
private noncomputable def stableConflationTriangleIsoRotateLoopBaseChange :
    letI := hE.stableHasShift
    hE.stableConflationTriangle S hS ≅
      (hE.stableConflationTriangle (hE.loopBaseChange sq)
        (hE.conflation_loopBaseChange sq)).rotate := by
  letI := hE.stableHasShift
  haveI := hE.stableShiftFunctor_additive 1
  let q := E.projectiveStableFunctor
  let S' := hE.loopBaseChange sq
  let hS' := hE.conflation_loopBaseChange sq
  let Ω := hE.enoughProjectives.loopObj S.X₃
  let J := fun A : C ↦ (hE.stableSuspensionObjIsoShift A).hom
  let T₁ : Triangle E.ProjectiveStableCategory :=
    Triangle.mk (q.map S.f) (q.map S.g) (q.map (hE.connectingMap hS) ≫ J S.X₁)
  let T₂ : Triangle E.ProjectiveStableCategory :=
    Triangle.mk (q.map S'.g) (q.map (hE.connectingMap hS') ≫ J Ω) (-(q.map S'.f)⟦(1 : ℤ)⟧')
  have hT₁ : T₁ = hE.stableConflationTriangle S hS := by
    simpa only [T₁, J, stableSuspensionObjIsoShift_hom] using
      (hE.stableConflationTriangle_eq_mk S hS).symm
  have hT₂ : T₂ = (hE.stableConflationTriangle S' hS').rotate := by
    rw [hE.stableConflationTriangle_eq_mk S' hS']
    simp only [T₂, J, stableSuspensionObjIsoShift_hom]
    -- `Triangle.rotate` has no constructor theorem; `T₂` is its constructor normal form.
    rfl
  -- The connecting maps of the two conflations are compared through the loop conflation.
  have hδ₁ := hE.projectiveStableFunctor_map_connectingMap_naturality
    (hE.enoughProjectives.conflation_loopInflation_loopDeflation S.X₃) hS (hE.loopSequenceHom hS)
  have hδ₂ := hE.projectiveStableFunctor_map_connectingMap_naturality hS'
    (hE.enoughProjectives.conflation_loopInflation_loopDeflation S.X₃) (hE.loopBaseChangeHom sq)
  simp only [loopSequenceHom, loopBaseChangeHom, Category.id_comp, Functor.map_comp,
    E.projectiveStableFunctor_map_cokernelMap_id _
      (hE.isProjective_I (hE.suspensionPresentation _)), Category.comp_id] at hδ₁ hδ₂
  have _ := isIso_projectiveStableFunctor_map_toLoopPullback hE hS sq
  -- The connecting map `Z ⟶ ΣΩZ` of the loop conflation is inverse to `ΣΩZ ≅ Z`.
  have hIso : T₁ ≅ T₂ := by
    refine Triangle.isoMk _ _ (asIso (q.map (hE.toLoopPullback sq))) (Iso.refl _)
      ((hE.suspensionLoopIso S.X₃).symm ≪≫ hE.stableSuspensionObjIsoShift Ω) ?_ ?_ ?_
    · simp [T₁, T₂, S', q, ← Functor.map_comp]
    · simp only [T₁, T₂, Triangle.mk_mor₂, Iso.trans_hom, Iso.symm_hom, suspensionLoopIso_inv,
        Iso.refl_hom, Category.id_comp]
      rw [← hδ₂, Category.assoc]
    · simp only [T₁, T₂, Triangle.mk_mor₃, asIso_hom, Iso.trans_hom, Iso.symm_hom,
        suspensionLoopIso_inv, Category.assoc]
      rw [hE.projectiveStableFunctor_map_loopBaseChange_f hS sq, Functor.map_neg, neg_neg,
        Functor.map_comp, Functor.map_comp,
        ← hE.stableSuspensionObjIsoShift_hom_naturality_assoc, hδ₁]
      simp only [Category.assoc, q, J, Ω]
  simpa only [hT₁, hT₂] using hIso

omit sq in
/-- Every standard triangle of a conflation is isomorphic to the rotation of the standard
triangle of another conflation. -/
private theorem exists_stableConflationTriangle_iso_rotate :
    letI := hE.stableHasShift
    ∃ (S' : ShortComplex C) (hS' : E.Conflation S'),
      Nonempty (hE.stableConflationTriangle S hS ≅
        (hE.stableConflationTriangle S' hS').rotate) := by
  have : HasPullback (hE.enoughProjectives.loopDeflation S.X₃) S.g :=
    E.hasPullbacks_deflations.hasPullback S.g
      (E.isDeflation_g (hE.enoughProjectives.conflation_loopInflation_loopDeflation S.X₃))
  exact ⟨_, _, ⟨hE.stableConflationTriangleIsoRotateLoopBaseChange hS
    (IsPullback.of_hasPullback _ _)⟩⟩

end LoopBaseChange

/-- A triangle whose rotation is a distinguished stable triangle is itself distinguished. -/
theorem mem_stableDistinguishedTriangles_of_rotate_mem
    (T : (letI := hE.stableHasShift; Triangle E.ProjectiveStableCategory))
    (hT : (letI := hE.stableHasShift; T.rotate ∈ hE.stableDistinguishedTriangles)) :
    (letI := hE.stableHasShift; T ∈ hE.stableDistinguishedTriangles) := by
  let := hE.stableHasShift
  have := hE.stableShiftFunctor_additive
  obtain ⟨S, hS, ⟨e⟩⟩ := (hE.mem_stableDistinguishedTriangles_iff _).1 hT
  obtain ⟨S', hS', ⟨e'⟩⟩ := hE.exists_stableConflationTriangle_iso_rotate hS
  exact hE.stableDistinguishedTriangles_isomorphic (hE.stableConflationTriangle_mem S' hS')
    ((rotate E.ProjectiveStableCategory).preimageIso (e ≪≫ e')).symm

/-- A triangle is a distinguished stable triangle exactly when its rotation is. -/
@[simp]
theorem rotate_mem_stableDistinguishedTriangles_iff
    (T : (letI := hE.stableHasShift; Triangle E.ProjectiveStableCategory)) :
    (letI := hE.stableHasShift; T.rotate ∈ hE.stableDistinguishedTriangles) ↔
      (letI := hE.stableHasShift; T ∈ hE.stableDistinguishedTriangles) :=
  ⟨hE.mem_stableDistinguishedTriangles_of_rotate_mem T,
    hE.rotate_stable_distinguished_triangle T⟩

end TauCeti.ExactStructure.IsFrobenius
