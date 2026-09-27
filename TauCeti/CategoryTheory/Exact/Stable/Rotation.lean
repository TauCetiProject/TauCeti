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
@[simp]
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

end TauCeti.ExactStructure.IsFrobenius
