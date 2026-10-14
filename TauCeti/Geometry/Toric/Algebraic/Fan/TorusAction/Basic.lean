/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over
public import TauCeti.Geometry.Toric.Algebraic.TorusAction.Scheme

/-!
# The torus action on the toric scheme of a fan

The dense torus `T = Spec ℂ[M]` of the integral character lattice `M` acts on every affine toric
chart `U_σ = Spec ℂ[σ^∨ ∩ M]` through the character-grading coaction, and these affine actions
commute with restriction to faces (`TauCeti.Toric.affineToricSchemeActionFaceMap_comp_action`).
This file glues them to an action `T ×_{Spec ℂ} X_Φ ⟶ X_Φ` on the toric scheme `X_Φ` of a finite
fan `Φ`. No regularity is required.

The fibre product `T ×_{Spec ℂ} X_Φ` is covered by the open subschemes `T ×_{Spec ℂ} U_σ`. The
affine toric open cover of `X_Φ` is locally directed, so its pullback along the projection
`T ×_{Spec ℂ} X_Φ ⟶ X_Φ` is a locally directed open cover as well, and morphisms out of
`T ×_{Spec ℂ} X_Φ` glue as soon as they are compatible with the face maps
(`AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOfLocallyDirected`).

## Main declarations

* `TauCeti.Toric.Fan.algebraicRealizationAction`: the torus action on the toric scheme of a fan.
* `TauCeti.Toric.Fan.algebraicRealizationActionChartMap_comp_algebraicRealizationAction`: on
  `T ×_{Spec ℂ} U_σ`, it is the affine torus action followed by the chart inclusion.
* `TauCeti.Toric.Fan.algebraicRealizationActionChartMap_hom_ext`: morphisms out of
  `T ×_{Spec ℂ} X_Φ` are determined on the charts `T ×_{Spec ℂ} U_σ`.
* `TauCeti.Toric.Fan.algebraicRealizationAction_comp_algebraicRealizationStructureMap`: the action
  is a morphism over `Spec ℂ`.
* `TauCeti.Toric.Fan.algebraicRealizationUnitSection_comp_algebraicRealizationAction`: the
  identity of the torus acts trivially.
* `TauCeti.Toric.Fan.algebraicRealizationActionChartMap_comp_algebraicRealizationAction_bot`: on
  the dense torus itself, the action is the multiplication of the torus.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3--1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.3 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-! ### The global torus action -/

variable {Φ}

/-- The product of the dense torus with the affine chart of a cone maps into the product of the
dense torus with the toric scheme, by the identity on the torus factor and the chart inclusion on
the other factor. -/
noncomputable def algebraicRealizationActionChartMap (σ : Φ.cones) :
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing Φ.lattice σ.1)))) ⟶
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)))))
      Φ.algebraicRealizationStructureMap :=
  pullback.map _ _ _ _ (𝟙 _) (Φ.affineToricChartι σ) (𝟙 _) (by simp)
    (by simp [affineToricChartι_comp_algebraicRealizationStructureMap])

/-- The product chart map is the identity on the torus factor. -/
@[reassoc (attr := simp)]
theorem algebraicRealizationActionChartMap_comp_fst (σ : Φ.cones) :
    algebraicRealizationActionChartMap σ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [algebraicRealizationActionChartMap]

/-- The product chart map is the chart inclusion on the toric-scheme factor. -/
@[reassoc (attr := simp)]
theorem algebraicRealizationActionChartMap_comp_snd (σ : Φ.cones) :
    algebraicRealizationActionChartMap σ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Φ.affineToricChartι σ := by
  simp [algebraicRealizationActionChartMap]

variable (Φ) in
/-- The pullback of the affine toric open cover to the product of the dense torus with the toric
scheme. Its member indexed by `σ` is isomorphic to the product of the dense torus with the chart of
`σ`, through `actionCoverRestriction`. -/
private noncomputable abbrev actionCover :
    (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)))))
      Φ.algebraicRealizationStructureMap).OpenCover :=
  Φ.affineToricOpenCover.pullback₁ (pullback.snd _ _)

private noncomputable def actionCoverRestriction (σ : Φ.cones) :
    pullback
        (pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap ℂ
            (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)))))
          Φ.algebraicRealizationStructureMap)
        (Φ.affineToricChartι σ) ≅
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ
          (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing Φ.lattice σ.1)))) :=
  pullbackLeftPullbackSndIso _ _ _ ≪≫
    pullback.congrHom rfl (Φ.affineToricChartι_comp_algebraicRealizationStructureMap σ)

@[reassoc]
private theorem map_actionCoverRestriction {τ σ : Φ.cones} (h : τ.1.IsFaceOf σ.1) :
    pullback.map (pullback.snd _ _) (Φ.affineToricChartι τ) (pullback.snd _ _)
        (Φ.affineToricChartι σ) (𝟙 _) (faceAffineToricSchemeMap Φ.lattice h) (𝟙 _)
        (by simp) (by simp) ≫ (actionCoverRestriction σ).hom =
      (actionCoverRestriction τ).hom ≫ affineToricSchemeActionFaceMap Φ.lattice σ.1 h := by
  apply pullback.hom_ext <;> simp [actionCoverRestriction]

private noncomputable def actionOnCover (σ : Φ.cones) :
    pullback
        (pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap ℂ
            (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)))))
          Φ.algebraicRealizationStructureMap)
        (Φ.affineToricChartι σ) ⟶ Φ.algebraicRealization :=
  (actionCoverRestriction σ).hom ≫ affineToricSchemeAction Φ.lattice σ.1 ≫ Φ.affineToricChartι σ

variable (Φ) in
private theorem actionCover_f (σ : Φ.cones) :
    (actionCover Φ).f σ = pullback.fst (pullback.snd _ _) (Φ.affineToricChartι σ) :=
  rfl

variable (Φ) in
private theorem actionCover_trans {τ σ : Φ.cones} (h : τ ⟶ σ) :
    (actionCover Φ).trans h =
      pullback.map (pullback.snd _ _) (Φ.affineToricChartι τ) (pullback.snd _ _)
        (Φ.affineToricChartι σ) (𝟙 _)
        (faceAffineToricSchemeMap Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom h))) (𝟙 _)
        (by simp) (by simp) :=
  rfl

private theorem trans_comp_actionOnCover {τ σ : Φ.cones} (h : τ ⟶ σ) :
    (actionCover Φ).trans h ≫ actionOnCover σ = actionOnCover τ := by
  rw [actionCover_trans, actionOnCover, actionOnCover]
  exact (map_actionCoverRestriction_assoc _ _).trans <| by
    rw [affineToricSchemeActionFaceMap_comp_action_assoc,
      faceAffineToricSchemeMap_comp_affineToricChartι]

variable (Φ) in
/-- The action of the dense torus on the toric scheme of a fan, glued from the affine torus
actions on the affine toric charts. -/
noncomputable def algebraicRealizationAction :
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)))))
      Φ.algebraicRealizationStructureMap ⟶ Φ.algebraicRealization :=
  (actionCover Φ).glueMorphismsOfLocallyDirected actionOnCover trans_comp_actionOnCover

private theorem fst_comp_algebraicRealizationAction (σ : Φ.cones) :
    pullback.fst (pullback.snd _ _) (Φ.affineToricChartι σ) ≫ Φ.algebraicRealizationAction =
      (actionCoverRestriction σ).hom ≫ affineToricSchemeAction Φ.lattice σ.1 ≫
        Φ.affineToricChartι σ :=
  (actionCover Φ).map_glueMorphismsOfLocallyDirected actionOnCover trans_comp_actionOnCover σ

@[reassoc]
private theorem actionCoverRestriction_comp_algebraicRealizationActionChartMap (σ : Φ.cones) :
    (actionCoverRestriction σ).hom ≫ algebraicRealizationActionChartMap σ =
      pullback.fst (pullback.snd _ _) (Φ.affineToricChartι σ) := by
  apply pullback.hom_ext
  · simp [actionCoverRestriction]
  · simp [actionCoverRestriction, pullback.condition]

/-- On the product of the dense torus with an affine chart, the torus action on the toric scheme
of a fan is the affine torus action followed by the chart inclusion. -/
@[reassoc (attr := simp)]
theorem algebraicRealizationActionChartMap_comp_algebraicRealizationAction (σ : Φ.cones) :
    algebraicRealizationActionChartMap σ ≫ Φ.algebraicRealizationAction =
      affineToricSchemeAction Φ.lattice σ.1 ≫ Φ.affineToricChartι σ := by
  rw [← cancel_epi (actionCoverRestriction σ).hom,
    actionCoverRestriction_comp_algebraicRealizationActionChartMap_assoc,
    fst_comp_algebraicRealizationAction]

/-- Morphisms out of the product of the dense torus with the toric scheme of a fan are determined
by their restrictions to the products of the dense torus with the affine charts. -/
theorem algebraicRealizationActionChartMap_hom_ext {Y : Scheme}
    {g h : pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)))))
      Φ.algebraicRealizationStructureMap ⟶ Y}
    (H : ∀ σ, algebraicRealizationActionChartMap σ ≫ g = algebraicRealizationActionChartMap σ ≫ h) :
    g = h := by
  refine (actionCover Φ).hom_ext g h fun (σ : Φ.cones) ↦ ?_
  have hσ := (actionCoverRestriction σ).hom ≫= H σ
  simp only [actionCoverRestriction_comp_algebraicRealizationActionChartMap_assoc] at hσ
  rw [actionCover_f]
  exact hσ

/-- Restricting the product of the dense torus with an affine chart to a face is compatible with
the inclusions into the product of the dense torus with the toric scheme. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeActionFaceMap_comp_algebraicRealizationActionChartMap
    {τ σ : Φ.cones} (h : τ.1.IsFaceOf σ.1) :
    affineToricSchemeActionFaceMap Φ.lattice σ.1 h ≫ algebraicRealizationActionChartMap σ =
      algebraicRealizationActionChartMap τ := by
  apply pullback.hom_ext <;> simp

variable (Φ)

/-- The torus action on the toric scheme of a fan is a morphism over `Spec ℂ`. -/
@[reassoc]
theorem algebraicRealizationAction_comp_algebraicRealizationStructureMap :
    Φ.algebraicRealizationAction ≫ Φ.algebraicRealizationStructureMap =
      pullback.snd _ _ ≫ Φ.algebraicRealizationStructureMap := by
  refine algebraicRealizationActionChartMap_hom_ext fun σ ↦ ?_
  simp [affineToricChartι_comp_algebraicRealizationStructureMap,
    affineToricSchemeAction_comp_specMap_algebraMap]

/-- The glued torus action as a morphism of schemes over `Spec ℂ`. -/
noncomputable def algebraicRealizationActionOver :
    (affineToricScheme Φ.lattice (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ)) ⊗
      Φ.algebraicRealization.asOver (Spec (.of ℂ)) ⟶
        Φ.algebraicRealization.asOver (Spec (.of ℂ)) := by
  let f : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ
      (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))))) ⊗
        Over.mk Φ.algebraicRealizationStructureMap ⟶
          Over.mk Φ.algebraicRealizationStructureMap :=
    Over.homMk Φ.algebraicRealizationAction
      (Φ.algebraicRealizationAction_comp_algebraicRealizationStructureMap.trans
        pullback.condition.symm)
  simpa only [OverClass.asOver, algebraicRealization_over, specOverSpec_over] using f

/-- Forgetting the base from the action over `Spec ℂ` gives the glued action morphism. -/
theorem algebraicRealizationActionOver_left :
    Φ.algebraicRealizationActionOver.left = Φ.algebraicRealizationAction := (rfl)

/-- Tensoring a chart inclusion with the identity on the torus gives the product chart map. -/
theorem whiskerLeft_affineToricChartι_asOver_left (σ : Φ.cones) :
    ((affineToricScheme Φ.lattice (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ)) ◁
      (Φ.affineToricChartι σ).asOver (Spec (.of ℂ))).left =
        algebraicRealizationActionChartMap σ := (rfl)

/-- The section of the projection from the product of the dense torus with the toric scheme of a
fan, given by the identity point of the dense torus. -/
noncomputable def algebraicRealizationUnitSection :
    Φ.algebraicRealization ⟶
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ
          (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)))))
        Φ.algebraicRealizationStructureMap :=
  pullback.lift
    (Φ.algebraicRealizationStructureMap ≫ Spec.map (CommRingCat.ofHom
      (Bialgebra.counitAlgHom ℂ
        (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))).toRingHom))
    (𝟙 _) (by
      have h : (Bialgebra.counitAlgHom ℂ
          (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))).toRingHom.comp
            (algebraMap ℂ _) = RingHom.id ℂ :=
        (Bialgebra.counitAlgHom ℂ _).comp_algebraMap
      rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
      simp)

/-- The torus component of the unit section is the identity point of the dense torus. -/
@[reassoc (attr := simp)]
theorem algebraicRealizationUnitSection_comp_fst :
    Φ.algebraicRealizationUnitSection ≫ pullback.fst _ _ =
      Φ.algebraicRealizationStructureMap ≫ Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom ℂ
          (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))).toRingHom) :=
  pullback.lift_fst ..

/-- The unit section is a section of the projection to the toric scheme. -/
@[reassoc (attr := simp)]
theorem algebraicRealizationUnitSection_comp_snd :
    Φ.algebraicRealizationUnitSection ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd ..

/-- On an affine chart, the unit section of the toric scheme is the unit section of the chart. -/
@[reassoc (attr := simp)]
theorem affineToricChartι_comp_algebraicRealizationUnitSection (σ : Φ.cones) :
    Φ.affineToricChartι σ ≫ Φ.algebraicRealizationUnitSection =
      affineToricSchemeUnitSection Φ.lattice σ.1 ≫ algebraicRealizationActionChartMap σ := by
  apply pullback.hom_ext
  · simp [affineToricChartι_comp_algebraicRealizationStructureMap_assoc]
  · simp

/-- The identity element of the dense torus acts trivially on the toric scheme of a fan. -/
@[reassoc (attr := simp)]
theorem algebraicRealizationUnitSection_comp_algebraicRealizationAction :
    Φ.algebraicRealizationUnitSection ≫ Φ.algebraicRealizationAction = 𝟙 _ := by
  ext σ
  simp

/-- On the chart of the zero cone, the dense torus, the torus action on the toric scheme of a fan
is the multiplication of the dense torus. -/
theorem algebraicRealizationActionChartMap_comp_algebraicRealizationAction_bot
    (h : ⊥ ∈ Φ.cones) :
    algebraicRealizationActionChartMap ⟨⊥, h⟩ ≫ Φ.algebraicRealizationAction =
      μ[((affineToricScheme Φ.lattice (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ)))].left ≫
        Φ.affineToricChartι ⟨⊥, h⟩ := by
  rw [algebraicRealizationActionChartMap_comp_algebraicRealizationAction]
  exact congrArg (· ≫ Φ.affineToricChartι ⟨⊥, h⟩) (affineToricSchemeAction_bot Φ.lattice)

end TauCeti.Toric.Fan
