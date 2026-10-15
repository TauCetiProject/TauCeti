/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.TorusAction.Basic
public import TauCeti.Geometry.Toric.Algebraic.TorusAction.Internal
public import TauCeti.CategoryTheory.Monoidal.Mod

/-!
# The internal torus action on a fan scheme

The glued torus morphism is an internal action in schemes over `Spec ℂ`. Its associativity
is checked on the affine cone opens, where the coordinate-ring coaction supplies the action
laws through the monoidal spectrum functor. The affine chart inclusions are equivariant.
No regularity or nonemptiness assumption on the fan is needed.

The construction uses `CategoryTheory.Functor.modObjObj` and Mathlib's monoidal `algSpec`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3--1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.3 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj Opposite

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

private noncomputable abbrev torus : Over (Spec (.of ℂ)) :=
  (affineToricScheme Φ.lattice (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ))

private noncomputable abbrev realization : Over (Spec (.of ℂ)) :=
  Over.mk Φ.algebraicRealizationStructureMap

private noncomputable abbrev chart (σ : Φ.cones) : Over (Spec (.of ℂ)) :=
  (Φ.affineToricChart σ).asOver (Spec (.of ℂ))

private noncomputable abbrev chartι (σ : Φ.cones) : chart Φ σ ⟶ realization Φ :=
  Over.homMk (Φ.affineToricChartι σ)
    (Φ.affineToricChartι_comp_algebraicRealizationStructureMap σ)

private noncomputable def action : torus Φ ⊗ realization Φ ⟶ realization Φ :=
  Over.homMk Φ.algebraicRealizationAction
    (Φ.algebraicRealizationAction_comp_algebraicRealizationStructureMap.trans
      pullback.condition.symm)

private theorem tensorChart_hom_ext (T : Over (Spec (.of ℂ))) {Y : Scheme}
    {f g : (T ⊗ realization Φ).left ⟶ Y}
    (H : ∀ σ, (T ◁ chartι Φ σ).left ≫ f = (T ◁ chartι Φ σ).left ≫ g) : f = g := by
  let cover : (T ⊗ realization Φ).left.OpenCover :=
    Φ.affineToricOpenCover.pullback₁ (pullback.snd T.hom _)
  refine cover.hom_ext f g fun σ ↦ ?_
  let e : pullback (pullback.snd T.hom (realization Φ).hom) (Φ.affineToricChartι σ) ≅
      (T ⊗ chart Φ σ).left :=
    pullbackLeftPullbackSndIso _ _ _ ≪≫
      pullback.congrHom rfl (Φ.affineToricChartι_comp_algebraicRealizationStructureMap σ)
  have he : e.hom ≫ (T ◁ chartι Φ σ).left = pullback.fst _ _ := by
    -- Fix the chart's structure-map presentation before applying pullback projection laws.
    change (pullbackLeftPullbackSndIso T.hom Φ.algebraicRealizationStructureMap
        (Φ.affineToricChartι σ) ≪≫ pullback.congrHom rfl
          (Φ.affineToricChartι_comp_algebraicRealizationStructureMap σ)).hom ≫
      pullback.map T.hom
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing Φ.lattice σ.1))))
        T.hom Φ.algebraicRealizationStructureMap (𝟙 _) (Φ.affineToricChartι σ) (𝟙 _)
        (by simp)
        (by simpa using (Φ.affineToricChartι_comp_algebraicRealizationStructureMap σ).symm) =
      pullback.fst _ _
    apply pullback.hom_ext <;> simp [pullback.condition]
  have h := e.hom ≫= H σ
  rw [← Category.assoc, ← Category.assoc, he] at h
  exact h

private theorem chart_equivariant (σ : Φ.cones) :
    letI : (algSpec (CommRingCat.of ℂ)).LaxMonoidal :=
      braidedAlgSpec.toMonoidal.toLaxMonoidal
    letI := affineCoordinateRingCoactionModObj Φ.lattice σ.1
    letI : ModObj (torus Φ) (chart Φ σ) := (algSpec (.of ℂ)).modObjObj
      (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))))
      (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice σ.1)))
    γ[torus Φ, chart Φ σ] ≫ chartι Φ σ = torus Φ ◁ chartι Φ σ ≫ action Φ := by
  let _ : (algSpec (CommRingCat.of ℂ)).LaxMonoidal :=
    braidedAlgSpec.toMonoidal.toLaxMonoidal
  let := affineCoordinateRingCoactionModObj Φ.lattice σ.1
  let _ : ModObj (torus Φ) (chart Φ σ) := (algSpec (.of ℂ)).modObjObj
    (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))))
    (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice σ.1)))
  have hs : γ[torus Φ, chart Φ σ].left = affineToricSchemeAction Φ.lattice σ.1 := by
    have h := congrArg (fun f ↦ f.left) ((algSpec (.of ℂ)).modObjObj_smul
      (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))))
      (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice σ.1))))
    simp only [Over.comp_left, algSpec_map_left, affineCoordinateRingCoactionModObj_smul] at h
    erw [h]
    -- Normalize only the spectrum tensorator and algebra-map carriers at this boundary.
    with_unfolding_all
      change (pullbackSpecIso ℂ (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))
        (affineCoordinateRing Φ.lattice σ.1)).hom ≫
        Spec.map (CommRingCat.ofHom (affineCoordinateRingCoaction Φ.lattice σ.1).toRingHom) = _
    rw [← cancel_epi (pullbackSpecIso ℂ _ _).inv,
      pullbackSpecIso_inv_comp_affineToricSchemeAction]
    simp
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  erw [hs]
  -- Present the chart arrow on its actual scheme carrier after forgetting the base.
  change affineToricSchemeAction Φ.lattice σ.1 ≫ Φ.affineToricChartι σ = _
  have hc : (torus Φ ◁ chartι Φ σ).left = algebraicRealizationActionChartMap σ := by
    exact whiskerLeft_affineToricChartι_asOver_left Φ σ
  rw [hc]
  exact (algebraicRealizationActionChartMap_comp_algebraicRealizationAction σ).symm

private theorem action_one : η[torus Φ] ▷ realization Φ ≫ action Φ =
    (λ_ (realization Φ)).hom := by
  rw [← cancel_epi (λ_ (realization Φ)).inv, Iso.inv_hom_id]
  apply Over.OverMorphism.ext
  have hu : (λ_ (realization Φ)).inv.left ≫ (η[torus Φ] ▷ realization Φ).left =
      Φ.algebraicRealizationUnitSection := by
    have hη : η[torus Φ].left = Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom ℂ
          (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))).toRingHom) :=
      one_spec_asOver_spec_left
    have hf := Over.whiskerRight_left_fst (R := realization Φ) η[torus Φ]
    have hs := Over.whiskerRight_left_snd (R := realization Φ) η[torus Φ]
    have hlf := Over.leftUnitor_inv_left_fst (realization Φ)
    have hls := Over.leftUnitor_inv_left_snd (realization Φ)
    apply pullback.hom_ext
    · erw [Category.assoc, hf, ← Category.assoc, hlf, hη]
      exact Φ.algebraicRealizationUnitSection_comp_fst.symm
    · erw [Category.assoc, hs, hls]
      exact Φ.algebraicRealizationUnitSection_comp_snd.symm
  simp only [Over.comp_left]
  rw [← Category.assoc, hu]
  -- Forgetting the over morphism leaves the original glued action map.
  change Φ.algebraicRealizationUnitSection ≫ Φ.algebraicRealizationAction = 𝟙 _
  exact Φ.algebraicRealizationUnitSection_comp_algebraicRealizationAction

private theorem action_mul : μ[torus Φ] ▷ realization Φ ≫ action Φ =
    (α_ (torus Φ) (torus Φ) (realization Φ)).hom ≫ torus Φ ◁ action Φ ≫ action Φ := by
  apply Over.OverMorphism.ext
  apply tensorChart_hom_ext Φ (torus Φ ⊗ torus Φ)
  intro σ
  let _ : (algSpec (CommRingCat.of ℂ)).LaxMonoidal :=
    braidedAlgSpec.toMonoidal.toLaxMonoidal
  let := affineCoordinateRingCoactionModObj Φ.lattice σ.1
  let _ : ModObj (torus Φ) (chart Φ σ) := (algSpec (.of ℂ)).modObjObj
    (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))))
    (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice σ.1)))
  have h := ModObj.mul_smul_self (torus Φ) (chart Φ σ) =≫ chartι Φ σ
  have he : (torus Φ ⊗ torus Φ) ◁ chartι Φ σ ≫
      (μ[torus Φ] ▷ realization Φ ≫ action Φ) =
        μ[torus Φ] ▷ chart Φ σ ≫ γ[torus Φ, chart Φ σ] ≫ chartι Φ σ := by
    rw [whisker_exchange_assoc, ← chart_equivariant]
  have he' : (torus Φ ⊗ torus Φ) ◁ chartι Φ σ ≫
      ((α_ (torus Φ) (torus Φ) (realization Φ)).hom ≫ torus Φ ◁ action Φ ≫ action Φ) =
        (α_ (torus Φ) (torus Φ) (chart Φ σ)).hom ≫
          torus Φ ◁ γ[torus Φ, chart Φ σ] ≫ γ[torus Φ, chart Φ σ] ≫ chartι Φ σ := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
      ← chart_equivariant, whiskerLeft_comp_assoc, ← chart_equivariant]
  have hc := he.trans (h.trans he'.symm)
  simpa only [Over.comp_left, Category.assoc] using congrArg (fun k ↦ k.left) hc

/-- The dense torus acts on the fan scheme over `Spec ℂ` by the glued affine torus actions. -/
noncomputable instance algebraicRealizationModObj :
    ModObj
      ((affineToricScheme Φ.lattice (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ)))
      (Φ.algebraicRealization.asOver (Spec (.of ℂ))) where
  smul := Φ.algebraicRealizationActionOver
  one_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, algebraicRealizationActionOver_left]
    -- The named over-structure has the same structure-map presentation used by the cover.
    change (η[torus Φ] ▷ realization Φ).left ≫ Φ.algebraicRealizationAction =
      (λ_ (realization Φ)).hom.left
    exact congrArg (fun f ↦ f.left) (action_one Φ)
  mul_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionAssocIso]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, algebraicRealizationActionOver_left]
    have hw : ((affineToricScheme Φ.lattice (⊥ : PointedCone ℝ V)).asOver
        (Spec (.of ℂ)) ◁ Φ.algebraicRealizationActionOver).left =
        (torus Φ ◁ action Φ).left := by
      apply pullback.hom_ext
      · exact (Over.whiskerLeft_left_fst _).trans (Over.whiskerLeft_left_fst _).symm
      · have h₁ := Over.whiskerLeft_left_snd (R := torus Φ)
          Φ.algebraicRealizationActionOver
        have h₂ := Over.whiskerLeft_left_snd (R := torus Φ) (action Φ)
        erw [algebraicRealizationActionOver_left] at h₁
        exact h₁.trans h₂.symm
    rw [hw]
    -- Pin the chosen over-scheme and its iterated tensor-product carriers.
    change (μ[torus Φ] ▷ realization Φ).left ≫ Φ.algebraicRealizationAction =
      (α_ (torus Φ) (torus Φ) (realization Φ)).hom.left ≫
        (torus Φ ◁ action Φ).left ≫ Φ.algebraicRealizationAction
    exact congrArg (fun f ↦ f.left) (action_mul Φ)

/-- The internal action is the existing glued torus morphism over `Spec ℂ`. -/
theorem algebraicRealizationModObj_smul :
    γ[(affineToricScheme Φ.lattice (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ)),
      Φ.algebraicRealization.asOver (Spec (.of ℂ))] = Φ.algebraicRealizationActionOver := (rfl)

/-- The affine chart inclusions intertwine the coaction-induced affine action and the global
torus action, as morphisms of schemes over `Spec ℂ`. -/
theorem isModHom_affineToricChartι (σ : Φ.cones) :
    letI : (algSpec (CommRingCat.of ℂ)).LaxMonoidal :=
      braidedAlgSpec.toMonoidal.toLaxMonoidal
    letI := affineCoordinateRingCoactionModObj Φ.lattice σ.1
    letI : ModObj
      ((affineToricScheme Φ.lattice (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ)))
      ((Φ.affineToricChart σ).asOver (Spec (.of ℂ))) := (algSpec (.of ℂ)).modObjObj
      (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))))
      (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice σ.1)))
    IsModHom
      ((affineToricScheme Φ.lattice (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ)))
      ((Φ.affineToricChartι σ).asOver (Spec (.of ℂ))) := by
  let _ : (algSpec (CommRingCat.of ℂ)).LaxMonoidal :=
    braidedAlgSpec.toMonoidal.toLaxMonoidal
  let := affineCoordinateRingCoactionModObj Φ.lattice σ.1
  let _ : ModObj (torus Φ) (chart Φ σ) := (algSpec (.of ℂ)).modObjObj
    (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V))))
    (op (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice σ.1)))
  constructor
  simp only [selfLeftAction_actionHomRight, algebraicRealizationModObj_smul]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, algebraicRealizationActionOver_left]
  have h := congrArg (fun f ↦ f.left) (chart_equivariant Φ σ)
  -- The over-chart inclusion is the same scheme morphism in both presentations.
  change γ[torus Φ, chart Φ σ].left ≫ Φ.affineToricChartι σ =
    (torus Φ ◁ chartι Φ σ).left ≫ Φ.algebraicRealizationAction
  exact h

end TauCeti.Toric.Fan
