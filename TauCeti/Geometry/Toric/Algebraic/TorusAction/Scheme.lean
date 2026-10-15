/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.TorusAction.Coaction
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The affine toric scheme action map

The grading coaction of an affine toric coordinate ring gives a morphism from the product of
the dense torus and the affine toric scheme to the affine toric scheme. The product is the fibre
product over `Spec ℂ`, identified with the spectrum of the tensor product of coordinate rings.
This is the affine action map that the global fan-scheme action glues along face opens.
Compatible maps of lattice cones induce maps between the two action domains and intertwine
the affine actions.

The defining equation on the tensor-product affine chart keeps the construction tied to the
coordinate-ring coaction, whose counit, coassociativity, and face-compatibility laws are proved
in `Coaction`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2--1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj
open scoped TensorProduct

namespace TauCeti.Toric

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (hi : IsIntegralLattice i) (σ : PointedCone ℝ V)

/-- The affine toric scheme action induced by the character-grading coaction. The dense torus
acts on the affine chart via the common base `Spec ℂ`. -/
noncomputable def affineToricSchemeAction :
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ)))) ⟶
        affineToricScheme hi σ :=
  (pullbackSpecIso ℂ
    (affineCoordinateRing hi (⊥ : PointedCone ℝ V))
    (affineCoordinateRing hi σ)).hom ≫
      Spec.map (CommRingCat.ofHom (affineCoordinateRingCoaction hi σ).toRingHom)

/-- On the tensor-product affine chart, the scheme action is `Spec` of the toric coaction. -/
@[reassoc (attr := simp)]
theorem pullbackSpecIso_inv_comp_affineToricSchemeAction :
    (pullbackSpecIso ℂ
      (affineCoordinateRing hi (⊥ : PointedCone ℝ V))
      (affineCoordinateRing hi σ)).inv ≫ affineToricSchemeAction hi σ =
        Spec.map (CommRingCat.ofHom (affineCoordinateRingCoaction hi σ).toRingHom) := by
  simp [affineToricSchemeAction]

/-- The affine torus action is a morphism over `Spec ℂ`: it commutes with the projections of its
source and target to `Spec ℂ`. -/
@[reassoc]
theorem affineToricSchemeAction_comp_specMap_algebraMap :
    affineToricSchemeAction hi σ ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ))) =
      pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ))) := by
  rw [← cancel_epi (pullbackSpecIso ℂ _ _).inv]
  simp [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    (affineCoordinateRingCoaction hi σ).comp_algebraMap]

/-! ### Naturality -/

private theorem mapsTo_bot
    {N' : Type} {V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (f : N →+ N') (g : V →ₗ[ℝ] V') (_hfg : ∀ n, g (i n) = i' (f n)) :
    Set.MapsTo g (⊥ : PointedCone ℝ V) (⊥ : PointedCone ℝ V') := by
  simp [Set.MapsTo]

/-- A compatible map of lattice cones induces the product map from the source torus action
domain to the target torus action domain.  Its two factors are the induced dense-torus map and
the induced affine toric morphism. -/
noncomputable def affineToricSchemeActionMap
    {N' : Type} {V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (hi' : IsIntegralLattice i') {τ : PointedCone ℝ V'}
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ
          (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ)))) ⟶
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ
          (affineCoordinateRing hi' (⊥ : PointedCone ℝ V')))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi' τ)))) :=
  pullback.map _ _ _ _
    (affineToricSchemeMap hi hi' f g hfg (mapsTo_bot f g hfg))
    (affineToricSchemeMap hi hi' f g hfg hστ) (𝟙 _)
    (by
      rw [Category.comp_id, affineToricSchemeMap_def]
      exact (comp_over (Spec.map (CommRingCat.ofHom
        (affineCoordinateRingMap hi hi' f g hfg
          (mapsTo_bot f g hfg)).toRingHom)) (Spec (.of ℂ))).symm)
    (by
      rw [Category.comp_id, affineToricSchemeMap_def]
      exact (comp_over (Spec.map (CommRingCat.ofHom
        (affineCoordinateRingMap hi hi' f g hfg hστ).toRingHom)) (Spec (.of ℂ))).symm)

/-- The product map on action domains has the induced dense-torus map as its first projection. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeActionMap_comp_fst
    {N' : Type} {V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (hi' : IsIntegralLattice i') {τ : PointedCone ℝ V'}
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) :
    affineToricSchemeActionMap hi σ hi' f g hfg hστ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫
        affineToricSchemeMap hi hi' f g hfg (by simp [Set.MapsTo]) := by
  simp [affineToricSchemeActionMap]

/-- The product map on action domains has the induced affine toric morphism as its second
projection. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeActionMap_comp_snd
    {N' : Type} {V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (hi' : IsIntegralLattice i') {τ : PointedCone ℝ V'}
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) :
    affineToricSchemeActionMap hi σ hi' f g hfg hστ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ affineToricSchemeMap hi hi' f g hfg hστ := by
  simp [affineToricSchemeActionMap]

/-- Affine toric morphisms intertwine the dense-torus actions induced by their lattice maps. -/
@[reassoc]
theorem affineToricSchemeActionMap_comp_action
    {N' : Type} {V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (hi' : IsIntegralLattice i') {τ : PointedCone ℝ V'}
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) :
    affineToricSchemeActionMap hi σ hi' f g hfg hστ ≫
        affineToricSchemeAction hi' τ =
      affineToricSchemeAction hi σ ≫ affineToricSchemeMap hi hi' f g hfg hστ := by
  rw [← cancel_epi (pullbackSpecIso ℂ _ _).inv]
  have hmap :
      (pullbackSpecIso ℂ (affineCoordinateRing hi ⊥)
          (affineCoordinateRing hi σ)).inv ≫
          affineToricSchemeActionMap hi σ hi' f g hfg hστ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
          (affineCoordinateRingMap hi hi' f g hfg
            (mapsTo_bot f g hfg))
          (affineCoordinateRingMap hi hi' f g hfg hστ)).toRingHom) ≫
          (pullbackSpecIso ℂ (affineCoordinateRing hi' ⊥)
            (affineCoordinateRing hi' τ)).inv := by
    apply pullback.hom_ext
    · rw [Category.assoc, affineToricSchemeActionMap_comp_fst]
      rw [← Category.assoc, pullbackSpecIso_inv_fst]
      rw [Category.assoc, pullbackSpecIso_inv_fst]
      simp only [affineToricSchemeMap_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      simp
    · rw [Category.assoc, affineToricSchemeActionMap_comp_snd]
      rw [← Category.assoc, pullbackSpecIso_inv_snd]
      rw [Category.assoc, pullbackSpecIso_inv_snd]
      simp only [affineToricSchemeMap_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      simp
  rw [← Category.assoc, hmap, Category.assoc,
    pullbackSpecIso_inv_comp_affineToricSchemeAction]
  rw [← Category.assoc, pullbackSpecIso_inv_comp_affineToricSchemeAction]
  rw [affineToricSchemeMap_def]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k.toRingHom))
    (affineCoordinateRingCoaction_comp_map hi hi' f g hfg hστ).symm

/-- For the zero cone, the affine action is multiplication of the dense torus scheme. -/
theorem affineToricSchemeAction_bot :
    affineToricSchemeAction hi (⊥ : PointedCone ℝ V) =
      μ[((affineToricScheme hi (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ)))].left := by
  rw [affineToricSchemeAction, mul_spec_asOver_spec_left,
    affineCoordinateRingCoaction_bot]
  rfl

/-- The unit of the dense torus, paired with the identity of the affine chart, defines a
section of the torus-times-chart projection. -/
noncomputable def affineToricSchemeUnitSection :
    affineToricScheme hi σ ⟶
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ
          (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ)))) :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ))) ≫
      η[((affineToricScheme hi (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ)))].left)
    (𝟙 _) (by
      have hη :
          η[((affineToricScheme hi (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ)))].left =
            Spec.map (CommRingCat.ofHom
              (Bialgebra.counitAlgHom ℂ
                (affineCoordinateRing hi (⊥ : PointedCone ℝ V))).toRingHom) :=
        one_spec_asOver_spec_left
      rw [hη, Category.assoc]
      simp [← Spec.map_comp, ← CommRingCat.ofHom_comp])

/-- The unit section has the identity as its projection to the affine chart. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeUnitSection_comp_snd :
    affineToricSchemeUnitSection hi σ ≫ pullback.snd _ _ = 𝟙 _ := by
  simp [affineToricSchemeUnitSection]

/-- The projection of the unit section to the dense torus is the identity section after the
structure map to `Spec ℂ`. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeUnitSection_comp_fst :
    affineToricSchemeUnitSection hi σ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ))) ≫
        Spec.map (CommRingCat.ofHom
          (Bialgebra.counitAlgHom ℂ
            (affineCoordinateRing hi (⊥ : PointedCone ℝ V))).toRingHom) := by
  rw [affineToricSchemeUnitSection, pullback.lift_fst]
  exact congrArg (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ))) ≫ ·)
    (one_spec_asOver_spec_left)

/-- The identity element of the dense torus acts trivially on an affine toric scheme. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeUnitSection_comp_action :
    affineToricSchemeUnitSection hi σ ≫ affineToricSchemeAction hi σ = 𝟙 _ := by
  let e : affineCoordinateRing hi (⊥ : PointedCone ℝ V) ⊗[ℂ]
      affineCoordinateRing hi σ →ₐ[ℂ] affineCoordinateRing hi σ :=
    (Algebra.TensorProduct.lid ℂ (affineCoordinateRing hi σ)).toAlgHom.comp
      (Algebra.TensorProduct.map
        (Bialgebra.counitAlgHom ℂ
          (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))
        (AlgHom.id ℂ (affineCoordinateRing hi σ)))
  have hsection : affineToricSchemeUnitSection hi σ =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        (pullbackSpecIso ℂ (affineCoordinateRing hi ⊥)
          (affineCoordinateRing hi σ)).inv := by
    apply pullback.hom_ext
    · rw [affineToricSchemeUnitSection_comp_fst]
      simp only [Category.assoc, pullbackSpecIso_inv_fst,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      simp [e, Algebra.smul_def, MonoidAlgebra.coe_algebraMap]
    · rw [affineToricSchemeUnitSection_comp_snd]
      simp only [Category.assoc, pullbackSpecIso_inv_snd,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have he : e.comp (Algebra.TensorProduct.includeRight :
          affineCoordinateRing hi σ →ₐ[ℂ]
            affineCoordinateRing hi ⊥ ⊗[ℂ] affineCoordinateRing hi σ) =
          AlgHom.id ℂ (affineCoordinateRing hi σ) := by
        ext x
        simp [e]
      -- `CommRingCat.ofHom` displays the composite as a ring-hom coercion.
      change 𝟙 _ = Spec.map (CommRingCat.ofHom
        (e.comp (Algebra.TensorProduct.includeRight :
          affineCoordinateRing hi σ →ₐ[ℂ]
            affineCoordinateRing hi ⊥ ⊗[ℂ] affineCoordinateRing hi σ)).toRingHom)
      rw [he]
      simp
  rw [hsection, affineToricSchemeAction]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have he : e.comp (affineCoordinateRingCoaction hi σ) =
      AlgHom.id ℂ (affineCoordinateRing hi σ) :=
    affineCoordinateRingCoaction_counit hi σ
  have hs := congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) he
  exact hs.trans (by simp)

/-- Restricting an affine toric chart to a face induces the corresponding map on its product
with the dense torus. On tensor-product coordinate rings it is the identity on the torus factor
and face restriction on the chart factor. -/
noncomputable def affineToricSchemeActionFaceMap {τ : PointedCone ℝ V}
    (hτσ : τ.IsFaceOf σ) :
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi τ)))) ⟶
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ)))) :=
  pullback.map _ _ _ _ (𝟙 _) (faceAffineToricSchemeMap hi hτσ) (𝟙 _)
    (by simp) (by simp [faceAffineToricSchemeMap_def, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- Face restriction leaves the dense-torus projection of the product unchanged. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeActionFaceMap_comp_fst {τ : PointedCone ℝ V}
    (hτσ : τ.IsFaceOf σ) :
    affineToricSchemeActionFaceMap hi σ hτσ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [affineToricSchemeActionFaceMap]

/-- On the affine-chart projection, the product map is face restriction. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeActionFaceMap_comp_snd {τ : PointedCone ℝ V}
    (hτσ : τ.IsFaceOf σ) :
    affineToricSchemeActionFaceMap hi σ hτσ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ faceAffineToricSchemeMap hi hτσ := by
  simp [affineToricSchemeActionFaceMap]

/-- The product map of a reflexive face inclusion is the identity. -/
@[simp]
theorem affineToricSchemeActionFaceMap_id :
    affineToricSchemeActionFaceMap hi σ (PointedCone.IsFaceOf.refl σ) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- Product maps of face inclusions compose as the underlying face maps do. -/
@[simp]
theorem affineToricSchemeActionFaceMap_comp {υ τ : PointedCone ℝ V}
    (hυτ : υ.IsFaceOf τ) (hτσ : τ.IsFaceOf σ) :
    affineToricSchemeActionFaceMap hi τ hυτ ≫
      affineToricSchemeActionFaceMap hi σ hτσ =
        affineToricSchemeActionFaceMap hi σ (hυτ.trans hτσ) := by
  apply pullback.hom_ext <;> simp [Category.assoc, faceAffineToricSchemeMap_comp]

/-- In tensor-product coordinates, the product face map acts as the identity on the torus
factor and as face restriction on the chart factor. -/
@[reassoc]
theorem affineToricSchemeActionFaceMap_comp_pullbackSpecIso {τ : PointedCone ℝ V}
    (hτσ : τ.IsFaceOf σ) :
    affineToricSchemeActionFaceMap hi σ hτσ ≫
      (pullbackSpecIso ℂ (affineCoordinateRing hi ⊥) (affineCoordinateRing hi σ)).hom =
    (pullbackSpecIso ℂ (affineCoordinateRing hi ⊥) (affineCoordinateRing hi τ)).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map
          (AlgHom.id ℂ (affineCoordinateRing hi ⊥))
          (faceAffineCoordinateRingMap hi hτσ)).toRingHom) := by
  rw [← Iso.eq_comp_inv]
  apply pullback.hom_ext
  · rw [affineToricSchemeActionFaceMap_comp_fst]
    simp only [Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← pullbackSpecIso_hom_fst]
    congr 1
    congr 1
    exact (congrArg (fun f => CommRingCat.ofHom f.toRingHom)
      (Algebra.TensorProduct.map_comp_includeLeft
        (AlgHom.id ℂ (affineCoordinateRing hi ⊥))
        (faceAffineCoordinateRingMap hi hτσ))).symm
  · rw [affineToricSchemeActionFaceMap_comp_snd]
    simp only [Category.assoc, pullbackSpecIso_inv_snd, faceAffineToricSchemeMap_def,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← pullbackSpecIso_hom_snd]
    simp only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [cancel_epi]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
      (Algebra.TensorProduct.map_comp_includeRight
        (AlgHom.id ℂ (affineCoordinateRing hi ⊥))
        (faceAffineCoordinateRingMap hi hτσ)).symm

/-- The affine torus action commutes with restriction to a face. This square is the scheme-level
compatibility used to glue the affine actions across the fan's open overlaps. -/
@[reassoc]
theorem affineToricSchemeActionFaceMap_comp_action {τ : PointedCone ℝ V}
    (hτσ : τ.IsFaceOf σ) :
    affineToricSchemeActionFaceMap hi σ hτσ ≫ affineToricSchemeAction hi σ =
      affineToricSchemeAction hi τ ≫ faceAffineToricSchemeMap hi hτσ := by
  simp only [affineToricSchemeAction, Category.assoc]
  rw [← Category.assoc, affineToricSchemeActionFaceMap_comp_pullbackSpecIso]
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [faceAffineToricSchemeMap_def, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have h := affineCoordinateRingCoaction_comp_face hi hτσ
  congr 1
  congr 1
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom) h.symm

end TauCeti.Toric
