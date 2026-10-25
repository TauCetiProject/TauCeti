/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.TorusAction.Action

/-!
# Naturality of algebraic toric actions

A morphism of finite fans induces both a morphism of their dense tori and a morphism of their
toric schemes.  The product of these maps intertwines the global torus actions.  The proof is
chartwise: on an affine cone chart it is the equivariance of the character-grading coaction.
No regularity or nonemptiness assumption on either fan is needed.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3--1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.3 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

namespace TauCeti.Toric.FanHom

variable {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (f : FanHom Φ Ψ)

private theorem mapsTo_bot :
    Set.MapsTo f.realMap (⊥ : PointedCone ℝ V) (⊥ : PointedCone ℝ V') := by
  simp [Set.MapsTo]

/-- The map between the action domains induced by a fan morphism: on the first factor it is the
dense-torus map induced by the lattice map, and on the second it is the algebraic toric map. -/
noncomputable def algebraicActionMap :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ
          (affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)))))
        Φ.algebraicRealizationStructureMap ⟶
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ
          (affineCoordinateRing Ψ.lattice (⊥ : PointedCone ℝ V')))))
    Ψ.algebraicRealizationStructureMap :=
  pullback.map _ _ _ _
    (affineToricSchemeMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice
      f.mapsTo_bot)
    f.algebraicMap (𝟙 _)
    (by
      rw [Category.comp_id, affineToricSchemeMap_def]
      exact (comp_over (Spec.map (CommRingCat.ofHom
        (affineCoordinateRingMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice
          f.mapsTo_bot).toRingHom)) (Spec (.of ℂ))).symm)
    (by rw [Category.comp_id, FanHom.algebraicMap_comp_algebraicRealizationStructureMap])

/-- On the torus factor, the map of action domains is the affine toric map of the zero cones. -/
@[reassoc (attr := simp)]
theorem algebraicActionMap_comp_fst :
    f.algebraicActionMap ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫
        affineToricSchemeMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice
          (by simp [Set.MapsTo]) := by
  simp [algebraicActionMap]

/-- On the realization factor, the map of action domains is the algebraic toric map. -/
@[reassoc (attr := simp)]
theorem algebraicActionMap_comp_snd :
    f.algebraicActionMap ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f.algebraicMap := by
  simp [algebraicActionMap]

/-- The product of a dense torus with a source affine chart maps to the product with its least
target chart by the affine action-domain map. -/
@[reassoc]
theorem algebraicRealizationActionChartMap_comp_algebraicActionMap (σ : Φ.cones) :
    Fan.algebraicRealizationActionChartMap σ ≫ f.algebraicActionMap =
      affineToricSchemeActionMap Φ.lattice σ.1 Ψ.lattice f.latticeMap f.realMap
          f.map_lattice (f.mapsTo_leastCone σ.2) ≫
        Fan.algebraicRealizationActionChartMap
          ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩ := by
  apply pullback.hom_ext
  · simp
  · simp [affineToricChartMap_def]

/-- Algebraic toric maps are equivariant: acting on the source and then applying the toric map
equals applying the induced maps on the torus and realization factors and then acting on the
target. -/
@[reassoc]
theorem algebraicActionMap_comp_algebraicRealizationAction :
    f.algebraicActionMap ≫ Ψ.algebraicRealizationAction =
      Φ.algebraicRealizationAction ≫ f.algebraicMap := by
  apply Fan.algebraicRealizationActionChartMap_hom_ext
  intro σ
  simp [algebraicRealizationActionChartMap_comp_algebraicActionMap_assoc,
    affineToricSchemeActionMap_comp_action_assoc,
    Fan.algebraicRealizationActionChartMap_comp_algebraicRealizationAction_assoc,
    affineToricChartι_comp_algebraicMap, affineToricChartMap_def]

end TauCeti.Toric.FanHom
