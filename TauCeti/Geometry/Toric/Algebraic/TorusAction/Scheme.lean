/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.Geometry.Toric.Algebraic.DenseTorus
public import TauCeti.Geometry.Toric.Algebraic.TorusAction.Coaction

/-!
# The action on an affine toric scheme

The grading coaction on the coordinate ring of an affine toric chart induces a morphism from
the product of the dense torus and the chart to the chart. We construct this morphism using the
standard comparison between a fibre product of affine schemes and the spectrum of a tensor
product, then package it as a morphism of schemes over `Spec ℂ`.

On the zero cone, the action morphism agrees with multiplication on the dense torus. The counit
and coassociativity identities for the underlying coordinate-ring coaction are proved in
`TauCeti.Geometry.Toric.Algebraic.TorusAction.Coaction`.

## Main declarations

* `TauCeti.Toric.affineToricSchemeAction`: the action morphism on an affine toric chart.
* `TauCeti.Toric.affineToricSchemeActionOver`: the action as a morphism over `Spec ℂ`.
* `TauCeti.Toric.affineToricSchemeAction_bot`: on the zero cone, the action is torus
  multiplication.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2--1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonObj MonoidalCategory TensorProduct

namespace TauCeti.Toric

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The action of the dense torus on the affine toric scheme of a cone. Its source is the
fibre product over `Spec ℂ`, identified with the spectrum of the tensor product of coordinate
rings, and its comorphism is `affineCoordinateRingCoaction`. -/
noncomputable def affineToricSchemeAction (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ)))) ⟶
      affineToricScheme hi σ :=
  (pullbackSpecIso ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))
      (affineCoordinateRing hi σ)).hom ≫
    Spec.map (CommRingCat.ofHom (affineCoordinateRingCoaction hi σ).toRingHom)

/-- The affine toric action, packaged as a morphism of schemes over `Spec ℂ`. -/
noncomputable def affineToricSchemeActionOver (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    (denseTorusScheme hi).asOver (Spec (.of ℂ)) ⊗
        (affineToricScheme hi σ).asOver (Spec (.of ℂ)) ⟶
      (affineToricScheme hi σ).asOver (Spec (.of ℂ)) := by
  refine Over.homMk (affineToricSchemeAction hi σ) ?_
  -- The tensor product in `Over` is the chosen pullback, so unfold its structure maps to state
  -- compatibility of the underlying action morphism with the maps to `Spec ℂ`.
  change affineToricSchemeAction hi σ ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ))) =
    pullback.fst
        (Spec.map (CommRingCat.ofHom
          (algebraMap ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ)))) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))))
  rw [affineToricSchemeAction, Category.assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (affineCoordinateRingCoaction hi σ).toRingHom.comp
      (algebraMap ℂ (affineCoordinateRing hi σ)) =
    algebraMap ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V) ⊗[ℂ]
      affineCoordinateRing hi σ) := by
    ext z
    simp
  rw [h]
  exact pullbackSpecIso_hom_base ℂ
    (affineCoordinateRing hi (⊥ : PointedCone ℝ V)) (affineCoordinateRing hi σ)

/-- The underlying scheme morphism of the bundled affine toric action is
`affineToricSchemeAction`. -/
@[simp]
theorem affineToricSchemeActionOver_left (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    (affineToricSchemeActionOver hi σ).left = affineToricSchemeAction hi σ := by
  rw [affineToricSchemeActionOver]
  exact Over.homMk_left _ _

/-- On the zero cone, the affine toric action is multiplication on the dense torus. -/
@[simp]
theorem affineToricSchemeAction_bot (hi : IsIntegralLattice i) :
    affineToricSchemeAction hi (⊥ : PointedCone ℝ V) =
      μ[((denseTorusScheme hi).asOver (Spec (.of ℂ)))].left := by
  rw [affineToricSchemeAction, mul_spec_asOver_spec_left]
  congr 1
  exact congrArg Spec.map <| congrArg CommRingCat.ofHom <|
    congrArg AlgHom.toRingHom <| affineCoordinateRingCoaction_bot hi

/-- On the zero cone, the bundled affine toric action is the multiplication morphism. -/
theorem affineToricSchemeActionOver_bot (hi : IsIntegralLattice i) :
    affineToricSchemeActionOver hi (⊥ : PointedCone ℝ V) =
      μ[((denseTorusScheme hi).asOver (Spec (.of ℂ)))] := by
  ext
  simp

end TauCeti.Toric
