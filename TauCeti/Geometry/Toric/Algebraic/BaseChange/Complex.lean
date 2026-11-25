/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.BaseChange.Fan
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over
public import TauCeti.Geometry.Toric.Algebraic.IntegralModel

/-!
# Toric schemes over `ℂ` and the complex realization of a fan

Over the complex numbers, the toric scheme `X_{Φ,ℂ}` of a finite fan, glued from the charts
`Spec ℂ[P_σ]` in additive exponent notation, is the algebraic realization
`TauCeti.Toric.Fan.algebraicRealization` of the fan, glued from the charts of
`TauCeti.Toric.affineToricScheme` in multiplicative exponent notation. The chart comparisons
`TauCeti.Toric.affineToricSchemeIsoAddMonoidAlgebraSpec` change exponent notation by Mathlib's
`AddMonoidAlgebra.toMultiplicativeAlgEquiv`; they commute with the face maps, so they glue to an
isomorphism of toric schemes over `Spec ℂ`. Thus the coefficient-general construction specializes
to the existing complex one rather than producing a second complex toric scheme.

## Main declarations

* `TauCeti.Toric.Fan.affineChartDiagramComplexIso`: the isomorphism of chart diagrams.
* `TauCeti.Toric.Fan.finiteFanSchemeComplexIso`: `X_{Φ,ℂ}` is the algebraic realization of `Φ`.
* `TauCeti.Toric.Fan.finiteFanSchemeComplexIso_hom_comp_algebraicRealizationStructureMap`: the
  isomorphism lies over `Spec ℂ`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2–1.4.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V} (Φ : Fan i)

-- The change of exponent notation intertwines the multiplicative and additive face ring maps.
private theorem faceAffineCoordinateRingMap_comp_toMultiplicativeAlgEquiv {τ σ : Φ.cones}
    (hτσ : τ.val.IsFaceOf σ.val) :
    (faceAffineCoordinateRingMap Φ.lattice hτσ).comp
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup Φ.lattice σ.val) :
          _ →ₐ[ℂ] _) =
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup Φ.lattice τ.val) :
          _ →ₐ[ℂ] _).comp (faceAffineChartRingMap ℂ Φ.lattice hτσ) :=
  AddMonoidAlgebra.algHom_ext (fun m ↦ by
    simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply,
      AddMonoidAlgebra.toMultiplicativeAlgEquiv_single, faceAffineCoordinateRingMap_single,
      faceAffineChartRingMap_single]
    -- On a monomial both sides give the monomial of the same character of `τ`.
    exact congrArg (MonoidAlgebra.single · 1) (congrArg Multiplicative.ofAdd
      (Subtype.ext (AddSubmonoid.coe_inclusion _ m).symm))) (Subsingleton.elim _ _)

/-- The change of exponent notation identifies the diagram of affine toric charts in
multiplicative notation with the diagram of complex affine charts in additive notation. -/
noncomputable def affineChartDiagramComplexIso : Φ.affineToricDiagram ≅ Φ.affineChartDiagram ℂ :=
  NatIso.ofComponents
    (fun σ ↦ (Over.forget _).mapIso (affineToricSchemeIsoAddMonoidAlgebraSpec Φ.lattice σ))
    fun {τ σ} f ↦ by
      have hτσ := Φ.isFaceOf_of_le σ.property τ.property (leOfHom f)
      have key :
          Spec.map (CommRingCat.ofHom (faceAffineCoordinateRingMap Φ.lattice hτσ).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ
            (dualSemigroup Φ.lattice σ.val) : _ →ₐ[ℂ] _).toRingHom) =
          Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ
            (dualSemigroup Φ.lattice τ.val) : _ →ₐ[ℂ] _).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (faceAffineChartRingMap ℂ Φ.lattice hτσ).toRingHom) := by
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun φ : _ →ₐ[ℂ] _ ↦ Spec.map (CommRingCat.ofHom φ.toRingHom))
          (faceAffineCoordinateRingMap_comp_toMultiplicativeAlgEquiv Φ hτσ)
      -- The diagram maps and the components unfold to the spectra of the ring maps in `key`.
      simp only [Functor.mapIso_hom, Over.forget_map,
        affineToricSchemeIsoAddMonoidAlgebraSpec_hom_left, affineToricDiagram_map,
        affineChartDiagram_map, faceAffineToricSchemeMap_def, faceAffineChartMap_def]
      exact key

/-- On the chart of a cone, the comparison of chart diagrams is the change of exponent
notation. -/
@[simp]
theorem affineChartDiagramComplexIso_hom_app (σ : Φ.cones) :
    (Φ.affineChartDiagramComplexIso).hom.app σ =
      (affineToricSchemeIsoAddMonoidAlgebraSpec Φ.lattice σ).hom.left :=
  (rfl)

/-- On the chart of a cone, the inverse comparison of chart diagrams is the inverse change of
exponent notation. -/
@[simp]
theorem affineChartDiagramComplexIso_inv_app (σ : Φ.cones) :
    (Φ.affineChartDiagramComplexIso).inv.app σ =
      (affineToricSchemeIsoAddMonoidAlgebraSpec Φ.lattice σ).inv.left :=
  (rfl)

/-- The toric scheme of a finite fan over `ℂ` is its algebraic realization. -/
noncomputable def finiteFanSchemeComplexIso : Φ.finiteFanScheme ℂ ≅ Φ.algebraicRealization :=
  (Φ.isColimitAffineChartCocone ℂ).coconePointsIsoOfNatIso Φ.isColimitAffineToricCocone
    Φ.affineChartDiagramComplexIso.symm

/-- On the chart of a cone, the comparison is the change of exponent notation followed by the
inclusion of the affine toric chart. -/
@[reassoc (attr := simp)]
theorem affineChartι_finiteFanSchemeComplexIso_hom (σ : Φ.cones) :
    Φ.affineChartι ℂ σ ≫ Φ.finiteFanSchemeComplexIso.hom =
      (affineToricSchemeIsoAddMonoidAlgebraSpec Φ.lattice σ).inv.left ≫
        Φ.affineToricChartι σ := by
  have h := (Φ.isColimitAffineChartCocone ℂ).comp_coconePointsIsoOfNatIso_hom
    Φ.isColimitAffineToricCocone Φ.affineChartDiagramComplexIso.symm σ
  rw [affineToricCocone_ι_app] at h
  exact h

/-- On the affine toric chart of a cone, the inverse comparison is the change of exponent notation
followed by the inclusion of the complex affine chart. -/
@[reassoc (attr := simp)]
theorem affineToricChartι_finiteFanSchemeComplexIso_inv (σ : Φ.cones) :
    Φ.affineToricChartι σ ≫ Φ.finiteFanSchemeComplexIso.inv =
      (affineToricSchemeIsoAddMonoidAlgebraSpec Φ.lattice σ).hom.left ≫ Φ.affineChartι ℂ σ := by
  have h := (Φ.isColimitAffineChartCocone ℂ).comp_coconePointsIsoOfNatIso_inv
    Φ.isColimitAffineToricCocone Φ.affineChartDiagramComplexIso.symm σ
  rw [affineToricCocone_ι_app] at h
  exact h

/-- The comparison of toric schemes lies over `Spec ℂ`. -/
@[reassoc (attr := simp)]
theorem finiteFanSchemeComplexIso_hom_comp_algebraicRealizationStructureMap :
    Φ.finiteFanSchemeComplexIso.hom ≫ Φ.algebraicRealizationStructureMap =
      Φ.finiteFanSchemeToSpec ℂ := by
  ext σ : 1
  rw [affineChartι_finiteFanSchemeComplexIso_hom_assoc,
    affineToricChartι_comp_algebraicRealizationStructureMap, affineChartι_finiteFanSchemeToSpec]
  exact Over.w (affineToricSchemeIsoAddMonoidAlgebraSpec Φ.lattice σ).inv

end TauCeti.Toric.Fan
