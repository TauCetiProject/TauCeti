/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Basic

/-!
# Naturality of the algebraic–analytic toric comparison

A fan morphism acts on algebraic complex points by composition with its morphism of fan
schemes. On an affine chart this is pullback along the map of dual semigroups, exactly as for
the analytic toric map. Consequently the algebraic–analytic comparison commutes with toric
maps. This identifies the actual scheme-theoretic map on complex points, rather than defining
it by conjugating an analytic map.

The map on algebraic complex points is continuous for the topology glued from affine charts,
even for nonregular fans. Identity and composition agree with those of scheme morphisms.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric.FanHom

variable {N N' N'' V V' V'' : Type} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V''] [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}
  {Φ : Fan i} {Ψ : Fan i'} {Ω : Fan i''} (f : FanHom Φ Ψ)

private theorem spec_map_comp_affineToricChartMap (σ : Φ.cones)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
    Spec.map (CommRingCat.ofHom x.toRingHom) ≫ f.affineToricChartMap σ =
      Spec.map (CommRingCat.ofHom (x.comp
        (affineCoordinateRingMap Φ.lattice Ψ.lattice f.latticeMap f.realMap
          f.map_lattice (f.mapsTo_leastCone σ.2))).toRingHom) := by
  rw [affineToricChartMap_def, affineToricSchemeMap_def, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (Spec.map ∘ CommRingCat.ofHom) (AlgHom.comp_toRingHom x _).symm

/-- On an affine chart, the algebraic map on complex points pulls back along the map of dual
semigroups into the least target cone. This holds without regularity of either fan. -/
@[simp]
theorem algebraicComplexPointMap_ofAffinePoint (σ : Φ.cones)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
    f.algebraicComplexPointMap (Fan.AlgebraicComplexPoint.ofAffinePoint σ x) =
      Fan.AlgebraicComplexPoint.ofAffinePoint
        (Φ := Ψ) ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩
        (f.analyticChartMap (υ := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩)
          (f.mapsTo_leastCone σ.2) x) := by
  ext1
  -- The analytic chart map has the bundled chart carrier; full transparency identifies it
  -- with the affine complex-point carrier used by `ofAffinePoint`.
  erw [coe_algebraicComplexPointMap, Fan.AlgebraicComplexPoint.coe_ofAffinePoint,
    Fan.AlgebraicComplexPoint.coe_ofAffinePoint, Category.assoc,
    affineToricChartι_comp_algebraicMap, ← Category.assoc, spec_map_comp_affineToricChartMap]
  congr 2
  erw [analyticChartMap_apply]
  have hp : x.comp (affineCoordinateRingMap Φ.lattice Ψ.lattice f.latticeMap f.realMap
      f.map_lattice (f.mapsTo_leastCone σ.2)) =
      AffineSemigroupComplexPoint.comap (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap
        f.realMap f.map_lattice (f.mapsTo_leastCone σ.2)) x := by
    apply AffineSemigroupComplexPoint.ext
    intro m
    simp
  exact congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom hp)

/-- The scheme-theoretic map on complex points is continuous for the glued monomial topologies,
including for nonregular fans. -/
@[fun_prop]
theorem continuous_algebraicComplexPointMap : Continuous f.algebraicComplexPointMap := by
  refine continuous_iSup_dom.2 fun σ ↦ continuous_coinduced_dom.2 ?_
  have h : f.algebraicComplexPointMap ∘
      (fun x : Φ.analyticAffineChart σ ↦ Fan.AlgebraicComplexPoint.ofAffinePoint σ x) =
      (fun x : Ψ.analyticAffineChart ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩ ↦
        Fan.AlgebraicComplexPoint.ofAffinePoint ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩ x) ∘
      f.analyticChartMap (υ := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩)
        (f.mapsTo_leastCone σ.2) :=
    funext (f.algebraicComplexPointMap_ofAffinePoint σ)
  rw [h]
  exact (Fan.AlgebraicComplexPoint.continuous_ofAffinePoint _).comp
    (f.analyticChartMap _).hom.continuous

/-- The algebraic–analytic comparison commutes with a toric map of regular fans. -/
theorem algebraicAnalyticEquiv_naturality (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (p : Φ.AlgebraicComplexPoint) :
    Fan.algebraicAnalyticEquiv hΨ (f.algebraicComplexPointMap p) =
      f.analyticMap hΦ hΨ (Fan.algebraicAnalyticEquiv hΦ p) := by
  obtain ⟨σ, x, rfl⟩ := Fan.AlgebraicComplexPoint.exists_ofAffinePoint_eq p
  -- Here the chart representatives initially have the affine-point carrier, not the bundled
  -- carrier in the analytic comparison formulas.
  erw [algebraicComplexPointMap_ofAffinePoint, Fan.algebraicAnalyticEquiv_ofAffinePoint,
    Fan.algebraicAnalyticEquiv_ofAffinePoint, analyticMap_analyticAffineChartι]

/-- The inverse algebraic–analytic comparison also commutes with toric maps. -/
@[simp]
theorem algebraicAnalyticEquiv_symm_naturality (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (p : Φ.analyticRealization hΦ) :
    (Fan.algebraicAnalyticEquiv hΨ).symm (f.analyticMap hΦ hΨ p) =
      f.algebraicComplexPointMap ((Fan.algebraicAnalyticEquiv hΦ).symm p) := by
  apply (Fan.algebraicAnalyticEquiv hΨ).injective
  simpa using (f.algebraicAnalyticEquiv_naturality hΦ hΨ
    ((Fan.algebraicAnalyticEquiv hΦ).symm p)).symm

end TauCeti.Toric.FanHom
