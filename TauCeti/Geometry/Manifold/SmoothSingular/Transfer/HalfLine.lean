/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.HalfLine
public import TauCeti.Geometry.Manifold.SmoothSingular.Contractible
public import TauCeti.Geometry.Manifold.SmoothSingular.Transfer.Basic

/-!
# Smooth-chain transfer on the closed half-line `[0, ∞)`

This file applies `ContMDiff.smoothSingularChainHomotopyEquivOfRetract` to the inward domination of
the closed half-line `EuclideanHalfSpace 1` (`[0, ∞)`) by the open half-line `(0, ∞)`
(`TauCeti.Geometry.Manifold.Instances.HalfLine`), along the inward translation
`EuclideanHalfSpace.halfLineInwardTranslation : x ↦ x + 1` and the global smooth inward deformation
`TauCeti.halfLineInwardDeformation : (t, x) ↦ x + (1 - t)²` from `j ∘ r` to `id`. This transfers
the star-convex chain homotopy equivalence of `(0, ∞)` to `[0, ∞)`
(`TauCeti.smoothSingularChainHomotopyEquivHalfLine`).

On `0`-simplices, the transferred homotopy inverse sends every singular `0`-simplex (and in
particular the boundary vertex `[0]`) to the interior smooth `0`-simplex `[1]`
(`EuclideanHalfSpace.normalRay 1`, `TauCeti.ι_smoothSingularChainHomotopyEquivHalfLine_inv_f_zero`),
whose difference from `[0]` is the boundary of the smooth curve `t ↦ t²` (`TauCeti.halfLineBridge`,
`TauCeti.ιChainComplex_halfLineBridge_d`).

## Main definitions and results

* `TauCeti.smoothSingularChainHomotopyEquivHalfLine`,
  `TauCeti.smoothSingularChainHomotopyEquivHalfLine_hom`,
  `TauCeti.smoothSingularChainHomotopyEquivHalfLine_inv`: concrete inward-translation transfer
  from `(0, ∞)` to `[0, ∞)` and its forward and inverse maps.
* `TauCeti.ι_smoothSingularChainHomotopyEquivHalfLine_inv_f_zero`: the inverse sends every
  singular `0`-simplex to `[1]`.
* `TauCeti.halfLineBridge`, `TauCeti.ιChainComplex_halfLineBridge_d`: the smooth `1`-simplex
  `t ↦ t²` bridging `[0]` to `[1]`.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Set Simplicial Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- **Smooth-chain homotopy equivalence on `[0, ∞)` transferred from `(0, ∞)`.** Combining the
star-convex equivalence on `(0, ∞)` (centred at `1`) with
`ContMDiff.smoothSingularChainHomotopyEquivOfRetract` along `r(x) = x + 1` and
`Φ(t, x) = x + (1 - t)²` yields a chain homotopy equivalence on `EuclideanHalfSpace 1`. -/
def smoothSingularChainHomotopyEquivHalfLine
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C) :
    HomotopyEquiv
      ((smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of (EuclideanHalfSpace 1))).chainComplex R) :=
  contMDiff_openHalfLineInclusion.smoothSingularChainHomotopyEquivOfRetract
    EuclideanHalfSpace.contMDiff_halfLineInwardTranslation
    contMDiff_halfLineInwardDeformation
    halfLineInwardDeformation_zero
    halfLineInwardDeformation_one R
    (smoothSingularChainHomotopyEquivOfStarConvex R starConvex_openHalfLine)
    (smoothSingularChainHomotopyEquivOfStarConvex_hom R starConvex_openHalfLine)

/-- The forward map of `smoothSingularChainHomotopyEquivHalfLine` is the inclusion of smooth
singular chains into continuous singular chains on `[0, ∞)`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivHalfLine_hom
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C) :
    (smoothSingularChainHomotopyEquivHalfLine R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1)).ι R := by
  rw [smoothSingularChainHomotopyEquivHalfLine,
    ContMDiff.smoothSingularChainHomotopyEquivOfRetract_hom]

/-- The homotopy inverse of `smoothSingularChainHomotopyEquivHalfLine` pushes continuous singular
chains of `[0, ∞)` into `(0, ∞)` by `halfLineInwardTranslation`, applies the star-convex
homotopy inverse on `(0, ∞)`, and pushes smooth chains back along `openHalfLineInclusion`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivHalfLine_inv
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C) :
    (smoothSingularChainHomotopyEquivHalfLine R).inv =
      SSet.chainComplexMap
          (TopCat.toSSet.map
            (TopCat.ofHom ⟨EuclideanHalfSpace.halfLineInwardTranslation,
              EuclideanHalfSpace.contMDiff_halfLineInwardTranslation.continuous⟩)) R ≫
        (smoothSingularChainHomotopyEquivOfStarConvex R starConvex_openHalfLine).inv ≫
          SSet.chainComplexMap
            (smoothSingularSubcomplexMap openHalfLineInclusion
              contMDiff_openHalfLineInclusion) R := by
  rw [smoothSingularChainHomotopyEquivHalfLine,
    ContMDiff.smoothSingularChainHomotopyEquivOfRetract_inv]

/-- On `[0, ∞)`, the transferred inverse sends every singular `0`-simplex (and in particular the
boundary vertex `[0]`) via `(0, ∞)` to the interior smooth `0`-simplex `[1]`. -/
@[reassoc]
theorem ι_smoothSingularChainHomotopyEquivHalfLine_inv_f_zero
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C)
    (σ : (TopCat.toSSet.obj (TopCat.of (EuclideanHalfSpace 1))) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of (EuclideanHalfSpace 1))).ιChainComplex σ ≫
        (smoothSingularChainHomotopyEquivHalfLine R).inv.f 0 =
      (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex
        ((SmoothSimplex.equiv₀ (𝓡∂ 1) (EuclideanHalfSpace 1)).symm
          (EuclideanHalfSpace.normalRay 1)) := by
  have hy : openHalfLineInclusion
      (⟨𝓘(ℝ, ℝ).symm (1 : ℝ), by simp⟩ :
        (⟨Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ)) =
      EuclideanHalfSpace.normalRay 1 := by
    rw [← EuclideanHalfSpace.normalRay_normalCoord (openHalfLineInclusion _),
      coe_openHalfLineInclusion_apply]
    simp
  rw [smoothSingularChainHomotopyEquivHalfLine_inv,
    smoothSingularChainHomotopyEquivOfStarConvex_inv R starConvex_openHalfLine
      (by simp),
    ← Functor.map_comp, ← Functor.map_comp,
    constToSmoothSingularSubcomplex_comp_map, map_comp_constToSmoothSingularSubcomplex,
    hy, SSet.ι_chainComplexMap_f, constToSmoothSingularSubcomplex_app_zero]

/-- The smooth curve `t ↦ t²` in `[0, ∞)`, which stays in `[0, ∞)` for every real `t` because
`t² ≥ 0`, bundled as a smooth `1`-simplex from `0` to `1`. -/
def halfLineBridge : SmoothSimplex (𝓡∂ 1) (EuclideanHalfSpace 1) 1 :=
  SmoothSimplex.ofCurve ((contDiff_id.pow 2).contMDiff.normalRay sq_nonneg)

/-- Read on `Δ¹`, `halfLineBridge` evaluates `t ↦ t²`. -/
@[simp]
theorem toContinuousMap_halfLineBridge_apply (x : fullSimplex 1) :
    halfLineBridge.toContinuousMap x = EuclideanHalfSpace.normalRay (x.val 0 ^ 2) :=
  SmoothSimplex.toContinuousMap_ofCurve_apply _ x

/-- In the smooth singular chain complex of `[0, ∞)`, the boundary of `halfLineBridge` is
`[1] - [0]`, witnessing that the transferred image `[1]` of the boundary vertex `[0]` is smoothly
homologous to `[0]`. -/
theorem ιChainComplex_halfLineBridge_d
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C) :
    (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex halfLineBridge ≫
        ((smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).chainComplex R).d 1 0 =
      (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex
          ((SmoothSimplex.equiv₀ (𝓡∂ 1) (EuclideanHalfSpace 1)).symm
            (EuclideanHalfSpace.normalRay 1)) -
        (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex
          ((SmoothSimplex.equiv₀ (𝓡∂ 1) (EuclideanHalfSpace 1)).symm 0) := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp [halfLineBridge, SmoothSimplex.δ_zero_ofCurve, SmoothSimplex.δ_one_ofCurve,
    sub_eq_add_neg]

end TauCeti
