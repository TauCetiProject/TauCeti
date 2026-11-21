/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.EuclideanHalfSpace
public import TauCeti.Geometry.Manifold.SmoothSingular.Transfer.Basic

import TauCeti.Geometry.Manifold.SmoothSingular.Contractible

/-!
# Smooth-chain transfer on the closed half-line `[0, ∞)`

On the closed half-line `EuclideanHalfSpace 1` (`[0, ∞)`), inward translation
`EuclideanHalfSpace.halfLineInwardTranslation` (`r(x) = x + 1`) into the open half-line
`TauCeti.openHalfLine` (`(0, ∞)`), together with the global smooth inward deformation
`TauCeti.halfLineInwardDeformation` (`Φ(t, x) = x + (1 - t)²`), transfers the star-convex
chain homotopy equivalence of `(0, ∞)` to `[0, ∞)`
(`TauCeti.smoothSingularChainHomotopyEquivHalfLine`).

On `0`-simplices, the transferred homotopy inverse sends every singular `0`-simplex (and in
particular the boundary vertex `[0]`) to the interior smooth `0`-simplex `TauCeti.halfLineOne`
(`[1]`, `TauCeti.ι_smoothSingularChainHomotopyEquivHalfLine_inv_f_zero`), whose difference from
`[0]` is the boundary of the smooth curve `t ↦ t²` (`TauCeti.halfLineBridge`,
`TauCeti.ιChainComplex_halfLineBridge_d`).

## Main definitions and results

* `TauCeti.halfLineOne`: the point `1` in `EuclideanHalfSpace 1`.
* `TauCeti.smoothSingularChainHomotopyEquivHalfLine`: concrete inward-translation transfer from
  `(0, ∞)` to `[0, ∞)`.
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

/-- The point `1` of the closed half-line `[0, ∞)`. -/
def halfLineOne : EuclideanHalfSpace 1 :=
  openHalfLineInclusion ⟨1, mem_openHalfLine_iff.mpr zero_lt_one⟩

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
    contMDiff_halfLineInwardTranslation
    contMDiff_halfLineInwardDeformation
    EuclideanHalfSpace.halfLineInwardDeformation_zero
    EuclideanHalfSpace.halfLineInwardDeformation_one R
    (starConvex_openHalfLine.smoothSingularChainHomotopyEquivOfStarConvex R)
    (starConvex_openHalfLine.smoothSingularChainHomotopyEquivOfStarConvex_hom R)

/-- The forward map of `smoothSingularChainHomotopyEquivHalfLine` is the inclusion of smooth
singular chains into continuous singular chains on `[0, ∞)`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivHalfLine_hom
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C) :
    (smoothSingularChainHomotopyEquivHalfLine R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1)).ι R := by
  simp [smoothSingularChainHomotopyEquivHalfLine]

/-- On `[0, ∞)`, the transferred inverse sends every singular `0`-simplex (and in particular the
boundary vertex `[0]`) via `(0, ∞)` to the interior smooth `0`-simplex `[1]`. -/
@[reassoc]
theorem ι_smoothSingularChainHomotopyEquivHalfLine_inv_f_zero
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C)
    (σ : (TopCat.toSSet.obj (TopCat.of (EuclideanHalfSpace 1))) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of (EuclideanHalfSpace 1))).ιChainComplex σ ≫
        (smoothSingularChainHomotopyEquivHalfLine R).inv.f 0 =
      (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex
        ((SmoothSimplex.equiv₀ (𝓡∂ 1) (EuclideanHalfSpace 1)).symm halfLineOne) := by
  rw [smoothSingularChainHomotopyEquivHalfLine,
    ContMDiff.smoothSingularChainHomotopyEquivOfRetract_inv, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, SSet.ι_chainComplexMap_f_assoc,
    starConvex_openHalfLine.ι_smoothSingularChainHomotopyEquivOfStarConvex_inv_f_zero_assoc
      (mem_openHalfLine_iff.mpr zero_lt_one) R,
    SSet.ι_chainComplexMap_f]
  congr 1
  exact SmoothSimplex.smoothSingularSubcomplexMap_app_equiv₀_symm
    contMDiff_openHalfLineInclusion ⟨1, mem_openHalfLine_iff.mpr zero_lt_one⟩

/-- The smooth curve `t ↦ t²` in `[0, ∞)`, which meets the boundary `0` with vanishing velocity so
that it extends smoothly across `t = 0` on all of `ℝ`, bundled as a smooth `1`-simplex from `0` to
`1`. -/
def halfLineBridge : SmoothSimplex (𝓡∂ 1) (EuclideanHalfSpace 1) 1 :=
  SmoothSimplex.ofCurve
    ((contDiff_id.pow 2).contMDiff.modelWithCornersEuclideanHalfSpace_symm_single sq_nonneg)

/-- In the smooth singular chain complex of `[0, ∞)`, the boundary of `halfLineBridge` is
`[1] - [0]`, witnessing that the transferred image `[1]` of the boundary vertex `[0]` is smoothly
homologous to `[0]`. -/
theorem ιChainComplex_halfLineBridge_d
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C) :
    (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex halfLineBridge ≫
        ((smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).chainComplex R).d 1 0 =
      (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex
          ((SmoothSimplex.equiv₀ (𝓡∂ 1) (EuclideanHalfSpace 1)).symm halfLineOne) -
        (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex
          ((SmoothSimplex.equiv₀ (𝓡∂ 1) (EuclideanHalfSpace 1)).symm 0) := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
  have h1 : (𝓡∂ 1).symm (EuclideanSpace.single 0 (1 : ℝ)) = halfLineOne := by
    ext i
    rw [Subsingleton.elim i 0, modelWithCornersEuclideanHalfSpace_symm_apply_of_le (by simp),
      halfLineOne, coe_openHalfLineInclusion_apply]
    simp
  have h0 : (𝓡∂ 1).symm (EuclideanSpace.single 0 (0 : ℝ)) = (0 : EuclideanHalfSpace 1) := by
    ext i
    rw [Subsingleton.elim i 0, modelWithCornersEuclideanHalfSpace_symm_apply_of_le (by simp)]
    simp
    rfl
  simp [halfLineBridge, SmoothSimplex.δ_zero_ofCurve, SmoothSimplex.δ_one_ofCurve, h1, h0,
    sub_eq_add_neg]

end TauCeti
