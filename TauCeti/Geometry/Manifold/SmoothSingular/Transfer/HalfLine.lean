/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.EuclideanHalfSpace
public import TauCeti.Geometry.Manifold.SmoothSingular.Transfer.Basic

import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.SmoothSingular.Contractible

/-!
# Smooth-chain transfer on the closed half-line `[0, ∞)`

This file constructs the inward domination of the closed half-line `EuclideanHalfSpace 1` (`[0, ∞)`)
by the open half-line `TauCeti.openHalfLine` (`(0, ∞)`): the smooth inclusion
`TauCeti.openHalfLineInclusion : openHalfLine → EuclideanHalfSpace 1`, the inward translation
`EuclideanHalfSpace.halfLineInwardTranslation : x ↦ x + 1`, and the global smooth inward
deformation `TauCeti.halfLineInwardDeformation : (t, x) ↦ x + (1 - t)²` from `j ∘ r` to `id`,
together with star-convexity of `openHalfLine` (`TauCeti.starConvex_openHalfLine`).

Applying `ContMDiff.smoothSingularChainHomotopyEquivOfRetract` along `r` and `Φ` transfers the
star-convex chain homotopy equivalence of `(0, ∞)` to `[0, ∞)`
(`TauCeti.smoothSingularChainHomotopyEquivHalfLine`).

On `0`-simplices, the transferred homotopy inverse sends every singular `0`-simplex (and in
particular the boundary vertex `[0]`) to the interior smooth `0`-simplex `TauCeti.halfLineOne`
(`[1]`, `TauCeti.ι_smoothSingularChainHomotopyEquivHalfLine_inv_f_zero`), whose difference from
`[0]` is the boundary of the smooth curve `t ↦ t²` (`TauCeti.halfLineBridge`,
`TauCeti.ιChainComplex_halfLineBridge_d`).

## Main definitions and results

* `TauCeti.openHalfLine`, `TauCeti.openHalfLineInclusion`,
  `TauCeti.contMDiff_openHalfLineInclusion`: the open positive half-line `(0, ∞)` and its smooth
  inclusion into `EuclideanHalfSpace 1`.
* `EuclideanHalfSpace.halfLineInwardTranslation`, `TauCeti.contMDiff_halfLineInwardTranslation`:
  the smooth inward translation `x ↦ x + 1` from `EuclideanHalfSpace 1` into `openHalfLine`.
* `TauCeti.halfLineInwardDeformation`, `TauCeti.contMDiff_halfLineInwardDeformation`,
  `EuclideanHalfSpace.halfLineInwardDeformation_zero`,
  `EuclideanHalfSpace.halfLineInwardDeformation_one`: the global smooth inward deformation
  `(t, x) ↦ x + (1 - t)²` from `j ∘ r` to `id`.
* `TauCeti.starConvex_openHalfLine`: `(0, ∞)` is star-convex around `1`.
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

/-- The open positive half-line `(0, ∞)` as an open submanifold of `ℝ`. -/
def openHalfLine : TopologicalSpace.Opens ℝ :=
  ⟨Ioi 0, isOpen_Ioi⟩

/-- A real number belongs to `openHalfLine` if and only if it is positive. -/
@[simp]
theorem mem_openHalfLine_iff {x : ℝ} : x ∈ openHalfLine ↔ 0 < x :=
  Iff.rfl

/-- Inclusion of the open half-line `(0, ∞)` into the closed half-line `EuclideanHalfSpace 1`. -/
def openHalfLineInclusion (y : openHalfLine) : EuclideanHalfSpace 1 :=
  (𝓡∂ 1).symm (EuclideanSpace.single 0 y.val)

/-- The `0`-th coordinate of `openHalfLineInclusion y` is `y`. -/
@[simp]
theorem coe_openHalfLineInclusion_apply (y : openHalfLine) :
    (openHalfLineInclusion y).val 0 = y.val := by
  have hy : 0 ≤ (EuclideanSpace.single 0 y.val : EuclideanSpace ℝ (Fin 1)) 0 := by
    simpa using (mem_openHalfLine_iff.mp y.property).le
  rw [openHalfLineInclusion, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hy]
  simp

/-- The inclusion `(0, ∞) → [0, ∞)` is smooth with respect to `𝓘(ℝ, ℝ)` and `𝓡∂ 1`. -/
theorem contMDiff_openHalfLineInclusion :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ openHalfLineInclusion :=
  contMDiff_subtypeVal.modelWithCornersEuclideanHalfSpace_symm_single fun y ↦
    (mem_openHalfLine_iff.mp y.property).le

end TauCeti

namespace EuclideanHalfSpace

open TauCeti

/-- Smooth inward translation `r(x) = x + 1` from the closed half-line `[0, ∞)` into its open
interior `(0, ∞)`. -/
def halfLineInwardTranslation (x : EuclideanHalfSpace 1) : openHalfLine :=
  ⟨x.val 0 + 1, mem_openHalfLine_iff.mpr (add_pos_of_nonneg_of_pos x.property zero_lt_one)⟩

/-- The underlying real value of `halfLineInwardTranslation x` is `x.val 0 + 1`. -/
@[simp]
theorem coe_halfLineInwardTranslation (x : EuclideanHalfSpace 1) :
    (x.halfLineInwardTranslation : ℝ) = x.val 0 + 1 :=
  (rfl)

end EuclideanHalfSpace

namespace TauCeti

/-- The inward translation `r(x) = x + 1` is smooth from `EuclideanHalfSpace 1` to `(0, ∞)`. -/
theorem contMDiff_halfLineInwardTranslation :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ EuclideanHalfSpace.halfLineInwardTranslation := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp
    (𝓡∂ 1).contMDiff).add contMDiff_const

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` on `ℝ × [0, ∞)`: because `(1 - t)² ≥ 0` for all
`t ∈ ℝ`, it stays in `[0, ∞)` globally in `t`, starts at `j(r(x)) = x + 1` at `t = 0`, and reaches
`x` at `t = 1`. -/
def halfLineInwardDeformation (p : ℝ × EuclideanHalfSpace 1) : EuclideanHalfSpace 1 :=
  (𝓡∂ 1).symm (EuclideanSpace.single 0 ((𝓡∂ 1) p.2 0 + (1 - p.1) ^ 2))

/-- The `0`-th coordinate of `halfLineInwardDeformation (t, x)` is `x + (1 - t)²`. -/
@[simp]
theorem coe_halfLineInwardDeformation_apply (p : ℝ × EuclideanHalfSpace 1) :
    (halfLineInwardDeformation p).val 0 = p.2.val 0 + (1 - p.1) ^ 2 := by
  have hp : 0 ≤ (EuclideanSpace.single 0 ((𝓡∂ 1) p.2 0 + (1 - p.1) ^ 2) :
      EuclideanSpace ℝ (Fin 1)) 0 := by
    have hx : 0 ≤ p.2.val 0 := p.2.property
    have hsq : 0 ≤ (1 - p.1) ^ 2 := sq_nonneg (1 - p.1)
    simpa using add_nonneg hx hsq
  rw [halfLineInwardDeformation, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hp]
  simp

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` preserves the open interior `(0, ∞)` at every
time `t ∈ ℝ`. -/
theorem halfLineInwardDeformation_pos {t : ℝ} {x : EuclideanHalfSpace 1} (hx : 0 < x.val 0) :
    0 < (halfLineInwardDeformation (t, x)).val 0 := by
  rw [coe_halfLineInwardDeformation_apply]
  nlinarith [sq_nonneg (1 - t)]

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` is jointly smooth on `ℝ × [0, ∞)`. -/
theorem contMDiff_halfLineInwardDeformation :
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) (𝓡∂ 1) ∞ halfLineInwardDeformation := by
  have hcoord : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × EuclideanHalfSpace 1 ↦ (𝓡∂ 1) p.2 0 + (1 - p.1) ^ 2) := by
    have hx : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × EuclideanHalfSpace 1 ↦ (𝓡∂ 1) p.2 0) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp
        (𝓡∂ 1).contMDiff).comp contMDiff_snd
    have ht : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × EuclideanHalfSpace 1 ↦ (1 - p.1) ^ 2) :=
      ((contDiff_const.sub contDiff_id).pow 2).contMDiff.comp contMDiff_fst
    exact hx.add ht
  exact hcoord.modelWithCornersEuclideanHalfSpace_symm_single fun p ↦
    add_nonneg p.2.property (sq_nonneg (1 - p.1))

end TauCeti

namespace EuclideanHalfSpace

open TauCeti

/-- At `t = 0`, `halfLineInwardDeformation` agrees with `j ∘ r`. -/
@[simp]
theorem halfLineInwardDeformation_zero (x : EuclideanHalfSpace 1) :
    halfLineInwardDeformation (0, x) = openHalfLineInclusion x.halfLineInwardTranslation := by
  ext i
  rw [Subsingleton.elim i 0, coe_halfLineInwardDeformation_apply, coe_openHalfLineInclusion_apply,
    coe_halfLineInwardTranslation]
  ring

/-- At `t = 1`, `halfLineInwardDeformation` is the identity on `[0, ∞)`. -/
@[simp]
theorem halfLineInwardDeformation_one (x : EuclideanHalfSpace 1) :
    halfLineInwardDeformation (1, x) = x := by
  ext i
  rw [Subsingleton.elim i 0, coe_halfLineInwardDeformation_apply]
  ring

end EuclideanHalfSpace

namespace TauCeti

/-- The open positive half-line `(0, ∞)` is star-convex around `1`. -/
theorem starConvex_openHalfLine : StarConvex ℝ 1 (openHalfLine : Set ℝ) :=
  (convex_Ioi (0 : ℝ)).starConvex (zero_lt_one : (1 : ℝ) ∈ Ioi 0)

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
