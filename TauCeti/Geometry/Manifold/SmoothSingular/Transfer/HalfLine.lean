/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.SmoothSingular.Contractible
public import TauCeti.Geometry.Manifold.SmoothSingular.Transfer.Basic

/-!
# Smooth-chain transfer on the closed half-line `[0, ∞)`

This file constructs the inward domination of the closed half-line `EuclideanHalfSpace 1` (`[0, ∞)`)
by the open half-line `(0, ∞)` (`⟨Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ`): the smooth
inclusion `TauCeti.openHalfLineInclusion`, the inward translation
`EuclideanHalfSpace.halfLineInwardTranslation : x ↦ x + 1`, and the global smooth inward
deformation `TauCeti.halfLineInwardDeformation : (t, x) ↦ x + (1 - t)²` from `j ∘ r` to `id`.

Applying `ContMDiff.smoothSingularChainHomotopyEquivOfRetract` along `r` and `Φ` transfers the
star-convex chain homotopy equivalence of `(0, ∞)` to `[0, ∞)`
(`TauCeti.smoothSingularChainHomotopyEquivHalfLine`).

On `0`-simplices, the transferred homotopy inverse sends every singular `0`-simplex (and in
particular the boundary vertex `[0]`) to the interior smooth `0`-simplex `[1]`
(`EuclideanHalfSpace.normalRay 1`, `TauCeti.ι_smoothSingularChainHomotopyEquivHalfLine_inv_f_zero`),
whose difference from `[0]` is the boundary of the smooth curve `t ↦ t²` (`TauCeti.halfLineBridge`,
`TauCeti.ιChainComplex_halfLineBridge_d`).

## Main definitions and results

* `TauCeti.openHalfLineInclusion`, `TauCeti.contMDiff_openHalfLineInclusion`: the smooth inclusion
  of the open positive half-line `(0, ∞)` into `EuclideanHalfSpace 1`.
* `EuclideanHalfSpace.halfLineInwardTranslation`,
  `EuclideanHalfSpace.contMDiff_halfLineInwardTranslation`: the smooth inward translation
  `x ↦ x + 1` from `EuclideanHalfSpace 1` into `(0, ∞)`.
* `TauCeti.halfLineInwardDeformation`, `TauCeti.contMDiff_halfLineInwardDeformation`,
  `TauCeti.halfLineInwardDeformation_zero`, `TauCeti.halfLineInwardDeformation_one`: the global
  smooth inward deformation `(t, x) ↦ x + (1 - t)²` from `j ∘ r` to `id`.
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

/-- Inclusion of the open half-line `(0, ∞)` into the closed half-line `EuclideanHalfSpace 1`. -/
def openHalfLineInclusion (y : (⟨Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ)) :
    EuclideanHalfSpace 1 :=
  EuclideanHalfSpace.normalRay y.val

/-- The `0`-th coordinate of `openHalfLineInclusion y` is `y`. -/
@[simp]
theorem coe_openHalfLineInclusion_apply
    (y : (⟨Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ)) :
    (openHalfLineInclusion y).val 0 = y.val := by
  rw [openHalfLineInclusion, EuclideanHalfSpace.normalRay_coe_apply,
    max_eq_left (Set.mem_Ioi.mp y.property).le]

/-- The inclusion `(0, ∞) → [0, ∞)` is smooth with respect to `𝓘(ℝ, ℝ)` and `𝓡∂ 1`. -/
theorem contMDiff_openHalfLineInclusion :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ openHalfLineInclusion :=
  contMDiff_subtypeVal.normalRay fun y ↦ (Set.mem_Ioi.mp y.property).le

end TauCeti

namespace EuclideanHalfSpace

open TauCeti

/-- Smooth inward translation `r(x) = x + 1` from the closed half-line `[0, ∞)` into its open
interior `(0, ∞)`. -/
def halfLineInwardTranslation (x : EuclideanHalfSpace 1) :
    (⟨Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ) :=
  ⟨x.val 0 + 1, Set.mem_Ioi.mpr (add_pos_of_nonneg_of_pos x.property zero_lt_one)⟩

/-- The underlying real value of `halfLineInwardTranslation x` is `x.val 0 + 1`. -/
@[simp]
theorem coe_halfLineInwardTranslation (x : EuclideanHalfSpace 1) :
    (x.halfLineInwardTranslation : ℝ) = x.val 0 + 1 :=
  (rfl)

/-- The inward translation `r(x) = x + 1` is smooth from `EuclideanHalfSpace 1` to `(0, ∞)`. -/
theorem contMDiff_halfLineInwardTranslation :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ halfLineInwardTranslation := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp
    (𝓡∂ 1).contMDiff).add contMDiff_const

end EuclideanHalfSpace

namespace TauCeti

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` on `ℝ × [0, ∞)`: because `(1 - t)² ≥ 0` for all
`t ∈ ℝ`, it stays in `[0, ∞)` globally in `t`, starts at `j(r(x)) = x + 1` at `t = 0`, and reaches
`x` at `t = 1`. -/
def halfLineInwardDeformation (p : ℝ × EuclideanHalfSpace 1) : EuclideanHalfSpace 1 :=
  EuclideanHalfSpace.normalRay (p.2.val 0 + (1 - p.1) ^ 2)

/-- The `0`-th coordinate of `halfLineInwardDeformation (t, x)` is `x + (1 - t)²`. -/
@[simp]
theorem coe_halfLineInwardDeformation_apply (p : ℝ × EuclideanHalfSpace 1) :
    (halfLineInwardDeformation p).val 0 = p.2.val 0 + (1 - p.1) ^ 2 := by
  rw [halfLineInwardDeformation, EuclideanHalfSpace.normalRay_coe_apply,
    max_eq_left (add_nonneg p.2.property (sq_nonneg (1 - p.1)))]

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
      (fun p : ℝ × EuclideanHalfSpace 1 ↦ p.2.val 0 + (1 - p.1) ^ 2) := by
    have hx : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × EuclideanHalfSpace 1 ↦ p.2.val 0) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp
        (𝓡∂ 1).contMDiff).comp contMDiff_snd
    have ht : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × EuclideanHalfSpace 1 ↦ (1 - p.1) ^ 2) :=
      ((contDiff_const.sub contDiff_id).pow 2).contMDiff.comp contMDiff_fst
    exact hx.add ht
  exact hcoord.normalRay fun p ↦ add_nonneg p.2.property (sq_nonneg (1 - p.1))

/-- At `t = 0`, `halfLineInwardDeformation` agrees with `j ∘ r`. -/
@[simp]
theorem halfLineInwardDeformation_zero (x : EuclideanHalfSpace 1) :
    halfLineInwardDeformation (0, x) = openHalfLineInclusion x.halfLineInwardTranslation := by
  ext i
  rw [Subsingleton.elim i 0, coe_halfLineInwardDeformation_apply, coe_openHalfLineInclusion_apply,
    EuclideanHalfSpace.coe_halfLineInwardTranslation]
  ring

/-- At `t = 1`, `halfLineInwardDeformation` is the identity on `[0, ∞)`. -/
@[simp]
theorem halfLineInwardDeformation_one (x : EuclideanHalfSpace 1) :
    halfLineInwardDeformation (1, x) = x := by
  ext i
  rw [Subsingleton.elim i 0, coe_halfLineInwardDeformation_apply]
  ring

/-- The open positive half-line `(0, ∞)` is star-convex about `1`. -/
theorem starConvex_openHalfLine :
    StarConvex ℝ (1 : ℝ)
      (𝓘(ℝ) '' ((⟨Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ) : Set ℝ)) := by
  simpa using (convex_Ioi (0 : ℝ)).starConvex (zero_lt_one : (1 : ℝ) ∈ Ioi 0)

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
  simp [smoothSingularChainHomotopyEquivHalfLine]

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
        ((SmoothSimplex.equiv₀ (𝓡∂ 1) (EuclideanHalfSpace 1)).symm
          (EuclideanHalfSpace.normalRay 1)) := by
  rw [smoothSingularChainHomotopyEquivHalfLine,
    ContMDiff.smoothSingularChainHomotopyEquivOfRetract_inv, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, SSet.ι_chainComplexMap_f_assoc,
    ι_smoothSingularChainHomotopyEquivOfStarConvex_inv_f_zero_assoc R starConvex_openHalfLine
      (Set.mem_Ioi.mpr zero_lt_one),
    SSet.ι_chainComplexMap_f]
  congr 1
  exact SmoothSimplex.smoothSingularSubcomplexMap_app_equiv₀_symm
    contMDiff_openHalfLineInclusion ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩

/-- The smooth curve `t ↦ t²` in `[0, ∞)`, which stays in `[0, ∞)` for every real `t` because
`t² ≥ 0`, bundled as a smooth `1`-simplex from `0` to `1`. -/
def halfLineBridge : SmoothSimplex (𝓡∂ 1) (EuclideanHalfSpace 1) 1 :=
  SmoothSimplex.ofCurve ((contDiff_id.pow 2).contMDiff.normalRay sq_nonneg)

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
