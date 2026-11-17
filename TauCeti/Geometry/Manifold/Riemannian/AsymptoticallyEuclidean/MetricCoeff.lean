/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.MetricCoeff

import TauCeti.Analysis.Normed.Module.Ball.Exterior
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Topology.Maps.Proper.Metric

/-!
# Coordinate exteriors and exterior pullback metric coefficients

This file provides the open coordinate exterior `exteriorOpen n R = {x ∈ ℝⁿ : R < ‖x‖}` and the
exterior Riemannian coordinate metric coefficients `exteriorMetricCoeff φ` (for maps
`φ : exteriorOpen n R → M`, extended by `0` on `{x : ‖x‖ ≤ R}`), together with their compatibility
with ambient pullback metric coefficients `pullbackMetricCoeff` (from
`TauCeti.Geometry.Manifold.Riemannian.Pullback.MetricCoeff`). These definitions are the shared
exterior coordinate substrate for asymptotically Euclidean ends
(`TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic`) and the coordinate ADM flux
(`TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Flux`).

## Main definitions

* `TauCeti.exteriorOpen`: the open submanifold `{x ∈ ℝⁿ : R < ‖x‖}` of `EuclideanSpace ℝ (Fin n)`.
* `TauCeti.exteriorMetricCoeff`: coordinate metric coefficients for an exterior map
  `φ : exteriorOpen n R → M`, extended by `0` on `{x : ‖x‖ ≤ R}`.

## Main results

* `TauCeti.isPathConnected_exteriorOpen` and `TauCeti.isConnected_exteriorOpen`: path-connectedness
  and connectedness of `exteriorOpen n R` for `2 ≤ n`.
* `TauCeti.isProperMap_exteriorOpen_norm`: properness of the coordinate norm map
  `exteriorOpen n R → Set.Ioi R`.
* `TauCeti.eventuallyEq_exteriorMetricCoeff`: local-germ congruence for exterior metric
  coefficients.
* `TauCeti.exteriorMetricCoeff_comp_subtypeVal_of_lt`,
  `TauCeti.eventuallyEq_exteriorMetricCoeff_comp_subtypeVal`, and
  `TauCeti.exteriorMetricCoeff_comp_inclusion_of_lt`: compatibility of `exteriorMetricCoeff` with
  ambient restriction (`pullbackMetricCoeff`) and nested exterior inclusions.
-/

public section

noncomputable section

open Set Function Filter Metric TopologicalSpace Bundle
open scoped Topology Manifold ContDiff RealInnerProductSpace

namespace TauCeti

/-! ### Coordinate exteriors -/

/-- The open exterior `{x ∈ ℝⁿ : R < ‖x‖}` of the closed coordinate ball of radius `R`, viewed as
an open submanifold of `EuclideanSpace ℝ (Fin n)`. -/
def exteriorOpen (n : ℕ) (R : ℝ) : Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨{x | R < ‖x‖}, isOpen_lt continuous_const continuous_norm⟩

@[simp] theorem coe_exteriorOpen (n : ℕ) (R : ℝ) :
    (exteriorOpen n R : Set (EuclideanSpace ℝ (Fin n))) = {x | R < ‖x‖} := (rfl)

@[simp] theorem mem_exteriorOpen {n : ℕ} {R : ℝ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ exteriorOpen n R ↔ R < ‖x‖ := Iff.rfl

/-- Increasing the excision radius shrinks `exteriorOpen`: for `R ≤ R'`,
`exteriorOpen n R' ≤ exteriorOpen n R`. -/
theorem exteriorOpen_anti {n : ℕ} {R R' : ℝ} (h : R ≤ R') :
    exteriorOpen n R' ≤ exteriorOpen n R :=
  fun _ hx => h.trans_lt (mem_exteriorOpen.mp hx)

/-- The exterior `exteriorOpen n R` is the complement of the closed ball of radius `R` at `0`. -/
theorem coe_exteriorOpen_eq_compl_closedBall (n : ℕ) (R : ℝ) :
    (exteriorOpen n R : Set (EuclideanSpace ℝ (Fin n))) = (closedBall 0 R)ᶜ := by
  ext x; simp [dist_zero_right]

/-- Every point of `exteriorOpen n R` for `0 ≤ R` is nonzero. -/
theorem exteriorOpen_coe_ne_zero {n : ℕ} {R : ℝ} (hR : 0 ≤ R) (x : exteriorOpen n R) :
    (x : EuclideanSpace ℝ (Fin n)) ≠ 0 :=
  norm_pos_iff.mp (hR.trans_lt (mem_exteriorOpen.mp x.2))

/-- In positive dimension, `exteriorOpen n R` is nonempty for every `R`. -/
theorem exteriorOpen_nonempty {n : ℕ} (hn : 1 ≤ n) (R : ℝ) :
    (exteriorOpen n R : Set (EuclideanSpace ℝ (Fin n))).Nonempty := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact NormedSpace.exists_lt_norm ℝ (EuclideanSpace ℝ (Fin n)) R

/-- In dimension at least `2`, `exteriorOpen n R` is path-connected. -/
theorem isPathConnected_exteriorOpen {n : ℕ} (hn : 2 ≤ n) (R : ℝ) :
    IsPathConnected (exteriorOpen n R : Set (EuclideanSpace ℝ (Fin n))) := by
  rw [coe_exteriorOpen_eq_compl_closedBall]
  refine isPathConnected_compl_closedBall ?_ 0 R
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast hn

/-- In dimension at least `2`, `exteriorOpen n R` is connected. -/
theorem isConnected_exteriorOpen {n : ℕ} (hn : 2 ≤ n) (R : ℝ) :
    IsConnected (exteriorOpen n R : Set (EuclideanSpace ℝ (Fin n))) :=
  (isPathConnected_exteriorOpen hn R).isConnected

/-- The coordinate norm map `x ↦ ⟨‖x‖, ...⟩` from `exteriorOpen n R` to `Set.Ioi R` is proper. -/
theorem isProperMap_exteriorOpen_norm {n : ℕ} {R : ℝ} :
    IsProperMap (fun x : exteriorOpen n R =>
      (⟨‖(x : EuclideanSpace ℝ (Fin n))‖, mem_exteriorOpen.mp x.2⟩ : Ioi R)) :=
  isProperMap_norm_Ioi R

/-! ### Exterior metric coefficients -/

section ExteriorMetricCoeff

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)]

/-- The Riemannian metric coefficients of a map `φ : exteriorOpen n R → M` defined on the exterior
`{x ∈ ℝⁿ : R < ‖x‖}`, extended by `0` on `{x : ‖x‖ ≤ R}`. -/
def exteriorMetricCoeff {R : ℝ} (φ : exteriorOpen n R → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  if hx : R < ‖x‖ then
    ⟪mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i),
      mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ j)⟫
  else 0

theorem exteriorMetricCoeff_def {R : ℝ} (φ : exteriorOpen n R → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    exteriorMetricCoeff φ x i j =
      if hx : R < ‖x‖ then
        ⟪mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i),
          mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ j)⟫
      else 0 := (rfl)

theorem exteriorMetricCoeff_of_lt {R : ℝ} (φ : exteriorOpen n R → M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) (i j : Fin n) :
    exteriorMetricCoeff φ x i j =
      ⟪mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i),
        mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩
          (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ :=
  dite_eq_left_of_eq_true (eq_true hx)

@[simp] theorem exteriorMetricCoeff_of_le {R : ℝ} (φ : exteriorOpen n R → M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ R) (i j : Fin n) :
    exteriorMetricCoeff φ x i j = 0 :=
  dite_eq_right_of_eq_false (eq_false (not_lt.mpr hx))

/-- Exterior metric coefficients are symmetric in `i` and `j`. -/
theorem exteriorMetricCoeff_symm {R : ℝ} (φ : exteriorOpen n R → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    exteriorMetricCoeff φ x i j = exteriorMetricCoeff φ x j i := by
  by_cases hx : R < ‖x‖
  · rw [exteriorMetricCoeff_of_lt _ hx, exteriorMetricCoeff_of_lt _ hx, real_inner_comm]
  · rw [exteriorMetricCoeff_of_le _ (not_lt.mp hx), exteriorMetricCoeff_of_le _ (not_lt.mp hx)]

/-- If two maps `φ₁ φ₂ : exteriorOpen n R → M` agree on a neighbourhood of `⟨x, ...⟩`, their
exterior metric coefficients agree at `x`. -/
theorem exteriorMetricCoeff_congr_nhds {R : ℝ} {φ₁ φ₂ : exteriorOpen n R → M}
    {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖)
    (h : φ₁ =ᶠ[𝓝 (⟨x, mem_exteriorOpen.mpr hx⟩ : exteriorOpen n R)] φ₂) (i j : Fin n) :
    exteriorMetricCoeff φ₁ x i j = exteriorMetricCoeff φ₂ x i j := by
  rw [exteriorMetricCoeff_of_lt _ hx, exteriorMetricCoeff_of_lt _ hx, h.mfderiv_eq]
  exact inner_tangentSpaceCast h.self_of_nhds.symm _ _

/-- If two maps `φ₁ φ₂ : exteriorOpen n R → M` agree on a neighbourhood of `⟨x, ...⟩`, their
exterior metric coefficients agree on a neighbourhood of `x` in `ℝⁿ`. -/
theorem eventuallyEq_exteriorMetricCoeff {R : ℝ} {φ₁ φ₂ : exteriorOpen n R → M}
    {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖)
    (h : φ₁ =ᶠ[𝓝 (⟨x, mem_exteriorOpen.mpr hx⟩ : exteriorOpen n R)] φ₂) (i j : Fin n) :
    (fun y => exteriorMetricCoeff φ₁ y i j) =ᶠ[𝓝 x] (fun y => exteriorMetricCoeff φ₂ y i j) := by
  have hmap : Filter.map (Subtype.val : exteriorOpen n R → EuclideanSpace ℝ (Fin n))
      (𝓝 ⟨x, mem_exteriorOpen.mpr hx⟩) = 𝓝 x :=
    (exteriorOpen n R).isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, mem_exteriorOpen.mpr hx⟩
  have hmem : {y : EuclideanSpace ℝ (Fin n) | ∃ hy : R < ‖y‖,
      φ₁ =ᶠ[𝓝 (⟨y, mem_exteriorOpen.mpr hy⟩ : exteriorOpen n R)] φ₂} ∈ 𝓝 x := by
    rw [← hmap, Filter.mem_map]
    filter_upwards [h.eventuallyEq_nhds] with z hz
    exact ⟨mem_exteriorOpen.mp z.2, hz⟩
  filter_upwards [hmem] with y ⟨hy, hy'⟩
  exact exteriorMetricCoeff_congr_nhds hy hy' i j

/-- At an exterior point `R < ‖x‖` where `mfderiv` is injective, every diagonal exterior metric
coefficient is strictly positive. -/
theorem exteriorMetricCoeff_diag_pos {R : ℝ} {φ : exteriorOpen n R → M}
    {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖)
    (hinj : Injective (mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩)) (i : Fin n) :
    0 < exteriorMetricCoeff φ x i i := by
  let z : exteriorOpen n R := ⟨x, mem_exteriorOpen.mpr hx⟩
  let e : TangentSpace (𝓡 n) z ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (TauCeti.Manifold.tangentSpaceOpenEquiv z).trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) x)
  let L := (mfderiv (𝓡 n) (𝓡 n) φ z).comp e.symm.toContinuousLinearMap
  have hpos : 0 < ⟪L (EuclideanSpace.basisFun (Fin n) ℝ i),
      L (EuclideanSpace.basisFun (Fin n) ℝ i)⟫ :=
    real_inner_self_pos.mpr
      ((map_ne_zero_iff L (hinj.comp e.symm.injective)).mpr
        ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.ne_zero i))
  dsimp only [L, e, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_trans_apply] at hpos
  rw [TauCeti.Manifold.tangentSpaceOpenEquiv_symm_apply,
    NormedSpace.fromTangentSpace_symm_apply] at hpos
  rwa [exteriorMetricCoeff_of_lt φ hx]

/-- Restricting an ambient map `φ : ℝⁿ → M` to `exteriorOpen n R` gives the same metric
coefficients at every point of `{x : R < ‖x‖}`. -/
@[simp] theorem exteriorMetricCoeff_comp_subtypeVal_of_lt {R : ℝ}
    (φ : EuclideanSpace ℝ (Fin n) → M) {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖)
    (i j : Fin n) :
    exteriorMetricCoeff (φ ∘ (Subtype.val : exteriorOpen n R → EuclideanSpace ℝ (Fin n))) x i j =
      pullbackMetricCoeff φ x i j := by
  rw [exteriorMetricCoeff_of_lt _ hx, pullbackMetricCoeff_def]
  exact congrArg₂ (inner ℝ)
    (TauCeti.Manifold.mfderiv_comp_subtype_val_apply (U := exteriorOpen n R) _)
    (TauCeti.Manifold.mfderiv_comp_subtype_val_apply (U := exteriorOpen n R) _)

/-- Near any point `x` with `R < ‖x‖`, `exteriorMetricCoeff (φ ∘ Subtype.val)` and
`pullbackMetricCoeff φ` agree on a neighbourhood of `x`. -/
theorem eventuallyEq_exteriorMetricCoeff_comp_subtypeVal {R : ℝ}
    (φ : EuclideanSpace ℝ (Fin n) → M) {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖)
    (i j : Fin n) :
    (fun y =>
      exteriorMetricCoeff (φ ∘ (Subtype.val : exteriorOpen n R → EuclideanSpace ℝ (Fin n))) y i j)
      =ᶠ[𝓝 x] (fun y => pullbackMetricCoeff φ y i j) := by
  filter_upwards [(exteriorOpen n R).isOpen.mem_nhds (mem_exteriorOpen.mpr hx)] with y hy
  exact exteriorMetricCoeff_comp_subtypeVal_of_lt φ (mem_exteriorOpen.mp hy) i j

/-- Restricting a map `φ : exteriorOpen n R → M` along `Opens.inclusion` from a smaller exterior
`exteriorOpen n R'` (`R ≤ R'`) preserves its metric coefficients at every point with `R' < ‖x‖`. -/
@[simp] theorem exteriorMetricCoeff_comp_inclusion_of_lt {R R' : ℝ} (hR : R ≤ R')
    (φ : exteriorOpen n R → M) {x : EuclideanSpace ℝ (Fin n)} (hx : R' < ‖x‖) (i j : Fin n) :
    exteriorMetricCoeff (φ ∘ Opens.inclusion (exteriorOpen_anti hR)) x i j =
      exteriorMetricCoeff φ x i j := by
  rw [exteriorMetricCoeff_of_lt _ hx, exteriorMetricCoeff_of_lt _ (hR.trans_lt hx)]
  exact congrArg₂ (inner ℝ)
    (TauCeti.Manifold.mfderiv_comp_inclusion_apply (exteriorOpen_anti hR) _)
    (TauCeti.Manifold.mfderiv_comp_inclusion_apply (exteriorOpen_anti hR) _)

end ExteriorMetricCoeff

end TauCeti
