/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The radial chart of the Euclidean unit ball in coordinates

The radial chart `z ↦ z / √(1 + ∑ j, z j ^ 2)` (`TauCeti.radialChart`) is an open partial
homeomorphism from `Fin n → ℝ` onto the open Euclidean unit ball `{z | ∑ j, z j ^ 2 < 1}`, with
inverse `z ↦ z / √(1 - ∑ j, z j ^ 2)`. It is Mathlib's `OpenPartialHomeomorph.univUnitBall` for the
Euclidean norm, read through `EuclideanSpace.equiv`, so it is smooth in both directions
(`TauCeti.contDiff_radialChart`, `TauCeti.contDiffOn_radialChart_symm`). It commutes with changes of
sign of the coordinates (`TauCeti.radialChart_smul`).
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

variable {n : ℕ}

/-- The radial chart `z ↦ (1 + ∑ j, z j ^ 2) ^ (-1 / 2) • z`, an open partial homeomorphism from
`Fin n → ℝ` onto the open Euclidean unit ball. It is `OpenPartialHomeomorph.univUnitBall` read
through `EuclideanSpace.equiv`. -/
noncomputable def radialChart : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ) :=
  ((EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.toOpenPartialHomeomorph.trans
    OpenPartialHomeomorph.univUnitBall).trans
    (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.toOpenPartialHomeomorph

/-- The radial chart is defined on all of `Fin n → ℝ`. -/
@[simp]
theorem radialChart_source : (radialChart (n := n)).source = univ := by
  simp only [radialChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  exact univ_inter _

/-- The radial chart is `OpenPartialHomeomorph.univUnitBall` read through
`EuclideanSpace.equiv`. -/
theorem coe_radialChart : ⇑(radialChart (n := n)) =
    EuclideanSpace.equiv (Fin n) ℝ ∘ OpenPartialHomeomorph.univUnitBall ∘
      (EuclideanSpace.equiv (Fin n) ℝ).symm := by
  simp only [radialChart, OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
    ContinuousLinearEquiv.coe_toHomeomorph]

/-- The inverse of the radial chart is `OpenPartialHomeomorph.univUnitBall.symm` read through
`EuclideanSpace.equiv`. -/
theorem coe_radialChart_symm : ⇑(radialChart (n := n)).symm =
    EuclideanSpace.equiv (Fin n) ℝ ∘ OpenPartialHomeomorph.univUnitBall.symm ∘
      (EuclideanSpace.equiv (Fin n) ℝ).symm := by
  simp only [radialChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_symm_apply,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, ContinuousLinearEquiv.symm_symm,
    Function.comp_assoc]

/-- The radial chart takes values in the open Euclidean unit ball. -/
@[simp]
theorem radialChart_target : (radialChart (n := n)).target = {z | ∑ j, z j ^ 2 < 1} := by
  ext z
  simp [radialChart, OpenPartialHomeomorph.univUnitBall_target, ← sq_lt_one_iff₀ (norm_nonneg _),
    EuclideanSpace.norm_sq_eq]

/-- The radial chart is `z ↦ z / √(1 + ∑ j, z j ^ 2)`. -/
@[simp]
theorem radialChart_apply (z : Fin n → ℝ) :
    radialChart z = (√(1 + ∑ j, z j ^ 2))⁻¹ • z := by
  simp [coe_radialChart, OpenPartialHomeomorph.univUnitBall_apply, EuclideanSpace.norm_sq_eq,
    PiLp.coe_continuousLinearEquiv]

/-- The inverse of the radial chart is `z ↦ z / √(1 - ∑ j, z j ^ 2)`. -/
@[simp]
theorem radialChart_symm_apply (z : Fin n → ℝ) :
    radialChart.symm z = (√(1 - ∑ j, z j ^ 2))⁻¹ • z := by
  simp [coe_radialChart_symm, OpenPartialHomeomorph.univUnitBall_symm_apply,
    EuclideanSpace.norm_sq_eq, PiLp.coe_continuousLinearEquiv]

/-- The radial chart is smooth. -/
theorem contDiff_radialChart : ContDiff ℝ ∞ (radialChart (n := n)) := by
  rw [coe_radialChart]
  exact (EuclideanSpace.equiv (Fin n) ℝ).contDiff.comp
    (OpenPartialHomeomorph.contDiff_univUnitBall.comp
      (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff)

/-- The inverse of the radial chart is smooth on the open unit ball. -/
theorem contDiffOn_radialChart_symm :
    ContDiffOn ℝ ∞ (radialChart (n := n)).symm radialChart.target := by
  have h : ContDiffOn ℝ ∞ ((EuclideanSpace.equiv (Fin n) ℝ) ∘
      OpenPartialHomeomorph.univUnitBall.symm ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm)
      ((EuclideanSpace.equiv (Fin n) ℝ).symm ⁻¹' Metric.ball 0 1) :=
    (EuclideanSpace.equiv (Fin n) ℝ).contDiff.comp_contDiffOn
      (OpenPartialHomeomorph.contDiffOn_univUnitBall_symm.comp
        (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.contDiffOn fun _ hz ↦ hz)
  refine h.congr_mono (fun z _ ↦ by rw [coe_radialChart_symm]) fun z hz ↦ ?_
  rw [radialChart_target, mem_ofPred_eq] at hz
  rw [mem_preimage, mem_ball_zero_iff, ← sq_lt_one_iff₀ (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, PiLp.continuousLinearEquiv_symm_apply]
  simpa only [WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs] using hz

/-- The radial chart commutes with changes of sign of the coordinates. -/
theorem radialChart_smul (δ : Fin n → ℤˣ) (z : Fin n → ℝ) :
    radialChart (δ • z) = δ • radialChart z := by
  have h : ∑ j, (δ • z) j ^ 2 = ∑ j, z j ^ 2 := Finset.sum_congr rfl fun j _ ↦ by
    rw [← sq_abs, ← Real.norm_eq_abs, Pi.smul_apply', norm_units_zsmul, Real.norm_eq_abs, sq_abs]
  rw [radialChart_apply, radialChart_apply, h, smul_comm]

end TauCeti
