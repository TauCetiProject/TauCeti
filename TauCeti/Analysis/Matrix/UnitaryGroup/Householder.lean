/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Householder
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smoothness of the Householder special unitary matrix

The special unitary matrix `Matrix.householderSpecialUnitary i j y` with `i`-th column `y` depends
smoothly on `y` on the open set `yᵢ ≠ 0`: its entries are built from the coordinates of `y`, their
conjugates, the phase `yᵢ / |yᵢ|` and `(1 + |yᵢ|)⁻¹`. As in `TauCeti.Analysis.Matrix.ContDiff`,
matrices carry the elementwise norm, so no matrix algebra norm is chosen.

## Main results

* `Matrix.contDiffOn_householderSpecialUnitary`: `y ↦ householderSpecialUnitary i j y` is smooth
  on `{y | y i ≠ 0}`.
* `Matrix.contDiffOn_householderSpecialUnitary_apply`: the same for each entry, a form that does
  not depend on a choice of norm on matrices.
-/

public section

open scoped ContDiff Matrix.Norms.Elementwise

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] {k : ℕ∞ω}

/-- Each entry of the special unitary matrix `Matrix.householderSpecialUnitary i j y` with `i`-th
column `y` depends smoothly on `y` where `yᵢ ≠ 0`. -/
theorem contDiffOn_householderSpecialUnitary_apply (i j l m : ι) :
    ContDiffOn ℝ k (fun y : ι → 𝕜 ↦ householderSpecialUnitary i j y l m) {y | y i ≠ 0} := by
  set s : Set (ι → 𝕜) := {y | y i ≠ 0}
  have hcoord (l : ι) : ContDiff ℝ k fun y : ι → 𝕜 ↦ y l := contDiff_apply ℝ (fun _ ↦ 𝕜) l
  have hnorm : ContDiffOn ℝ k (fun y : ι → 𝕜 ↦ ‖y i‖) s :=
    fun y hy ↦ ((contDiffAt_norm 𝕜 hy).comp y (hcoord i).contDiffAt).contDiffWithinAt
  have hphase : ContDiffOn ℝ k (fun y : ι → 𝕜 ↦ ‖y i‖⁻¹ • y i) s :=
    (hnorm.inv fun _ hy ↦ norm_ne_zero_iff.2 hy).smul (hcoord i).contDiffOn
  have hc : ContDiffOn ℝ k (fun y : ι → 𝕜 ↦ (1 + ‖y i‖)⁻¹) s :=
    (contDiffOn_const.add hnorm).inv fun _ _ ↦ by positivity
  have hstar {f : (ι → 𝕜) → 𝕜} (hf : ContDiffOn ℝ k f s) : ContDiffOn ℝ k (fun y ↦ star (f y)) s :=
    (RCLike.conjCLE (K := 𝕜)).contDiff.comp_contDiffOn hf
  have haxis (l : ι) : ContDiffOn ℝ k (fun y ↦ householderSpecialUnitaryAxis i y l) s := by
    simp only [householderSpecialUnitaryAxis_apply]
    exact (hphase.mul contDiffOn_const).add (hcoord l).contDiffOn
  have hdiag (l : ι) : ContDiffOn ℝ k (fun y ↦ householderSpecialUnitaryDiag i j y l) s := by
    simp only [householderSpecialUnitaryDiag_apply]
    split_ifs
    · exact hphase.neg
    · exact hstar hphase
    · exact contDiffOn_const
  simp only [householderSpecialUnitary_apply]
  exact (contDiffOn_const.sub (hc.smul ((haxis l).mul (hstar (haxis m))))).mul (hdiag m)

/-- The special unitary matrix `Matrix.householderSpecialUnitary i j y` with `i`-th column `y`
depends smoothly on `y` where `yᵢ ≠ 0`. -/
theorem contDiffOn_householderSpecialUnitary (i j : ι) :
    ContDiffOn ℝ k (householderSpecialUnitary (𝕜 := 𝕜) i j) {y | y i ≠ 0} :=
  contDiffOn_pi.2 fun l ↦ contDiffOn_pi.2 fun m ↦ contDiffOn_householderSpecialUnitary_apply i j l m

end Matrix
