/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Order.Interval.Set.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.Lattice

/-!
# Piecewise-linear radial cutoff

The piecewise-linear cutoff of radius `R > 0`, defined by
`TauCeti.radialLinearCutoff R t = max 0 (min 1 (2 - 2 * t / R))`, takes values in `[0, 1]`,
equals `1` for `t ≤ R / 2`, vanishes for `R ≤ t`, is continuous in `t`, and satisfies
`‖radialLinearCutoff R t • v - v‖ ≤ ‖v‖` in any real seminormed space.

## Main definitions

* `TauCeti.radialLinearCutoff`: the piecewise-linear cutoff `max 0 (min 1 (2 - 2 * t / R))`.

## Main results

* `TauCeti.radialLinearCutoff_mem_Icc`: `radialLinearCutoff R t ∈ Set.Icc 0 1`.
* `TauCeti.radialLinearCutoff_eq_one`: `radialLinearCutoff R t = 1` for `0 < R` and `t ≤ R / 2`.
* `TauCeti.radialLinearCutoff_eq_zero`: `radialLinearCutoff R t = 0` for `0 < R` and `R ≤ t`.
* `TauCeti.continuous_radialLinearCutoff`: `t ↦ radialLinearCutoff R t` is continuous.
* `TauCeti.norm_radialLinearCutoff_smul_sub_le`: `‖radialLinearCutoff R t • v - v‖ ≤ ‖v‖`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/New/Spanning/Bessel/CutTailBound.lean`,
declarations `New.besselCutoff`, `New.besselCutoff_mem_Icc`, `New.besselCutoff_eq_one`,
`New.besselCutoff_eq_zero`, and `New.enorm_besselCut_sub_le`.
-/

public section

open Set

namespace TauCeti

/-- The piecewise-linear radial cutoff of radius `R`: it is `1` for `t ≤ R / 2`, `0` for `R ≤ t`
(when `0 < R`), and linear in between. -/
noncomputable def radialLinearCutoff (R t : ℝ) : ℝ :=
  max 0 (min 1 (2 - 2 * t / R))

/-- The radial linear cutoff always takes values in `[0, 1]`. -/
theorem radialLinearCutoff_mem_Icc (R t : ℝ) : radialLinearCutoff R t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left .., max_le zero_le_one (min_le_left ..)⟩

/-- For `0 < R` and `t ≤ R / 2`, the radial linear cutoff equals `1`. -/
theorem radialLinearCutoff_eq_one {R t : ℝ} (hR : 0 < R) (ht : t ≤ R / 2) :
    radialLinearCutoff R t = 1 := by
  have h_le : 2 * t / R ≤ 1 := (div_le_one hR).mpr (by linarith)
  rw [radialLinearCutoff, min_eq_left (by linarith), max_eq_right zero_le_one]

/-- For `0 < R` and `R ≤ t`, the radial linear cutoff vanishes. -/
theorem radialLinearCutoff_eq_zero {R t : ℝ} (hR : 0 < R) (ht : R ≤ t) :
    radialLinearCutoff R t = 0 := by
  have h_ge : 2 ≤ 2 * t / R := (le_div_iff₀ hR).mpr (by linarith)
  exact max_eq_left (min_le_of_right_le (by linarith))

/-- For any `R : ℝ`, the radial linear cutoff `t ↦ radialLinearCutoff R t` is continuous. -/
theorem continuous_radialLinearCutoff (R : ℝ) : Continuous (radialLinearCutoff R) := by
  unfold radialLinearCutoff
  fun_prop

/-- Truncating a vector `v` by `radialLinearCutoff R t` changes it by at most `‖v‖`. -/
theorem norm_radialLinearCutoff_smul_sub_le {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (R t : ℝ) (v : E) :
    ‖radialLinearCutoff R t • v - v‖ ≤ ‖v‖ := by
  obtain ⟨h0, h1⟩ := radialLinearCutoff_mem_Icc R t
  have h_sub : radialLinearCutoff R t • v - v = (radialLinearCutoff R t - 1) • v := by
    rw [sub_smul, one_smul]
  rw [h_sub, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  exact mul_le_of_le_one_left (norm_nonneg v) (by linarith)

end TauCeti
