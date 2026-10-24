/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Norm comparisons passing to derivatives

If two continuous linear images of the increments of a map near `x` satisfy a norm comparison
`‖L (φ y - φ x)‖ ≤ A * ‖M (φ y - φ x)‖`, then so do the corresponding images of its derivative at
`x`. For instance, tangent vectors to a set whose points have heights bounded by `A` times the
distances of their base points obey the same bound.
-/

public section

open Filter Topology

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- A norm comparison `‖L (φ y - φ x)‖ ≤ A * ‖M (φ y - φ x)‖` between two continuous linear images
of the increments of `φ` near `x` passes to its derivative `φ'` at `x`. -/
theorem HasFDerivAt.norm_apply_le_mul_norm_apply {φ : E → F} {φ' : E →L[𝕜] F} {x : E}
    (hφ : HasFDerivAt φ φ' x) {L : F →L[𝕜] G} {M : F →L[𝕜] H} {A : ℝ}
    (h : ∀ᶠ y in 𝓝 x, ‖L (φ y - φ x)‖ ≤ A * ‖M (φ y - φ x)‖) (k : E) :
    ‖L (φ' k)‖ ≤ A * ‖M (φ' k)‖ := by
  -- Differentiate along the line `s ↦ φ (x + s • k)` and pass to the limit in the slopes.
  have hline : HasDerivAt (fun s : 𝕜 ↦ x + s • k) k 0 := by
    simpa using (HasDerivAt.smul_const (hasDerivAt_id (0 : 𝕜)) k).const_add x
  have hγ : HasDerivAt (fun s : 𝕜 ↦ φ (x + s • k)) (φ' k) 0 := by
    have : HasFDerivAt φ φ' (x + (0 : 𝕜) • k) := by simpa using hφ
    exact this.comp_hasDerivAt (0 : 𝕜) hline
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hγ
  have hmem : ∀ᶠ s in 𝓝[≠] (0 : 𝕜),
      ‖L (φ (x + s • k) - φ x)‖ ≤ A * ‖M (φ (x + s • k) - φ x)‖ :=
    nhdsWithin_le_nhds (hline.continuousAt.tendsto.eventually
      (p := fun y ↦ ‖L (φ y - φ x)‖ ≤ A * ‖M (φ y - φ x)‖) (by simpa using h))
  refine le_of_tendsto_of_tendsto (((L.continuous.tendsto _).comp hslope).norm)
    ((((M.continuous.tendsto _).comp hslope).norm).const_mul A) ?_
  filter_upwards [hmem] with s hs
  simp only [zero_add, zero_smul, add_zero, Function.comp_apply, map_smul, norm_smul]
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left hs (norm_nonneg _)
