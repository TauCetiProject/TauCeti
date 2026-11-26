/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Translates of large multiples in an open cone

Let `Γ` be an open subset of a real topological vector space which is closed under
multiplication by positive reals, such as an open cone of frequencies in microlocal analysis.
If `ξ ∈ Γ`, then `Γ` contains `t • ξ + w` for every fixed `w` and all sufficiently large `t`:
writing `t • ξ + w = t • (ξ + t⁻¹ • w)`, the vector `ξ + t⁻¹ • w` tends to `ξ`. Consequently a
function decaying like `1 / (1 + ‖η‖)` on such a set vanishes wherever it is constant along a
line `t ↦ t • ξ + w`; this is how lower bounds on wave front sets are proved.

## Main results

* `IsOpen.eventually_smul_add_mem`: an open set closed under positive scaling contains
  `t • ξ + w` for all large `t` whenever it contains `ξ`.
* `IsOpen.eq_zero_of_forall_smul_add_eq`: a function with `(1 + ‖η‖) ‖g η‖` bounded on an open
  cone around `ξ ≠ 0` vanishes wherever it is constant along a line `t ↦ t • ξ + w`.
-/

public section

open Filter Topology

namespace IsOpen

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E]

/-- An open set `Γ` containing `ξ` and closed under multiplication by positive reals contains
`t • ξ + w` for all sufficiently large `t`, since `t • ξ + w = t • (ξ + t⁻¹ • w)` and
`ξ + t⁻¹ • w` tends to `ξ`. -/
theorem eventually_smul_add_mem {Γ : Set E} (hΓ : IsOpen Γ) {ξ : E} (hξΓ : ξ ∈ Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) (w : E) : ∀ᶠ t : ℝ in atTop, t • ξ + w ∈ Γ := by
  have hlim : Tendsto (fun t : ℝ => ξ + t⁻¹ • w) atTop (𝓝 ξ) := by
    simpa using tendsto_const_nhds.add ((tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const w)
  filter_upwards [hlim (hΓ.mem_nhds hξΓ), eventually_gt_atTop 0] with t ht ht0
  simpa [smul_add, smul_smul, ht0.ne'] using hcone t ht0 _ ht

end IsOpen

namespace IsOpen

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- **Decay in a cone forces vanishing along lines.** Let `Γ` be an open cone containing a nonzero
`ξ`, and let `(1 + ‖η‖) ‖g η‖` be bounded on `Γ`. If `g` is constant along the line
`t ↦ t • ξ + w`, then the constant is zero: the line eventually lies in `Γ`, where
`‖g (t • ξ + w)‖ ≤ C / (1 + ‖t • ξ + w‖)` tends to `0`. Applied to a localized Fourier transform,
this shows that a distribution is not microlocally smooth. -/
theorem eq_zero_of_forall_smul_add_eq {g : E → F} {Γ : Set E} (hΓ : IsOpen Γ) {ξ : E}
    (hξΓ : ξ ∈ Γ) (hξ : ξ ≠ 0) (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) {C : ℝ}
    (hC : ∀ η ∈ Γ, (1 + ‖η‖) * ‖g η‖ ≤ C) {w : E} {c : F} (hc : ∀ t : ℝ, g (t • ξ + w) = c) :
    c = 0 := by
  have hξpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hgrow : Tendsto (fun t : ℝ => 1 + ‖t • ξ + w‖) atTop atTop := by
    refine tendsto_atTop_mono (fun t => ?_)
      (tendsto_atTop_add_const_right _ (-‖w‖) (tendsto_id.atTop_mul_const hξpos))
    have h := norm_sub_le (t • ξ + w) w
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs] at h
    have := mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg ξ)
    simp only [id]
    linarith
  refine norm_le_zero_iff.1 (ge_of_tendsto ((tendsto_const_nhds (x := C)).div_atTop hgrow) ?_)
  filter_upwards [hΓ.eventually_smul_add_mem hξΓ hcone w] with t ht
  have hbound := hC _ ht
  rw [hc] at hbound
  exact (le_div_iff₀' (by positivity)).2 hbound

end IsOpen
