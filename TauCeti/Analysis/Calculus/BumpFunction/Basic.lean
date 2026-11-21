/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Bump functions with support in a ball

On a real normed space with smooth bump functions, every open ball contains the topological
support of a smooth bump function centred at its centre. Multiplying the identity by such a bump
gives a smooth map into the ball that is the identity near its centre; composing with it turns a
map defined only on a ball into a globally defined map with the same germ at the centre.

A bump function centred at `0` can be dilated by any factor `c > 0`: scaling both radii by `c`
gives the bump function `ξ ↦ φ (c⁻¹ • ξ)`.

## Main results

* `TauCeti.exists_contDiffBump_tsupport_subset_ball`: a bump centred at `c` whose topological
  support lies in the ball of radius `r` around `c`.
* `TauCeti.exists_contDiff_eventuallyEq_id_forall_mem_ball`: a smooth map into the ball of radius
  `r` about `0` which is the identity near `0`.
* `ContDiffBump.dilate`: the dilation of a bump function centred at `0` by a factor `c > 0`, with
  `ContDiffBump.dilate_apply`: its value at `ξ` is `φ (c⁻¹ • ξ)`.
-/

public section

open Metric Filter
open scoped ContDiff Topology

namespace TauCeti

/-- A smooth bump function centred at `c` whose topological support lies in the ball of radius
`r > 0` around `c`. -/
theorem exists_contDiffBump_tsupport_subset_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [HasContDiffBump E] (c : E) {r : ℝ} (hr : 0 < r) :
    ∃ b : ContDiffBump c, tsupport b ⊆ ball c r :=
  -- the bump of radii `r / 4` and `r / 2`
  ⟨⟨r / 4, r / 2, by positivity, by linarith⟩, by
    rw [ContDiffBump.tsupport_eq]
    exact closedBall_subset_ball (half_lt_self hr)⟩

/-- A smooth self-map of a real normed space with smooth bump functions which is the identity near
`0` and takes values in the ball of radius `r > 0` about `0`. It is `x ↦ b(x) • x` for a bump `b`
equal to `1` near `0` and supported in that ball. -/
theorem exists_contDiff_eventuallyEq_id_forall_mem_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [HasContDiffBump E] {r : ℝ} (hr : 0 < r) :
    ∃ ρ : E → E, ContDiff ℝ ∞ ρ ∧ ρ =ᶠ[𝓝 0] id ∧ ∀ x, ρ x ∈ ball (0 : E) r := by
  let b : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨fun x ↦ b x • x, b.contDiff.smul contDiff_id, ?_, fun x ↦ ?_⟩
  · filter_upwards [b.eventuallyEq_one] with x hx
    simp [hx]
  · dsimp only
    rcases lt_or_ge ‖x‖ r with hx | hx
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg b.nonneg]
      exact (mul_le_of_le_one_left (norm_nonneg x) b.le_one).trans_lt hx
    · rw [b.zero_of_le_dist (by simpa using hx), zero_smul]
      exact mem_ball_self hr

end TauCeti

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E]

/-- The **dilation** of a bump function centred at `0` by a factor `c > 0`: the bump function with
radii `c * φ.rIn` and `c * φ.rOut`, whose value at `ξ` is `φ (c⁻¹ • ξ)`
(`ContDiffBump.dilate_apply`). -/
def dilate (φ : ContDiffBump (0 : E)) {c : ℝ} (hc : 0 < c) : ContDiffBump (0 : E) where
  rIn := c * φ.rIn
  rOut := c * φ.rOut
  rIn_pos := mul_pos hc φ.rIn_pos
  rIn_lt_rOut := mul_lt_mul_of_pos_left φ.rIn_lt_rOut hc

/-- The inner radius of `ContDiffBump.dilate`. -/
@[simp]
theorem dilate_rIn (φ : ContDiffBump (0 : E)) {c : ℝ} (hc : 0 < c) :
    (φ.dilate hc).rIn = c * φ.rIn :=
  (rfl)

/-- The outer radius of `ContDiffBump.dilate`. -/
@[simp]
theorem dilate_rOut (φ : ContDiffBump (0 : E)) {c : ℝ} (hc : 0 < c) :
    (φ.dilate hc).rOut = c * φ.rOut :=
  (rfl)

/-- The dilation of `φ` by `c` is `φ` evaluated at `c⁻¹ • ξ`. -/
@[simp]
theorem dilate_apply [NormedSpace ℝ E] [HasContDiffBump E] (φ : ContDiffBump (0 : E)) {c : ℝ}
    (hc : 0 < c) (ξ : E) : φ.dilate hc ξ = φ (c⁻¹ • ξ) := by
  have h₁ : (φ.dilate hc).rOut / (φ.dilate hc).rIn = φ.rOut / φ.rIn := by
    rw [dilate_rOut, dilate_rIn, mul_div_mul_left _ _ hc.ne']
  have h₂ : (φ.dilate hc).rIn⁻¹ = φ.rIn⁻¹ * c⁻¹ := by
    rw [dilate_rIn, mul_inv, mul_comm]
  simp only [ContDiffBump.apply, sub_zero, smul_smul, h₁, h₂]

end ContDiffBump
