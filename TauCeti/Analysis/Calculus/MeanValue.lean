/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact

/-!
# Consequences of the mean value theorem

## Escaping a superlevel set at bounded speed

Let `w` be a differentiable real function on a real normed space whose derivative has norm at
most `L` on the band `{a ≤ w ≤ b}`. Starting from a point where `w ≥ b`, the function cannot reach
the level `a` within distance `(b - a) / L` (`TauCeti.lt_apply_add_of_norm_fderiv_le`).

Mathlib's `Convex.norm_image_sub_le_of_norm_fderiv_le` needs the derivative bound along the
whole segment; here it is only assumed on the band, which is what is available near a level set
of a function whose gradient is controlled only there. The proof applies the one-variable mean
value theorem on the part of the segment where the function crosses the band.

## Invariance along a direction

Over `ℝ` or `ℂ`, a map whose derivative kills a vector `v` at every point `z + t • v` with
`‖t‖ ≤ 1` takes the same value at `z` and `z + v`
(`TauCeti.apply_add_eq_of_fderiv_apply_eq_zero`). Unlike Mathlib's
`Convex.is_const_of_fderivWithin_eq_zero`, only the derivative in the direction `v` is assumed to
vanish, so the map need not be constant near the segment.
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If the derivative of `w` has norm at most `L` wherever `a ≤ w ≤ b`, then `w` stays above `a`
at distance less than `(b - a) / L` from every point where `w ≥ b`. -/
theorem lt_apply_add_of_norm_fderiv_le {w : E → ℝ} (hw : Differentiable ℝ w)
    {a b L : ℝ} (hL : 0 ≤ L) (hbound : ∀ x, a ≤ w x → w x ≤ b → ‖fderiv ℝ w x‖ ≤ L) {x z : E}
    (hx : b ≤ w x) (hz : L * ‖z‖ < b - a) : a < w (x + z) := by
  by_contra! h
  -- Along the segment from `x` to `x + z`, let `s₁` be the first time with `w ≤ a` and `s₀` the
  -- last earlier time with `w ≥ b`. Strictly between them `a < w < b`, so the derivative bound
  -- applies there, and the mean value theorem gives a contradiction.
  let f : ℝ → ℝ := fun s => w (x + s • z)
  have hfd (s : ℝ) : HasDerivAt f (fderiv ℝ w (x + s • z) z) s := by
    have hline : HasDerivAt (fun s : ℝ => x + s • z) z s := by
      simpa using ((hasDerivAt_id s).smul_const z).const_add x
    exact (hw (x + s • z)).hasFDerivAt.comp_hasDerivAt s hline
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun s => (hfd s).continuousAt
  have hab : a < b := by nlinarith [norm_nonneg z]
  obtain ⟨s₁, ⟨⟨hs₁I, hs₁a⟩, hs₁⟩⟩ :=
    (isCompact_Icc.inter_right (isClosed_Iic.preimage hfc)).exists_isLeast
      (⟨1, right_mem_Icc.2 zero_le_one, by simpa [f] using h⟩ :
        (Icc (0 : ℝ) 1 ∩ f ⁻¹' Iic a).Nonempty)
  obtain ⟨s₀, ⟨⟨hs₀I, hs₀b⟩, hs₀⟩⟩ :=
    (isCompact_Icc.inter_right (isClosed_Ici.preimage hfc)).exists_isGreatest
      (⟨0, left_mem_Icc.2 hs₁I.1, by simpa [f] using hx⟩ : (Icc 0 s₁ ∩ f ⁻¹' Ici b).Nonempty)
  simp only [mem_preimage, mem_Iic, mem_Ici] at hs₁a hs₀b
  have hlt : s₀ < s₁ :=
    lt_of_le_of_ne hs₀I.2 fun he => by rw [he] at hs₀b; linarith
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope f (fun s => fderiv ℝ w (x + s • z) z) hlt
    hfc.continuousOn fun s _ => hfd s
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hs₀I.1.trans hc.1.le, hc.2.le.trans hs₁I.2⟩
  have hca : a < f c := by
    by_contra! hca
    exact (hs₁ ⟨hcI, hca⟩).not_gt hc.2
  have hcb : f c < b := by
    by_contra! hcb
    exact (hs₀ ⟨⟨hcI.1, hc.2.le⟩, hcb⟩).not_gt hc.1
  have hd : -(L * ‖z‖) ≤ fderiv ℝ w (x + c • z) z := by
    have := ((fderiv ℝ w (x + c • z)).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (hbound _ hca.le hcb.le) (norm_nonneg z))
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (fderiv ℝ w (x + c • z) z)]
  have hpos : 0 < s₁ - s₀ := sub_pos.2 hlt
  have hslope : f s₁ - f s₀ = fderiv ℝ w (x + c • z) z * (s₁ - s₀) := by
    rw [hcd, div_mul_cancel₀ _ hpos.ne']
  have : -(L * ‖z‖) ≤ f s₁ - f s₀ := by
    rw [hslope]
    nlinarith [mul_nonneg hL (norm_nonneg z), hs₀I.1, hs₁I.2]
  linarith

section Direction

variable {𝕂 : Type*} [RCLike 𝕂] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕂 G]

/-- If `g` is differentiable at every point `z + t • v` with `‖t‖ ≤ 1` and its derivative kills `v`
there, then `g` takes the same value at `z` and at `z + v`. -/
theorem apply_add_eq_of_fderiv_apply_eq_zero {g : F → G} {z v : F}
    (hg : ∀ t : 𝕂, ‖t‖ ≤ 1 → DifferentiableAt 𝕂 g (z + t • v))
    (hv : ∀ t : 𝕂, ‖t‖ ≤ 1 → fderiv 𝕂 g (z + t • v) v = 0) : g (z + v) = g z := by
  -- The restriction of `g` to the line through `z` in direction `v` has zero derivative on the
  -- closed unit disc, which is convex and contains `0` and `1`.
  have hq : ∀ t ∈ Metric.closedBall (0 : 𝕂) 1, HasFDerivWithinAt (fun t : 𝕂 ↦ g (z + t • v))
      ((fderiv 𝕂 g (z + t • v)).comp ((ContinuousLinearMap.id 𝕂 𝕂).smulRight v))
      (Metric.closedBall 0 1) t := fun t ht ↦
    ((hg t (by simpa using ht)).hasFDerivAt.comp t
      ((hasFDerivAt_id t).smul_const v |>.const_add z)).hasFDerivWithinAt
  have h := (convex_closedBall (0 : 𝕂) 1).norm_image_sub_le_of_norm_hasFDerivWithin_le hq
    (C := 0) (fun t ht ↦ by
      rw [norm_le_zero_iff]
      ext
      simp [hv t (by simpa using ht)])
    (Metric.mem_closedBall_self zero_le_one) (show (1 : 𝕂) ∈ Metric.closedBall 0 1 by simp)
  simpa [sub_eq_zero] using h

end Direction

end TauCeti
