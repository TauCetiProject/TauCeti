/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.Compact

/-!
# Mean value estimates

Let `w` be a differentiable real function on a real normed space whose derivative has norm at
most `L` on the band `{a ≤ w ≤ b}`. Starting from a point where `w ≥ b`, the function cannot reach
the level `a` within distance `(b - a) / L` (`TauCeti.lt_apply_add_of_norm_fderiv_le`).

Mathlib's `Convex.norm_image_sub_le_of_norm_fderiv_le` needs the derivative bound along the
whole segment; here it is only assumed on the band, which is what is available near a level set
of a function whose gradient is controlled only there. The proof applies the one-variable mean
value theorem on the part of the segment where the function crosses the band.

If two maps on a convex set have derivatives within `ε` of a common linear map and agree at a
point `y`, then by the mean value inequality applied to their difference they stay within
`2 ε ‖x - y‖` of each other (`Convex.norm_sub_le_of_norm_hasFDerivWithin_sub_le`).
This compares a map to a model agreeing with it to first order before splicing them together
(`TauCeti.Analysis.Calculus.Splice`).
-/

public section

/-- **Two maps with nearby derivatives that agree at a point stay close.** If the derivatives of
`k` and `l` on a convex set `S` are within `ε` of a fixed linear map `A`, and `k` and `l` agree at
`y ∈ S`, then `‖l x - k x‖ ≤ 2 ε ‖x - y‖` for every `x ∈ S`. -/
theorem Convex.norm_sub_le_of_norm_hasFDerivWithin_sub_le {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {S : Set X} (hS : Convex ℝ S)
    {k l : X → Y} {k' l' : X → X →L[ℝ] Y} {A : X →L[ℝ] Y} {ε : ℝ}
    (hk : ∀ x ∈ S, HasFDerivWithinAt k (k' x) S x) (hl : ∀ x ∈ S, HasFDerivWithinAt l (l' x) S x)
    (hk' : ∀ x ∈ S, ‖k' x - A‖ ≤ ε) (hl' : ∀ x ∈ S, ‖l' x - A‖ ≤ ε) {x y : X} (hx : x ∈ S)
    (hy : y ∈ S) (hxy : k y = l y) : ‖l x - k x‖ ≤ 2 * ε * ‖x - y‖ := by
  have h := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun v => l v - k v)
    (f' := fun v => l' v - k' v) (C := 2 * ε) (fun v hv => (hl v hv).sub (hk v hv))
    (fun v hv => (norm_sub_le_norm_sub_add_norm_sub (l' v) A (k' v)).trans
      (by rw [norm_sub_rev A]; linarith [hl' v hv, hk' v hv])) hy hx
  rwa [hxy, sub_self, sub_zero] at h

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

end TauCeti
