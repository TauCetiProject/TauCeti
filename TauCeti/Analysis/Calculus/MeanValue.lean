/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.Compact

/-!
# Mean value estimates

## A directional mean value inequality

The mean value inequality only needs control of the derivative in the direction of the
chord being estimated, not an operator norm bound. This is useful on lower-dimensional
simplices, where derivatives are determined only on tangent directions, and when estimating
a parametrized map in terms of the size of its geometric chord.

The argument follows Mathlib's `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`,
using its one-variable mean value inequality along the same line segment.

## Escaping a superlevel set at bounded speed

Let `w` be a differentiable real function on a real normed space whose derivative has norm at
most `L` on the band `{a ≤ w ≤ b}`. Starting from a point where `w ≥ b`, the function cannot reach
the level `a` within distance `(b - a) / L` (`TauCeti.lt_apply_add_of_norm_fderiv_le`).

Mathlib's `Convex.norm_image_sub_le_of_norm_fderiv_le` needs the derivative bound along the
whole segment; here it is only assumed on the band, which is what is available near a level set
of a function whose gradient is controlled only there. The proof applies the one-variable mean
value theorem on the part of the segment where the function crosses the band.

The file also records the one-variable form of Mathlib's
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`, bounding the increment of a function
against a fixed derivative `φ` (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le'`).

For a function on the real line with derivative of norm at most `D r ^ (β - 1)` at every `r > 0`,
where `0 ≤ β ≤ 1`, the increments satisfy `‖u b - u a‖ ≤ 2 D |b - a| a ^ (β - 1)` for `a > 0` and
`a / 2 ≤ b` (`TauCeti.norm_sub_le_mul_abs_sub_mul_rpow_of_hasDerivAt`).

## Comparing maps with nearby derivatives

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

namespace Convex

/-- The mean value inequality with a bound only in the direction of the chord. The bound
is needed only on the segment joining the endpoints. In particular, neither an operator norm
bound nor a full-dimensional domain is required. Derivatives may be taken over a real or
complex scalar field. -/
theorem norm_image_sub_le_of_norm_hasFDerivWithin_apply_le
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set E} {f : E → F}
    {f' : E → E →L[𝕜] F} {x y : E} {C : ℝ} (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, HasFDerivWithinAt f (f' z) s z)
    (hbound : ∀ z ∈ segment ℝ x y, ‖f' z (y - x)‖ ≤ C)
    (hx : x ∈ s) (hy : y ∈ s) : ‖f y - f x‖ ≤ C := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  let γ : ℝ → E := AffineMap.lineMap x y
  have hγ : MapsTo γ (Icc 0 1) s := hs.mapsTo_lineMap hx hy
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (f ∘ γ) (f' (γ t) (y - x)) (Icc 0 1) t := by
    intro t ht
    simpa only [ContinuousLinearMap.coe_restrictScalars'] using
      ((hf _ (hγ ht)).restrictScalars ℝ).comp_hasDerivWithinAt t
        AffineMap.hasDerivWithinAt_lineMap hγ
  have hb : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' (γ t) (y - x)‖ ≤ C := by
    intro t ht
    exact hbound _ (lineMap_mem_segment ℝ _ _ (Ico_subset_Icc_self ht))
  simpa [γ] using norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb

end Convex

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

open Real in
/-- Mean value bound near `a > 0`: if `u` has derivative `f' r` of norm at most `D r^(β - 1)` at
every `r > 0` (`0 ≤ β ≤ 1`), then `‖u b - u a‖ ≤ 2 D |b - a| a^(β - 1)` for `a / 2 ≤ b`. -/
theorem norm_sub_le_mul_abs_sub_mul_rpow_of_hasDerivAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u f' : ℝ → F} {β D : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β - 1 ≤ 0)
    (hD : 0 ≤ D)
    (hderiv : ∀ r, 0 < r → HasDerivAt u (f' r) r) (hbound : ∀ r, 0 < r → ‖f' r‖ ≤ D * r ^ (β - 1))
    {a b : ℝ} (ha : 0 < a) (hb : a / 2 ≤ b) : ‖u b - u a‖ ≤ 2 * D * (|b - a| * a ^ (β - 1)) := by
  have ha2 : 0 < a / 2 := half_pos ha
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := u) (s := Ici (a / 2))
    (f' := f') (C := D * (a / 2) ^ (β - 1))
    (fun r hr => (hderiv r (ha2.trans_le hr)).hasDerivWithinAt)
    (fun r hr => (hbound r (ha2.trans_le hr)).trans
      (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos ha2 hr hβ₁) hD))
    (convex_Ici _) (x := a) (y := b) (mem_Ici.2 (by linarith)) (mem_Ici.2 hb)
  have hhalf : (a / 2) ^ (β - 1) ≤ 2 * a ^ (β - 1) := by
    rw [div_rpow ha.le zero_le_two, div_eq_mul_inv, ← rpow_neg zero_le_two, neg_sub, mul_comm]
    gcongr
    calc (2 : ℝ) ^ (1 - β) ≤ 2 ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 2 := rpow_one 2
  rw [Real.norm_eq_abs] at hmv
  calc ‖u b - u a‖ ≤ D * (a / 2) ^ (β - 1) * |b - a| := hmv
    _ ≤ D * (2 * a ^ (β - 1)) * |b - a| := by gcongr
    _ = _ := by ring

end TauCeti

namespace Convex

variable {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f f' : 𝕜 → G} {s : Set 𝕜} {x y : 𝕜}

/-- Variant of the mean value inequality on a convex set in dimension 1, using a bound on the
difference between the derivative and a fixed vector `φ`, rather than a bound on the derivative
itself. Version with `HasDerivWithinAt`. -/
theorem norm_image_sub_le_of_norm_hasDerivWithin_le' {φ : G} {C : ℝ}
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x - φ‖ ≤ C)
    (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x - (y - x) • φ‖ ≤ C * ‖y - x‖ := by
  have key := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun z ↦ f z - z • φ)
    (fun z hz ↦ ((hf z hz).sub ((hasDerivWithinAt_id z s).smul_const φ)).congr_deriv
      (by rw [one_smul])) bound xs ys
  convert key using 2
  rw [sub_smul]
  abel

end Convex

namespace ContDiff

open Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lipschitz bound for a jointly `C¹` family on a box.** If `Γ t s` is `C¹` in `(t, s)`, there is
a constant `B` such that `‖Γ t₁ s₁ - Γ t₂ s₂‖ ≤ B * max |t₁ - t₂| |s₁ - s₂|` for all `t₁, t₂` in
`[t₀, t₁']` and all `s₁, s₂` in `[a, b]`. -/
theorem exists_norm_sub_le_mul_max_uncurry {Γ : ℝ → ℝ → E} (hΓ : ContDiff ℝ 1 (uncurry Γ))
    (t₀ t₀' a b : ℝ) :
    ∃ B : NNReal, ∀ ⦃x₁ y₁ x₂ y₂ : ℝ⦄, x₁ ∈ Icc t₀ t₀' → y₁ ∈ Icc a b → x₂ ∈ Icc t₀ t₀' →
      y₂ ∈ Icc a b → ‖Γ x₁ y₁ - Γ x₂ y₂‖ ≤ B * max |x₁ - x₂| |y₁ - y₂| := by
  have hQc : IsCompact (Icc t₀ t₀' ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hQv : Convex ℝ (Icc t₀ t₀' ×ˢ Icc a b) := (convex_Icc _ _).prod (convex_Icc _ _)
  obtain ⟨B, hB⟩ := hΓ.contDiffOn.exists_lipschitzOnWith one_ne_zero hQv hQc
  refine ⟨B, fun x₁ y₁ x₂ y₂ hx₁ hy₁ hx₂ hy₂ ↦ ?_⟩
  have := hB.dist_le_mul (x := (x₁, y₁)) (y := (x₂, y₂)) ⟨hx₁, hy₁⟩ ⟨hx₂, hy₂⟩
  simpa [dist_eq_norm, Prod.dist_eq, Real.dist_eq] using this

end ContDiff
