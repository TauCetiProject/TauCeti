/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Log
import TauCeti.Analysis.Complex.UpperLogContinuity
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A branched double cover of the strip by the upper half-plane

Let `p`, `q` and `r` be real numbers with `q` strictly between `p` and `r`, that is
`0 < (q - p) * (r - q)`. The rational function `G w = (w - p) * (w - r) / (w - q)` is real on the
real line, has zeros at `p` and `r` and poles at `q` and `∞`, and maps the upper half-plane into
itself, because
`(G w).im = w.im * (1 + (q - p) * (r - q) / normSq (w - q))`
(`TauCeti.im_sub_mul_sub_div_sub`). So `Λ w = log (G w) / π` maps the upper half-plane
holomorphically into the strip `0 < z.im < 1`, and:

* `Λ` is continuous on the closed upper half-plane with `p`, `q` and `r` removed, and maps the
  real points other than `p`, `q` and `r` to the two boundary lines of the strip, according to the
  sign of `G`;
* `re (Λ w)` tends to `-∞` as `w` tends to `p` or to `r`, and to `+∞` as `w` tends to `q` or to
  infinity;
* every point `ζ` of the strip has exactly two preimages in the upper half-plane, except the image
  of `b = q + √((q - p) * (r - q)) * I`, which has exactly one
  (`TauCeti.ncard_inter_preimage_log_sub_mul_sub_div_sub_div_pi`). The preimages of `ζ` are the
  two roots of the quadratic `(w - p) * (w - r) = exp (π ζ) * (w - q)`; both lie in the upper
  half-plane, and they coincide exactly at the critical point `b` of `G`.

So `Λ` is a branched double cover of the strip by the upper half-plane, with one branch point. It
is the upper half-plane model of the holomorphic strips of Heegaard Floer homology whose domain
is a rectangle: the boundary of the half-plane, cut at `p`, `q`, `r` and `∞`, consists of four
arcs mapped alternately to the two boundary lines of the strip, with the two corners `p` and `r`
at the negative end and the two corners `q` and `∞` at the positive end.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. 159 (2004), 1027--1158.
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. 10 (2006),
  955--1097.
-/

public section

open Bornology Complex Filter Function Set Topology
open UpperHalfPlane (upperHalfPlaneSet)
open scoped Real

namespace TauCeti

/-- The imaginary part of `(w - p) * (w - r) / (w - q)` for real `p`, `q`, `r` and `w ≠ q`. When
`q` lies between `p` and `r` the factor `1 + (q - p) * (r - q) / normSq (w - q)` is positive, so
the map preserves the upper and the lower half-plane. -/
theorem im_sub_mul_sub_div_sub (p q r : ℝ) {w : ℂ} (hw : w ≠ q) :
    ((w - p) * (w - r) / (w - q)).im = w.im * (1 + (q - p) * (r - q) / normSq (w - q)) := by
  have hw' : w - q ≠ 0 := sub_ne_zero.mpr hw
  have key : (w - p) * (w - r) / (w - q) =
      (w - q) + ((2 * q - p - r : ℝ) : ℂ) + (((q - p) * (q - r) : ℝ) : ℂ) / (w - q) := by
    field_simp
    push_cast
    ring
  rw [key, add_im, add_im, ofReal_im, div_im, ofReal_im, ofReal_re, sub_im, ofReal_im]
  ring

/-- For `q` strictly between `p` and `r`, the factor in `TauCeti.im_sub_mul_sub_div_sub` is
positive. -/
private theorem one_add_div_normSq_pos {p q r : ℝ} (hq : 0 < (q - p) * (r - q)) (w : ℂ) :
    0 < 1 + (q - p) * (r - q) / normSq (w - q) :=
  add_pos_of_pos_of_nonneg one_pos (div_nonneg hq.le (normSq_nonneg _))

/-- The function `(w - p) * (w - r) / (w - q)` is nonzero away from `p`, `q` and `r`. -/
private theorem sub_mul_sub_div_sub_ne_zero {p q r : ℝ} {w : ℂ} (hp : w ≠ p) (hq : w ≠ q)
    (hr : w ≠ r) : (w - p) * (w - r) / (w - q) ≠ 0 :=
  div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hp) (sub_ne_zero.mpr hr)) (sub_ne_zero.mpr hq)

/-- The function `(w - p) * (w - r) / (w - q)` is continuous away from the pole `q`. -/
private theorem continuousAt_sub_mul_sub_div_sub (p r : ℝ) {q : ℝ} {w : ℂ} (hq : w ≠ q) :
    ContinuousAt (fun w : ℂ => (w - p) * (w - r) / (w - q)) w := by
  fun_prop (disch := exact sub_ne_zero.mpr hq)

/-- For `q` strictly between `p` and `r`, the map `w ↦ (w - p) * (w - r) / (w - q)` sends a point
`w ≠ q` to the upper half-plane exactly when `w` lies in the upper half-plane. -/
theorem im_sub_mul_sub_div_sub_pos_iff {p q r : ℝ} (hq : 0 < (q - p) * (r - q)) {w : ℂ}
    (hw : w ≠ q) : 0 < ((w - p) * (w - r) / (w - q)).im ↔ 0 < w.im := by
  rw [im_sub_mul_sub_div_sub p q r hw]
  exact mul_pos_iff_of_pos_right (one_add_div_normSq_pos hq w)

/-- The map `w ↦ log ((w - p) * (w - r) / (w - q)) / π` sends the upper half-plane into the strip
`0 < z.im < 1` when `q` lies strictly between `p` and `r`. -/
theorem mapsTo_log_sub_mul_sub_div_sub_div_pi {p q r : ℝ} (hq : 0 < (q - p) * (r - q)) :
    MapsTo (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π) upperHalfPlaneSet
      {z : ℂ | z.im ∈ Ioo 0 1} := by
  intro w hw
  have hG := (im_sub_mul_sub_div_sub_pos_iff hq (sub_ofReal_ne_zero_of_mem_upperHalfPlaneSet hw q
    |> sub_ne_zero.mp)).mpr hw
  have := bijOn_log_upperHalfPlaneSet.mapsTo hG
  simp only [mem_ofPred_eq, mem_Ioo, div_ofReal_im] at this ⊢
  exact ⟨div_pos this.1 Real.pi_pos, (div_lt_one Real.pi_pos).mpr this.2⟩

/-- The map `w ↦ log ((w - p) * (w - r) / (w - q)) / π` is holomorphic on the upper half-plane
when `q` lies strictly between `p` and `r`. -/
theorem differentiableOn_log_sub_mul_sub_div_sub_div_pi {p q r : ℝ}
    (hq : 0 < (q - p) * (r - q)) :
    DifferentiableOn ℂ (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π)
      upperHalfPlaneSet := by
  intro w hw
  have hwq := sub_ofReal_ne_zero_of_mem_upperHalfPlaneSet hw q
  have hG := (im_sub_mul_sub_div_sub_pos_iff hq (sub_ne_zero.mp hwq)).mpr hw
  have hd : DifferentiableAt ℂ (fun w : ℂ => (w - p) * (w - r) / (w - q)) w := by
    fun_prop (disch := exact hwq)
  exact ((hd.clog (mem_slitPlane_iff.mpr (.inr hG.ne'))).div_const _).differentiableWithinAt

/-- The map `w ↦ log ((w - p) * (w - r) / (w - q)) / π` is continuous on the closed upper
half-plane with the three points `p`, `q` and `r` removed, when `q` lies strictly between `p` and
`r`. On the real line the principal logarithm is approached from above. -/
theorem continuousOn_log_sub_mul_sub_div_sub_div_pi {p q r : ℝ} (hq : 0 < (q - p) * (r - q)) :
    ContinuousOn (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π)
      ({w : ℂ | 0 ≤ w.im} \ {(p : ℂ), (q : ℂ), (r : ℂ)}) := by
  -- `(w - p) * (w - r) / (w - q)` stays in the punctured closed upper half-plane, where the
  -- logarithm is continuous
  have hmaps : MapsTo (fun w : ℂ => (w - p) * (w - r) / (w - q))
      ({w : ℂ | 0 ≤ w.im} \ {(p : ℂ), (q : ℂ), (r : ℂ)}) {z : ℂ | 0 ≤ z.im ∧ z ≠ 0} := by
    rintro v ⟨hv, hvpqr⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hvpqr
    obtain ⟨hvp, hvq, hvr⟩ := hvpqr
    refine ⟨?_, sub_mul_sub_div_sub_ne_zero hvp hvq hvr⟩
    rw [im_sub_mul_sub_div_sub p q r hvq]
    exact mul_nonneg hv (one_add_div_normSq_pos hq v).le
  intro w hw
  have hwq : w ≠ q := fun h => hw.2 (by simp [h])
  exact ((continuousOn_log_im_nonneg_ne_zero _ (hmaps hw)).comp (x := w)
    (continuousAt_sub_mul_sub_div_sub p r hwq).continuousWithinAt hmaps).div_const _

/-- The map `w ↦ log ((w - p) * (w - r) / (w - q)) / π` sends the real points other than `p`, `q`
and `r` to the two boundary lines of the strip: to the line `z.im = 0` where
`(w - p) * (w - r) / (w - q)` is positive, and to the line `z.im = 1` where it is negative. -/
theorem mapsTo_log_sub_mul_sub_div_sub_div_pi_boundary (p q r : ℝ) :
    MapsTo (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π)
      ({w : ℂ | w.im = 0} \ {(p : ℂ), (q : ℂ), (r : ℂ)}) {z : ℂ | z.im = 0 ∨ z.im = 1} := by
  rintro w ⟨hw, hwpqr⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hwpqr
  obtain ⟨hwp, hwq, hwr⟩ := hwpqr
  have hwre : (w.re : ℂ) = w := conj_eq_iff_re.mp (conj_eq_iff_im.mpr hw)
  set t : ℝ := (w.re - p) * (w.re - r) / (w.re - q)
  have ht : (w - p) * (w - r) / (w - q) = (t : ℂ) := by
    rw [← hwre]
    simp only [t]
    push_cast
    ring
  have ht0 : t ≠ 0 := by
    have : (t : ℂ) ≠ 0 := ht ▸ sub_mul_sub_div_sub_ne_zero hwp hwq hwr
    exact_mod_cast this
  simp only [mem_ofPred_eq, ht, div_ofReal_im, log_im]
  rcases ht0.lt_or_gt with h | h
  · right
    rw [arg_ofReal_of_neg h, div_self Real.pi_ne_zero]
  · left
    rw [arg_ofReal_of_nonneg h.le, zero_div]

/-- Near any real point `a`, the function `(w - p) * (w - r) / (w - q)` is nonzero away from `a`. -/
private theorem eventually_sub_mul_sub_div_sub_ne_zero (p q r a : ℝ) :
    ∀ᶠ w : ℂ in 𝓝[≠] (a : ℂ), (w - p) * (w - r) / (w - q) ≠ 0 := by
  have hne (s : ℝ) : ∀ᶠ w : ℂ in 𝓝[≠] (a : ℂ), w ≠ s := by
    rcases eq_or_ne a s with rfl | h
    · exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds (by exact_mod_cast h))
  filter_upwards [hne p, hne q, hne r] with w hp hq hr
  exact sub_mul_sub_div_sub_ne_zero hp hq hr

/-- The real part of `w ↦ log ((w - p) * (w - r) / (w - q)) / π` tends to `-∞` at each of the
zeros `p` and `r`, provided that zero is not the pole `q`. -/
theorem tendsto_log_sub_mul_sub_div_sub_div_pi_comap_re_atBot {p q r : ℝ} {a : ℝ}
    (ha : a = p ∨ a = r) (haq : a ≠ q) :
    Tendsto (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π) (𝓝[≠] (a : ℂ))
      (comap re atBot) := by
  refine tendsto_comap_iff.mpr ?_
  have hG := continuousAt_sub_mul_sub_div_sub p r (w := a) (by exact_mod_cast haq)
  have hG0 : ((a : ℂ) - p) * ((a : ℂ) - r) / ((a : ℂ) - q) = 0 := by
    rcases ha with rfl | rfl <;> simp
  have hnorm : Tendsto (fun w : ℂ => ‖(w - p) * (w - r) / (w - q)‖) (𝓝[≠] (a : ℂ)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by
      simpa [hG0] using (hG.tendsto.mono_left nhdsWithin_le_nhds).norm,
      (eventually_sub_mul_sub_div_sub_ne_zero p q r a).mono fun w hw => norm_pos_iff.mpr hw⟩
  simpa [comp_def, div_ofReal_re, log_re] using
    (Real.tendsto_log_nhdsGT_zero.comp hnorm).atBot_div_const Real.pi_pos

/-- The real part of `w ↦ log ((w - p) * (w - r) / (w - q)) / π` tends to `+∞` at the pole `q`,
provided `q` is neither of the zeros `p` and `r`. -/
theorem tendsto_log_sub_mul_sub_div_sub_div_pi_comap_re_atTop {p q r : ℝ} (hpq : p ≠ q)
    (hqr : q ≠ r) :
    Tendsto (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π) (𝓝[≠] (q : ℂ))
      (comap re atTop) := by
  refine tendsto_comap_iff.mpr ?_
  have hnum : Tendsto (fun w : ℂ => ‖(w - p) * (w - r)‖) (𝓝[≠] (q : ℂ))
      (𝓝 ‖((q : ℂ) - p) * ((q : ℂ) - r)‖) :=
    (((continuous_id.sub continuous_const).mul (continuous_id.sub continuous_const)).norm.tendsto
      _).mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun w : ℂ => ‖w - q‖) (𝓝[≠] (q : ℂ)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using
      ((continuous_sub_right (q : ℂ)).norm.tendsto (q : ℂ)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun w hw => norm_pos_iff.mpr (sub_ne_zero.mpr hw)⟩
  have hpos : 0 < ‖((q : ℂ) - p) * ((q : ℂ) - r)‖ :=
    norm_pos_iff.mpr (mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hpq.symm))
      (sub_ne_zero.mpr (by exact_mod_cast hqr)))
  have hnorm : Tendsto (fun w : ℂ => ‖(w - p) * (w - r) / (w - q)‖) (𝓝[≠] (q : ℂ)) atTop :=
    (hnum.pos_mul_atTop hpos (tendsto_inv_nhdsGT_zero.comp hden)).congr fun w => by
      rw [comp_apply, norm_div, div_eq_mul_inv]
  simpa [comp_def, div_ofReal_re, log_re] using
    (Real.tendsto_log_atTop.comp hnorm).atTop_div_const Real.pi_pos

/-- The real part of `w ↦ log ((w - p) * (w - r) / (w - q)) / π` tends to `+∞` at infinity. -/
theorem tendsto_log_sub_mul_sub_div_sub_div_pi_cobounded (p q r : ℝ) :
    Tendsto (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π) (cobounded ℂ)
      (comap re atTop) := by
  refine tendsto_comap_iff.mpr ?_
  set A : ℝ := |p| + |q| + |r|
  have hA : 0 ≤ A := by positivity
  -- far out, `‖G w‖` is at least `(‖w‖ - A) / 2`
  have hlow : ∀ᶠ w : ℂ in cobounded ℂ,
      (‖w‖ - A) / 2 ≤ ‖(w - p) * (w - r) / (w - q)‖ := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop (3 * A + 1)] with w hw
    have hs (s : ℝ) (hs : |s| ≤ A) : ‖w‖ - A ≤ ‖w - s‖ :=
      (sub_le_sub_left (by simpa using hs) _).trans (norm_sub_norm_le w s)
    have hp := hs p (by simp only [A]; linarith [abs_nonneg q, abs_nonneg r])
    have hr := hs r (by simp only [A]; linarith [abs_nonneg p, abs_nonneg q])
    have hq : ‖w - q‖ ≤ ‖w‖ + A :=
      (norm_sub_le w q).trans (by
        rw [norm_real, Real.norm_eq_abs]
        simp only [A]
        linarith [abs_nonneg p, abs_nonneg r])
    have hq0 : 0 < ‖w - q‖ := by
      refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h => ?_)
      have : ‖w‖ ≤ A := by
        rw [h, norm_real, Real.norm_eq_abs]
        simp only [A]
        linarith [abs_nonneg p, abs_nonneg r]
      linarith
    rw [norm_div, norm_mul, le_div_iff₀ hq0]
    nlinarith [mul_le_mul hp hr (by linarith) (norm_nonneg _),
      mul_le_mul_of_nonneg_left hq (show 0 ≤ (‖w‖ - A) / 2 by linarith)]
  have hlin : Tendsto (fun w : ℂ => (‖w‖ - A) / 2) (cobounded ℂ) atTop :=
    (tendsto_atTop_add_const_right _ (-A) tendsto_norm_cobounded_atTop).atTop_div_const two_pos
  have hnorm := tendsto_atTop_mono' _ hlow hlin
  simpa [comp_def, div_ofReal_re, log_re] using
    (Real.tendsto_log_atTop.comp hnorm).atTop_div_const Real.pi_pos

/-! ### The fibres -/

/-- For `ζ` in the strip, the preimage of `ζ` in the upper half-plane under
`w ↦ log ((w - p) * (w - r) / (w - q)) / π` is the zero set of the quadratic
`w * w - (p + r + exp (π ζ)) * w + (p * r + exp (π ζ) * q)`: both roots lie in the upper
half-plane. -/
private theorem inter_preimage_log_sub_mul_sub_div_sub_div_pi {p q r : ℝ}
    (hq : 0 < (q - p) * (r - q)) {ζ : ℂ} (hζ : ζ ∈ {z : ℂ | z.im ∈ Ioo 0 1}) :
    upperHalfPlaneSet ∩ (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π) ⁻¹' {ζ} =
      {w : ℂ | w * w - (p + r + cexp (π * ζ)) * w + (p * r + cexp (π * ζ) * q) = 0} := by
  have hη : 0 < (cexp (π * ζ)).im := by
    simp only [exp_im, re_ofReal_mul, im_ofReal_mul]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi
      (mul_pos Real.pi_pos hζ.1) (by nlinarith [Real.pi_pos, hζ.2]))
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  ext w
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hw, hΛ⟩
    have hwq := sub_ofReal_ne_zero_of_mem_upperHalfPlaneSet hw q
    have hG0 : (w - p) * (w - r) / (w - q) ≠ 0 := fun h => by
      have := (im_sub_mul_sub_div_sub_pos_iff hq (sub_ne_zero.mp hwq)).mpr hw
      rw [h, zero_im] at this
      exact this.false
    have hl : log ((w - p) * (w - r) / (w - q)) = π * ζ := by
      rw [← hΛ, mul_div_cancel₀ _ hπ]
    have hG : (w - p) * (w - r) / (w - q) = cexp (π * ζ) := by
      rw [← exp_log hG0, hl]
    rw [div_eq_iff hwq] at hG
    linear_combination hG
  · intro hQ
    have hwq : w - q ≠ 0 := fun h => by
      have : ((q : ℂ) - p) * ((q : ℂ) - r) ≠ 0 := by
        have : (q - p) * (q - r) ≠ 0 := by nlinarith
        exact_mod_cast this
      exact this (by rw [sub_eq_zero.mp h] at hQ; linear_combination hQ)
    have hG : (w - p) * (w - r) / (w - q) = cexp (π * ζ) := by
      rw [div_eq_iff hwq]
      linear_combination hQ
    have hw : 0 < w.im := (im_sub_mul_sub_div_sub_pos_iff hq (sub_ne_zero.mp hwq)).mp (hG ▸ hη)
    refine ⟨hw, ?_⟩
    rw [hG, log_exp (by simp; nlinarith [Real.pi_pos, hζ.1])
      (by simp; nlinarith [Real.pi_pos, hζ.2]), mul_div_cancel_left₀ _ hπ]

/-- A root `w₁` of the quadratic of `inter_preimage_log_sub_mul_sub_div_sub_div_pi` is a double
root, `w₁ = (p + r + exp (π ζ)) - w₁`, exactly when `ζ` is the image of the branch point
`q + √((q - p) * (r - q)) * I`. -/
private theorem eq_sub_iff_eq_log_branch {p q r : ℝ} (hq : 0 < (q - p) * (r - q)) {ζ : ℂ}
    (hζ : ζ ∈ {z : ℂ | z.im ∈ Ioo 0 1}) {w₁ : ℂ}
    (hw₁ : w₁ * w₁ - (p + r + cexp (π * ζ)) * w₁ + (p * r + cexp (π * ζ) * q) = 0) :
    w₁ = (p + r + cexp (π * ζ)) - w₁ ↔ ζ = (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π)
      ((q : ℂ) + (√((q - p) * (r - q)) : ℝ) * I) := by
  have hfib := inter_preimage_log_sub_mul_sub_div_sub_div_pi hq hζ
  set η := cexp (π * ζ)
  set ρ : ℝ := √((q - p) * (r - q))
  have hρ : (ρ : ℂ) * ρ = (q - p) * (r - q) := by
    exact_mod_cast Real.mul_self_sqrt hq.le
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr hq
  have hw₁H : w₁ ∈ upperHalfPlaneSet ∩
      (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π) ⁻¹' {ζ} := by
    rw [hfib]
    exact hw₁
  constructor
  · intro h
    have hfac : (w₁ - q - ρ * I) * (w₁ - q + ρ * I) = 0 := by
      linear_combination (-1 : ℂ) * hw₁ + (w₁ - q) * h + hρ - (ρ : ℂ) * ρ * I_mul_I
    have hne : w₁ - q + ρ * I ≠ 0 := fun h0 => by
      have := congrArg im h0
      simp only [sub_im, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, mul_one,
        sub_zero, zero_im] at this
      linarith [hw₁H.1.out, hρ0]
    have hb : w₁ = q + ρ * I := by
      linear_combination (mul_eq_zero.mp hfac).resolve_right hne
    exact hb ▸ hw₁H.2.symm
  · intro h
    have hbH : (q : ℂ) + ρ * I ∈ upperHalfPlaneSet ∩
        (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π) ⁻¹' {ζ} :=
      ⟨by simp [upperHalfPlaneSet, hρ0], by simp [h]⟩
    rw [hfib] at hbH
    have hQ := hbH.out
    -- `σ = 2 b`, so the two roots `w₁` and `σ - w₁` are both `b`
    have hσ : p + r + η = 2 * (q + ρ * I) := by
      refine mul_right_cancel₀ (show (ρ : ℂ) * I ≠ 0 from
        mul_ne_zero (ofReal_ne_zero.mpr hρ0.ne') I_ne_zero) ?_
      linear_combination (-1 : ℂ) * hQ + hρ - (ρ : ℂ) * ρ * I_mul_I
    have hroots : (q + ρ * I - w₁) * (q + ρ * I - (p + r + η - w₁)) = 0 := by
      linear_combination hQ - hw₁
    rcases mul_eq_zero.mp hroots with h' | h'
    · linear_combination -hσ - 2 * h'
    · linear_combination hσ + 2 * h'

/-- **The fibres of the double cover.** Let `q` lie strictly between `p` and `r`, and let
`Λ w = log ((w - p) * (w - r) / (w - q)) / π`. Every point `ζ` of the strip `0 < z.im < 1` has
exactly two preimages under `Λ` in the upper half-plane, except the image of the branch point
`q + √((q - p) * (r - q)) * I`, which has exactly one. -/
theorem ncard_inter_preimage_log_sub_mul_sub_div_sub_div_pi {p q r : ℝ}
    (hq : 0 < (q - p) * (r - q)) {ζ : ℂ} (hζ : ζ ∈ {z : ℂ | z.im ∈ Ioo 0 1}) :
    (upperHalfPlaneSet ∩ (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π) ⁻¹' {ζ}).ncard =
      if ζ = (fun w : ℂ => log ((w - p) * (w - r) / (w - q)) / π)
          ((q : ℂ) + (√((q - p) * (r - q)) : ℝ) * I) then 1 else 2 := by
  rw [inter_preimage_log_sub_mul_sub_div_sub_div_pi hq hζ]
  set σ : ℂ := p + r + cexp (π * ζ)
  set P : ℂ := p * r + cexp (π * ζ) * q
  -- a root `w₁`; the other root is `σ - w₁`
  obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (discrim 1 (-σ) P)
  obtain ⟨w₁, hw₁⟩ := exists_quadratic_eq_zero one_ne_zero ⟨s, hs⟩
  have hroot : {w : ℂ | w * w - σ * w + P = 0} = {w₁, σ - w₁} := by
    ext w
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    rw [← sub_eq_zero (a := w) (b := w₁), ← sub_eq_zero (a := w) (b := σ - w₁), ← mul_eq_zero]
    constructor
    · intro h
      linear_combination h - hw₁
    · intro h
      linear_combination h + hw₁
  have hiff := eq_sub_iff_eq_log_branch hq hζ (w₁ := w₁) (by linear_combination hw₁)
  rw [hroot]
  split_ifs with h
  · rw [← hiff.mpr h, pair_eq_singleton, ncard_singleton]
  · exact ncard_pair fun h' => h (hiff.mp h')

end TauCeti
