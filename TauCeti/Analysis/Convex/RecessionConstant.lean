/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The recession constant of a function on the half-line

The *recession constant* of `U : ℝ → ℝ` is the asymptotic slope `U'(∞) = lim_{s → ∞} U(s) / s`,
an extended real. It measures how `U` grows at infinity, and it is the coefficient that the internal
energy `∫ U(ρ) dm` of a measure assigns to its part singular with respect to the reference measure
`m`: concentrating mass `M` on an `m`-null set costs `U'(∞) M`.

The constant is defined as an upper limit (`TauCeti.recessionConstant`), so it exists for every
function. For `U` convex on `[0, ∞)` the slopes `(U s - U 0) / s` are monotone, so `U(s) / s`
genuinely converges to it (`ConvexOn.tendsto_div_recessionConstant`).

## Main definitions

* `TauCeti.recessionConstant U`: the upper limit of `U(s) / s` as `s → ∞`, in `EReal`.

## Main results

* `ConvexOn.tendsto_div_recessionConstant`: for `U` convex on `[0, ∞)`, `U(s) / s` tends to the
  recession constant.
* `TauCeti.recessionConstant_mul_log`: the recession constant of `r ↦ r log r` is `⊤`.
* `ConvexOn.apply_mul_le_of_forall_le`: a convex function on `(0, ∞)` bounded above by `L` stays
  convex when extended by the value `L` at `0`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §9.3.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 17.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace TauCeti

/-- The *recession constant* `U'(∞) = lim_{s → ∞} U(s) / s` of a function `U : ℝ → ℝ`, as an
extended real. It is defined as the upper limit of `U(s) / s`, so it exists for every `U`; for `U`
convex on `[0, ∞)` it is a genuine limit (`ConvexOn.tendsto_div_recessionConstant`). -/
def recessionConstant (U : ℝ → ℝ) : EReal :=
  limsup (fun s : ℝ ↦ ((U s / s : ℝ) : EReal)) atTop

/-- The defining formula of the recession constant, as the upper limit of `U(s) / s`. -/
theorem recessionConstant_def (U : ℝ → ℝ) :
    recessionConstant U = limsup (fun s : ℝ ↦ ((U s / s : ℝ) : EReal)) atTop :=
  (rfl)

/-- If `U(s) / s` tends to `L` as `s → ∞`, then `L` is the recession constant of `U`. -/
theorem recessionConstant_eq_of_tendsto {U : ℝ → ℝ} {L : EReal}
    (h : Tendsto (fun s : ℝ ↦ ((U s / s : ℝ) : EReal)) atTop (𝓝 L)) :
    recessionConstant U = L :=
  h.limsup_eq

/-- The recession constant of `r ↦ r log r` is `⊤`: its slopes `log s` are unbounded. -/
theorem recessionConstant_mul_log : recessionConstant (fun r ↦ r * Real.log r) = ⊤ := by
  refine recessionConstant_eq_of_tendsto <|
    (EReal.tendsto_coe_atTop.comp Real.tendsto_log_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp [mul_div_cancel_left₀ _ hs.ne']

end TauCeti

open TauCeti

/-- For `U` convex on `[0, ∞)`, `U(s) / s` tends to the recession constant of `U` as `s → ∞`. -/
theorem ConvexOn.tendsto_div_recessionConstant {U : ℝ → ℝ} (hU : ConvexOn ℝ (Ici 0) U) :
    Tendsto (fun s : ℝ ↦ ((U s / s : ℝ) : EReal)) atTop (𝓝 (recessionConstant U)) := by
  -- The secant slope from `0`, read off at times `≥ 1` so that it is monotone on all of `ℝ`.
  set g : ℝ → EReal := fun s ↦ (((U (max s 1) - U 0) / max s 1 : ℝ) : EReal) with hg_def
  have hg_mono : Monotone g := fun s t hst ↦ by
    have h₁ : (0 : ℝ) < max s 1 := lt_max_of_lt_right one_pos
    have h₂ := hU.secant_mono (a := 0) (x := max s 1) (y := max t 1) self_mem_Ici
      (mem_Ici.2 h₁.le) (mem_Ici.2 (h₁.trans_le (max_le_max_right 1 hst)).le) h₁.ne'
      (h₁.trans_le (max_le_max_right 1 hst)).ne' (max_le_max_right 1 hst)
    simp only [sub_zero] at h₂
    exact EReal.coe_le_coe_iff.2 h₂
  have hg : Tendsto g atTop (𝓝 (⨆ s, g s)) := tendsto_atTop_iSup hg_mono
  have h₀ : Tendsto (fun s : ℝ ↦ ((U 0 / s : ℝ) : EReal)) atTop (𝓝 0) := by
    rw [← EReal.coe_zero]
    exact EReal.tendsto_coe.2 (tendsto_const_nhds.div_atTop tendsto_id)
  have hsum : Tendsto (fun s : ℝ ↦ g s + ((U 0 / s : ℝ) : EReal)) atTop
      (𝓝 ((⨆ s, g s) + 0)) :=
    (EReal.continuousAt_add (Or.inr EReal.zero_ne_bot) (Or.inr EReal.zero_ne_top)).tendsto.comp
      (hg.prodMk_nhds h₀)
  rw [add_zero] at hsum
  have hlim : Tendsto (fun s : ℝ ↦ ((U s / s : ℝ) : EReal)) atTop (𝓝 (⨆ s, g s)) := by
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with s hs
    have hs₀ : s ≠ 0 := (one_pos.trans_le hs).ne'
    simp only [hg_def, max_eq_left hs, ← EReal.coe_add]
    congr 1
    field_simp
    ring
  rwa [recessionConstant_eq_of_tendsto hlim]

/-- A convex function `φ` on `(0, ∞)` bounded above by `L` satisfies `φ (b x) ≤ b φ x + (1 - b) L`
for `x > 0` and `0 < b ≤ 1`: extending `φ` by the value `L` at `0` keeps it convex on `[0, ∞)`.
For `φ(s) = sⁿ U(s⁻ⁿ)` nonincreasing, the best such bound is the recession constant of `U`, since
`U(r) / r = φ(r^{-1/n})`. -/
theorem ConvexOn.apply_mul_le_of_forall_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Ioi 0) φ)
    {L : ℝ} (hL : ∀ s ∈ Ioi (0 : ℝ), φ s ≤ L) {x b : ℝ} (hx : 0 < x) (hb₀ : 0 < b)
    (hb₁ : b ≤ 1) : φ (b * x) ≤ b * φ x + (1 - b) * L := by
  -- Write `b x` as a convex combination of `x` and `ε x` and let `ε → 0⁺`.
  set F : ℝ → ℝ := fun ε => (b - ε) / (1 - ε) * φ x + (1 - (b - ε) / (1 - ε)) * L
  have hF : Tendsto F (𝓝[>] 0) (𝓝 (b * φ x + (1 - b) * L)) := by
    have : ContinuousAt F 0 := by fun_prop (disch := norm_num)
    simpa [F] using this.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hF ?_
  filter_upwards [Ioo_mem_nhdsGT hb₀] with ε hε
  have hε1 : ε < 1 := hε.2.trans_le hb₁
  have hl₀ : 0 ≤ (b - ε) / (1 - ε) := div_nonneg (by linarith [hε.2]) (by linarith)
  have hl₁ : 0 ≤ 1 - (b - ε) / (1 - ε) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hne : 1 - ε ≠ 0 := by linarith
  have := hφ.2 (mem_Ioi.2 hx) (mem_Ioi.2 (mul_pos hε.1 hx)) hl₀ hl₁ (by ring)
  simp only [smul_eq_mul] at this
  rw [show (b - ε) / (1 - ε) * x + (1 - (b - ε) / (1 - ε)) * (ε * x) = b * x by
    field_simp; ring] at this
  have hεL := mul_le_mul_of_nonneg_left (hL _ (mul_pos hε.1 hx)) hl₁
  simp only [F]
  linarith
