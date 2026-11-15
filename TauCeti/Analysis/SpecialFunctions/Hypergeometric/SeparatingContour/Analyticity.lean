/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.SeparatingContour.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.Analysis.SpecialFunctions.Gamma.Order

/-!
# Canonical separating-contour continuation and joint four-variable holomorphy

This module defines the canonical abscissa-independent separating-contour Mellin–Barnes functional
`Complex.mellinBarnesContour` and proves its joint four-variable holomorphy
`Complex.analyticOnNhd_mellinBarnesContour` on
`{(a, b, c, z) | a ∉ -ℕ ∧ b ∉ -ℕ ∧ -z ∈ Complex.slitPlane}` across all lower parameters `c : ℂ`,
including resonant integer differences `a - b ∈ ℤ` where simple poles coalesce into double poles.

Locally around `(a₀, b₀, c₀, z₀)`, fixing `σ < 0` avoiding `-Re a₀ - ℕ` and `-Re b₀ - ℕ`, joint
holomorphy of the vertical integral follows from compact-segment holomorphy, uniform Stirling decay,
and Hartogs's theorem; joint holomorphy of the finite residue sum follows by rewriting it via
`TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg` as a sum of Cauchy
circle integrals around isolating circles.

## Main definitions and results

* `Complex.mellinBarnesContour`, `Complex.mellinBarnesContour_symm`,
  `Complex.mellinBarnesContour_eq_mellinBarnesSeparating`.
* `Complex.analyticOnNhd_mellinBarnesContour`: joint four-variable holomorphy in `(a, b, c, z)`.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Nat Real Topology

namespace Complex

private theorem abs_arg_lt_pi_of_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) : |w.arg| < π :=
  abs_lt.2 ⟨neg_pi_lt_arg w, lt_of_le_of_ne (arg_le_pi w) (slitPlane_arg_ne_pi hw)⟩

private theorem not_both_abscissa_poles {w : ℂ} {x₁ x₂ : ℝ}
    (hx₁ : -1 < x₁ ∧ x₁ < 0) (hx₂ : -1 < x₂ ∧ x₂ < 0) (hne : x₁ ≠ x₂)
    (h1 : ∃ k : ℕ, w.re + x₁ = -k) (h2 : ∃ k : ℕ, w.re + x₂ = -k) : False := by
  obtain ⟨k₁, hk₁⟩ := h1; obtain ⟨k₂, hk₂⟩ := h2
  have hdiff : (((k₂ : ℤ) - k₁ : ℤ) : ℝ) = x₁ - x₂ := by push_cast; linarith
  have hlt1 : (k₂ : ℤ) - k₁ < 1 := by exact_mod_cast (by linarith : (((k₂ : ℤ) - k₁ : ℤ) : ℝ) < 1)
  have hgt1 : (-1 : ℤ) < (k₂ : ℤ) - k₁ := by
    exact_mod_cast (by linarith : (-1 : ℝ) < (((k₂ : ℤ) - k₁ : ℤ) : ℝ))
  have hz : (k₂ : ℤ) - k₁ = 0 := by omega
  exact hne (by rw [hz, Int.cast_zero] at hdiff; linarith)

private noncomputable def mellinBarnesAbscissa (a b : ℂ) : ℝ :=
  open Classical in
  if (∀ k : ℕ, a.re + (-1 / 2 : ℝ) ≠ -k) ∧ (∀ k : ℕ, b.re + (-1 / 2 : ℝ) ≠ -k) then -1 / 2
  else if (∀ k : ℕ, a.re + (-1 / 4 : ℝ) ≠ -k) ∧ (∀ k : ℕ, b.re + (-1 / 4 : ℝ) ≠ -k) then -1 / 4
  else -3 / 4

private theorem mellinBarnesAbscissa_symm (a b : ℂ) :
    mellinBarnesAbscissa a b = mellinBarnesAbscissa b a := by
  classical simp only [mellinBarnesAbscissa, and_comm]

private theorem mellinBarnesAbscissa_lt_zero (a b : ℂ) : mellinBarnesAbscissa a b < 0 := by
  classical unfold mellinBarnesAbscissa; split_ifs <;> norm_num

private theorem mellinBarnesAbscissa_avoid (a b : ℂ) :
    (∀ k : ℕ, a.re + mellinBarnesAbscissa a b ≠ -k) ∧
      (∀ k : ℕ, b.re + mellinBarnesAbscissa a b ≠ -k) := by
  classical
  unfold mellinBarnesAbscissa
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · by_contra h3
    rw [not_and_or] at h1 h2 h3; push Not at h1 h2 h3
    have np {w : ℂ} {x₁ x₂ : ℝ} (p₁ : -1 < x₁ ∧ x₁ < 0) (p₂ : -1 < x₂ ∧ x₂ < 0) (ne : x₁ ≠ x₂) :=
      not_both_abscissa_poles (w := w) p₁ p₂ ne
    rcases h1 with h1a | h1b <;> rcases h2 with h2a | h2b <;> rcases h3 with h3a | h3b
    · exact np ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) h1a h2a
    · exact np ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) h1a h2a
    · exact np ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) h1a h3a
    · exact np ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) h2b h3b
    · exact np ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) h2a h3a
    · exact np ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) h1b h3b
    · exact np ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) h1b h2b
    · exact np ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) h1b h2b

/-- **Canonical separating-contour Mellin–Barnes continuation.** Evaluated at a canonical negative
abscissa avoiding `-Re a - ℕ` and `-Re b - ℕ`, this agrees with `mellinBarnesSeparating a b c z σ`
for every admissible negative abscissa `σ < 0` when `-z ∈ slitPlane`. -/
def mellinBarnesContour (a b c z : ℂ) : ℂ :=
  mellinBarnesSeparating a b c z (mellinBarnesAbscissa a b)

/-- Symmetry of `mellinBarnesContour` in `a` and `b`. -/
theorem mellinBarnesContour_symm (a b c z : ℂ) :
    mellinBarnesContour a b c z = mellinBarnesContour b a c z := by
  rw [mellinBarnesContour, mellinBarnesContour, mellinBarnesAbscissa_symm a b,
    mellinBarnesSeparating_symm a b c z]

/-- On `-z ∈ slitPlane`, `mellinBarnesContour a b c z` equals `mellinBarnesSeparating a b c z σ`
for every negative abscissa `σ < 0` avoiding `-Re a - ℕ` and `-Re b - ℕ`. -/
theorem mellinBarnesContour_eq_mellinBarnesSeparating {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (hσ : σ < 0) (ha : ∀ k : ℕ, a.re + σ ≠ -k) (hb : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz : -z ∈ slitPlane) :
    mellinBarnesContour a b c z = mellinBarnesSeparating a b c z σ :=
  mellinBarnesSeparating_eq_of_lt_zero c (mellinBarnesAbscissa_lt_zero a b) hσ
    (mellinBarnesAbscissa_avoid a b).1 (mellinBarnesAbscissa_avoid a b).2 ha hb hz

private theorem analyticAt_mellinBarnesIntegrand_uncurry {v : Fin 4 → ℂ} {t : ℂ}
    (ha : ∀ k : ℕ, v 0 + t ≠ -k) (hb : ∀ k : ℕ, v 1 + t ≠ -k) (ht : ∀ m : ℕ, -t ≠ -m)
    (hz : -v 3 ∈ slitPlane) :
    AnalyticAt ℂ
      (fun x : (Fin 4 → ℂ) × ℂ => mellinBarnesIntegrand (x.1 0) (x.1 1) (x.1 2) (x.1 3) x.2)
      (v, t) := by
  have hproj (i : Fin 4) : AnalyticAt ℂ (fun x : (Fin 4 → ℂ) × ℂ => x.1 i) (v, t) :=
    ((ContinuousLinearMap.proj (R := ℂ) i).comp
      (ContinuousLinearMap.fst ℂ (Fin 4 → ℂ) ℂ)).analyticAt (v, t)
  simp_rw [mellinBarnesIntegrand_def]
  exact ((((((analyticAt_Gamma ha).comp_of_eq ((hproj 0).add analyticAt_snd) rfl).mul
    ((analyticAt_Gamma hb).comp_of_eq ((hproj 1).add analyticAt_snd) rfl)).mul
    ((analyticAt_Gamma ht).comp_of_eq analyticAt_snd.neg rfl)).mul
    ((differentiable_one_div_Gamma.analyticAt (v 2 + t)).comp_of_eq
      ((hproj 2).add analyticAt_snd) rfl)).mul ((hproj 3).neg.cpow analyticAt_snd hz))

private theorem exists_ball_abscissa_avoid (w₀ : ℂ) {σ : ℝ} (hw₀ : ∀ k : ℕ, w₀.re + σ ≠ -k) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ w ∈ ball w₀ δ, (∀ k : ℕ, w.re + σ ≠ -k) ∧
        (∀ k : ℕ, (-w₀ - k).re < σ → (-w - k).re < σ) := by
  let N : ℕ := ⌊-w₀.re - σ⌋₊ + 2
  have hN : (Finset.range N).Nonempty := ⟨0, by simp [N]⟩
  let δ : ℝ := min (1 / 2) ((Finset.range N).inf' hN fun k => |w₀.re + σ + k| / 2)
  have hδ : 0 < δ := lt_min (by norm_num) ((Finset.lt_inf'_iff hN).2 fun k _ =>
    div_pos (abs_pos.2 fun h => hw₀ k (by linarith)) (by norm_num))
  refine ⟨δ, hδ, min_le_left _ _, fun w hw => ?_⟩
  have hw_re : |w.re - w₀.re| < δ := (abs_re_le_norm (w - w₀)).trans_lt (mem_ball_iff_norm.1 hw)
  have hδ_half : δ ≤ 1 / 2 := min_le_left _ _
  have hlarge {k : ℕ} (hk : N ≤ k) : 0 < w.re + σ + k := by
    have h2 : (⌊-w₀.re - σ⌋₊ + 2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Nat.lt_floor_add_one (-w₀.re - σ), (abs_lt.1 hw_re).1, sub_re w w₀]
  refine ⟨fun k => ?_, fun k hk0 => ?_⟩
  · by_cases hk : k < N
    · have hle : δ ≤ |w₀.re + σ + k| / 2 :=
        (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 hk))
      intro hEq
      have habs : |w₀.re + σ + k| = |w.re - w₀.re| := by
        rw [show w.re - w₀.re = -(w₀.re + σ + k) by linarith, abs_neg]
      linarith [abs_nonneg (w₀.re + σ + k)]
    · intro hEq; linarith [hlarge (not_lt.1 hk)]
  · simp only [sub_re, neg_re, natCast_re] at hk0 ⊢
    by_cases hk : k < N
    · have hle : δ ≤ |w₀.re + σ + k| / 2 :=
        (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 hk))
      rw [abs_of_pos (by linarith)] at hle; linarith [(abs_lt.1 hw_re).1]
    · linarith [hlarge (not_lt.1 hk)]

private theorem analyticAt_truncated_vertical_mellinBarnes {v : Fin 4 → ℂ} {σ : ℝ}
    (hσ : σ < 0) (ha : ∀ k : ℕ, (v 0).re + σ ≠ -k) (hb : ∀ k : ℕ, (v 1).re + σ ≠ -k)
    (hz : -v 3 ∈ slitPlane) (n : ℕ) :
    AnalyticAt ℂ (fun q : Fin 4 → ℂ =>
      ∫ y : ℝ in (-(n : ℝ))..(n : ℝ),
        mellinBarnesIntegrand (q 0) (q 1) (q 2) (q 3) (σ + y * I)) v := by
  have hn_le : -(n : ℝ) ≤ (n : ℝ) := by linarith [n.cast_nonneg (α := ℝ)]
  let γ : ℝ → ℂ := fun y => (σ : ℂ) + (projIcc (-(n : ℝ)) n hn_le y : ℝ) * I
  let K : Set ℂ := (fun y : ℝ => (σ : ℂ) + y * I) '' Icc (-(n : ℝ)) n
  have hγ : Continuous γ :=
    continuous_const.add ((continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_projIcc)).mul continuous_const)
  have hkernel : ∀ t ∈ K, AnalyticAt ℂ
      (fun x : (Fin 4 → ℂ) × ℂ => mellinBarnesIntegrand (x.1 0) (x.1 1) (x.1 2) (x.1 3) x.2)
      (v, t) := by
    rintro _ ⟨y, _, rfl⟩
    exact analyticAt_mellinBarnesIntegrand_uncurry
      (fun k h => ha k (by have hre := congrArg re h; simp at hre; linarith))
      (fun k h => hb k (by have hre := congrArg re h; simp at hre; linarith))
      (fun m h => by have hre := congrArg re h; simp at hre; linarith [m.cast_nonneg (α := ℝ)]) hz
  refine (TauCeti.analyticAt_integral_smul (isCompact_Icc.image (by fun_prop)) hγ
    (fun y => ⟨_, (projIcc (-(n : ℝ)) n hn_le y).property, rfl⟩) hkernel
    (integrable_const (1 : ℂ) : Integrable _ (volume.restrict (Ioc (-(n : ℝ)) n)))).congr
    (Eventually.of_forall fun q => ?_)
  dsimp only
  rw [intervalIntegral.integral_of_le hn_le]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  simp only [one_smul, γ, projIcc_of_mem hn_le (Ioc_subset_Icc_self hy)]

private theorem tendsto_setIntegral_compl_Ioc_zero {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun n : ℕ => ∫ y in (Ioc (-(n : ℝ)) n)ᶜ, g y) atTop (𝓝 0) := by
  have hsub : Tendsto (fun n : ℕ => (∫ y : ℝ, g y) - ∫ y : ℝ in (-(n : ℝ))..(n : ℝ), g y)
      atTop (𝓝 0) := by
    simpa only [sub_self, Function.comp_def] using (tendsto_const_nhds (x := ∫ y : ℝ, g y)).sub
      (intervalIntegral_tendsto_integral hg
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop)
  refine hsub.congr fun n => ?_
  rw [intervalIntegral.integral_of_le (by linarith [n.cast_nonneg (α := ℝ)]),
    ← integral_add_compl measurableSet_Ioc hg, add_sub_cancel_left]

private theorem tendstoUniformlyOn_truncated_vertical_mellinBarnes {v₀ : Fin 4 → ℂ} {σ δ₀ δ₁ ρ : ℝ}
    (hσ : σ < 0) (hδ₀_le : δ₀ ≤ 1 / 2) (hδ₁_le : δ₁ ≤ 1 / 2)
    (hav₀ : ∀ w ∈ ball (v₀ 0) δ₀, ∀ k : ℕ, w.re + σ ≠ -k)
    (hav₁ : ∀ w ∈ ball (v₀ 1) δ₁, ∀ k : ℕ, w.re + σ ≠ -k)
    (hz₀ : -v₀ 3 ∈ slitPlane)
    (hz_sub : ∀ z ∈ ball (v₀ 3) ρ, -z ∈ slitPlane ∧
      ‖v₀ 3‖ / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * ‖v₀ 3‖ ∧ |(-z).arg| ≤ π - 2 * ((π - |(-v₀ 3).arg|) / 4)) :
    TendstoUniformlyOn
      (fun (n : ℕ) (v : Fin 4 → ℂ) =>
        ∫ y : ℝ in (-(n : ℝ))..(n : ℝ), mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) (σ + y * I))
      (fun v : Fin 4 → ℂ =>
        ∫ y : ℝ, mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) (σ + y * I)) atTop
      (((fun v : Fin 4 → ℂ => v 0) ⁻¹' ball (v₀ 0) δ₀ ∩
          (fun v : Fin 4 → ℂ => v 1) ⁻¹' ball (v₀ 1) δ₁) ∩
        ((fun v : Fin 4 → ℂ => v 2) ⁻¹' ball (v₀ 2) 1 ∩
          (fun v : Fin 4 → ℂ => v 3) ⁻¹' ball (v₀ 3) ρ)) := by
  let δ : ℝ := (π - |(-v₀ 3).arg|) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz₀]
  have hr₁ : 0 < ‖v₀ 3‖ / 2 := half_pos (norm_pos_iff.2 (neg_ne_zero.1 (slitPlane_ne_zero hz₀)))
  let R₁ : ℝ := max (‖v₀ 0‖ + 1) (‖v₀ 1‖ + 1)
  let R₂ : ℝ := max (‖v₀ 2‖ + 1) |σ|
  let R : ℝ := max R₁ R₂ + 1
  obtain ⟨B, Y₀, _, _, hdom, htail⟩ := exists_norm_mellinBarnesIntegrand_vertical_le (R := R)
    (r₂ := 2 * ‖v₀ 3‖) (by positivity) hr₁ hδ
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_setIntegral_compl_Ioc_zero hdom).eventually (gt_mem_nhds hε),
    eventually_ge_atTop (⌈Y₀⌉₊ + 1)] with n hn_ε hn_Y v hv
  rw [dist_eq_norm]
  have hint_v := verticalIntegrable_mellinBarnesIntegrand (v 2) (hav₀ (v 0) hv.1.1)
    (hav₁ (v 1) hv.1.2) (fun m _ => by linarith [m.cast_nonneg (α := ℝ)]) (hz_sub (v 3) hv.2.2).1
  rw [intervalIntegral.integral_of_le (by linarith [n.cast_nonneg (α := ℝ)]),
    ← integral_add_compl (s := Ioc (-(n : ℝ)) n) measurableSet_Ioc hint_v, add_sub_cancel_left]
  refine (norm_integral_le_integral_norm _).trans_lt ((integral_mono_ae
    hint_v.norm.integrableOn hdom.integrableOn ?_).trans_lt hn_ε)
  filter_upwards [ae_restrict_mem measurableSet_Ioc.compl] with y hy
  have hyY : Y₀ ≤ |y| := by
    have hYN : Y₀ ≤ n := (Nat.le_ceil Y₀).trans
      (by exact_mod_cast (Nat.le_add_right _ 1).trans hn_Y)
    rcases not_and_or.1 hy with h1 | h2
    · linarith [not_lt.1 h1, neg_le_abs y]
    · linarith [not_le.1 h2, le_abs_self y]
  have hR1 : R₁ ≤ R := (le_max_left R₁ R₂).trans (le_add_of_nonneg_right zero_le_one)
  have hR2 : R₂ ≤ R := (le_max_right R₁ R₂).trans (le_add_of_nonneg_right zero_le_one)
  have hv0R : ‖v 0‖ ≤ R := by
    linarith [norm_le_norm_sub_add (v 0) (v₀ 0), (mem_ball_iff_norm.1 hv.1.1).le.trans hδ₀_le,
      (le_max_left (‖v₀ 0‖ + 1) (‖v₀ 1‖ + 1)).trans hR1]
  have hv1R : ‖v 1‖ ≤ R := by
    linarith [norm_le_norm_sub_add (v 1) (v₀ 1), (mem_ball_iff_norm.1 hv.1.2).le.trans hδ₁_le,
      (le_max_right (‖v₀ 0‖ + 1) (‖v₀ 1‖ + 1)).trans hR1]
  have hv2R : ‖v 2‖ ≤ R := by
    linarith [norm_le_norm_sub_add (v 2) (v₀ 2), (mem_ball_iff_norm.1 hv.2.1).le,
      (le_max_left (‖v₀ 2‖ + 1) |σ|).trans hR2]
  have hσR : |σ| ≤ R := (le_max_right (‖v₀ 2‖ + 1) |σ|).trans hR2
  have hzb := hz_sub (v 3) hv.2.2
  exact htail (v 0) (v 1) (v 2) (v 3) σ y hv0R hv1R hv2R hzb.2.1 hzb.2.2.1 hzb.2.2.2 hσR hyY

private theorem exists_ball_slitPlane_arg_bound {z₀ : ℂ} (hz₀ : -z₀ ∈ slitPlane) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ ball z₀ ρ, -z ∈ slitPlane ∧
      ‖z₀‖ / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * ‖z₀‖ ∧ |(-z).arg| ≤ π - 2 * ((π - |(-z₀).arg|) / 4) := by
  obtain ⟨ρ₁, hρ₁, hsub₁⟩ := Metric.isOpen_iff.1 (isOpen_slitPlane.preimage continuous_neg) z₀ hz₀
  let δ : ℝ := (π - |(-z₀).arg|) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz₀]
  have hcont_arg : ContinuousAt (fun z : ℂ => |(-z).arg|) z₀ :=
    continuous_abs.continuousAt.comp ((continuousAt_arg hz₀).comp continuous_neg.continuousAt)
  obtain ⟨ρ₂, hρ₂, hsub₂⟩ := Metric.eventually_nhds_iff_ball.1
    (hcont_arg.eventually (gt_mem_nhds (show |(-z₀).arg| < |(-z₀).arg| + 2 * δ by linarith)))
  have hz₀_pos : 0 < ‖z₀‖ := norm_pos_iff.2 (neg_ne_zero.1 (slitPlane_ne_zero hz₀))
  refine ⟨min (‖z₀‖ / 2) (min ρ₁ ρ₂), lt_min (by positivity) (lt_min hρ₁ hρ₂), fun z hz => ?_⟩
  have hzn : ‖z - z₀‖ < ‖z₀‖ / 2 := (mem_ball_iff_norm.1 hz).trans_le (min_le_left _ _)
  have hlt := hsub₂ z (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hz)
  exact ⟨hsub₁ (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz),
    by linarith [norm_sub_norm_le z₀ z, norm_sub_rev z₀ z],
    by linarith [norm_le_norm_sub_add z z₀], by dsimp [δ] at hlt ⊢; linarith⟩

private theorem analyticAt_vertical_mellinBarnes {v₀ : Fin 4 → ℂ} {σ : ℝ}
    (hσ : σ < 0) (ha₀ : ∀ k : ℕ, (v₀ 0).re + σ ≠ -k) (hb₀ : ∀ k : ℕ, (v₀ 1).re + σ ≠ -k)
    (hz₀ : -v₀ 3 ∈ slitPlane) :
    AnalyticAt ℂ (fun v : Fin 4 → ℂ =>
      ∫ y : ℝ, mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) (σ + y * I)) v₀ := by
  obtain ⟨δ₀, hδ₀, hδ₀_le, hav₀⟩ := exists_ball_abscissa_avoid (v₀ 0) ha₀
  obtain ⟨δ₁, hδ₁, hδ₁_le, hav₁⟩ := exists_ball_abscissa_avoid (v₀ 1) hb₀
  obtain ⟨ρ, hρ, hz_sub⟩ := exists_ball_slitPlane_arg_bound hz₀
  let U : Set (Fin 4 → ℂ) :=
    ((· 0) ⁻¹' ball (v₀ 0) δ₀ ∩ (· 1) ⁻¹' ball (v₀ 1) δ₁) ∩
    ((· 2) ⁻¹' ball (v₀ 2) 1 ∩ (· 3) ⁻¹' ball (v₀ 3) ρ)
  have hU_open : IsOpen U :=
    ((isOpen_ball.preimage (continuous_apply 0)).inter
      (isOpen_ball.preimage (continuous_apply 1))).inter
      ((isOpen_ball.preimage (continuous_apply 2)).inter
        (isOpen_ball.preimage (continuous_apply 3)))
  have hv₀U : v₀ ∈ U := ⟨⟨mem_ball_self hδ₀, mem_ball_self hδ₁⟩,
    ⟨mem_ball_self zero_lt_one, mem_ball_self hρ⟩⟩
  have hunif := tendstoUniformlyOn_truncated_vertical_mellinBarnes hσ hδ₀_le hδ₁_le
    (fun w hw => (hav₀ w hw).1) (fun w hw => (hav₁ w hw).1) hz₀ hz_sub
  have hF_an (n : ℕ) (v : Fin 4 → ℂ) (hv : v ∈ U) :=
    analyticAt_truncated_vertical_mellinBarnes hσ (hav₀ (v 0) hv.1.1).1
      (hav₁ (v 1) hv.1.2).1 (hz_sub (v 3) hv.2.2).1 n
  have hG_cont := hunif.continuousOn <| (Eventually.of_forall (f := atTop) fun n : ℕ =>
    (fun v hv => (hF_an n v hv).continuousAt.continuousWithinAt : ContinuousOn _ U)).frequently
  refine hG_cont.analyticAt_of_differentiableAt_update (hU_open.mem_nhds hv₀U) fun y hy i => ?_
  let V : Set ℂ := (fun x => Function.update y i x) ⁻¹' U
  have hV_open : IsOpen V := hU_open.preimage (Continuous.update continuous_const i continuous_id)
  have hupd : Differentiable ℂ (fun x : ℂ => Function.update y i x) :=
    differentiable_pi.2 fun j => by by_cases hj : j = i <;> simp [Function.update, hj]
  have hunifV : TendstoUniformlyOn
      (fun (n : ℕ) x => ∫ w : ℝ in (-(n : ℝ))..(n : ℝ),
        mellinBarnesIntegrand (Function.update y i x 0) (Function.update y i x 1)
          (Function.update y i x 2) (Function.update y i x 3) (σ + w * I))
      (fun x => ∫ w : ℝ,
        mellinBarnesIntegrand (Function.update y i x 0) (Function.update y i x 1)
          (Function.update y i x 2) (Function.update y i x 3) (σ + w * I)) atTop V :=
    Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
      (Metric.tendstoUniformlyOn_iff.1 hunif ε hε).mono fun _ hn _ hx => hn _ hx
  have hyV : y i ∈ V := show Function.update y i (y i) ∈ U by rwa [Function.update_eq_self]
  exact (hunifV.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall (f := atTop) fun (n : ℕ) x hx =>
      ((hF_an n _ hx).differentiableAt.comp x (hupd x)).differentiableWithinAt)
    hV_open).differentiableAt (hV_open.mem_nhds hyV)

private theorem exists_pos_lt_norm_sub_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ m) :
    ∃ r : ℝ, 0 < r ∧ ∀ m : ℕ, r < ‖s - m‖ := by
  let M : ℕ := ⌈‖s‖⌉₊ + 2
  have hM : (Finset.range M).Nonempty := ⟨0, by simp [M]⟩
  let r : ℝ := min (1 / 2) ((Finset.range M).inf' hM fun m => ‖s - m‖ / 2)
  have hr : 0 < r := lt_min (by norm_num) ((Finset.lt_inf'_iff hM).2 fun m _ =>
    div_pos (norm_pos_iff.2 (sub_ne_zero.2 (hs m))) (by norm_num))
  refine ⟨r, hr, fun m => ?_⟩
  by_cases hm : m < M
  · have hle : r ≤ ‖s - m‖ / 2 :=
      (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 hm))
    linarith [norm_pos_iff.2 (sub_ne_zero.2 (hs m))]
  · have h2 : (⌈‖s‖⌉₊ + 2 : ℝ) ≤ m := by exact_mod_cast not_lt.1 hm
    have h := norm_sub_norm_le (m : ℂ) s
    rw [Complex.norm_natCast, norm_sub_rev] at h
    linarith [Nat.le_ceil ‖s‖,
      min_le_left (1 / 2 : ℝ) ((Finset.range M).inf' hM fun m => ‖s - m‖ / 2)]

private theorem exists_isolating_radius_mellinBarnesLeftPoles {a₀ b₀ : ℂ} (σ : ℝ)
    (ha₀ : ∀ k : ℕ, a₀ ≠ -k) (hb₀ : ∀ k : ℕ, b₀ ≠ -k) :
    ∃ r : ℝ, 0 < r ∧
      (∀ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, σ + r < s.re) ∧
      (∀ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, ∀ m : ℕ, r < ‖s - m‖) ∧
      (∀ s₁ ∈ mellinBarnesLeftPoles a₀ b₀ σ, ∀ s₂ ∈ mellinBarnesLeftPoles a₀ b₀ σ,
        s₁ ≠ s₂ → 2 * r < dist s₁ s₂) := by
  set P₀ : Finset ℂ := mellinBarnesLeftPoles a₀ b₀ σ
  have hs_nat : ∀ s ∈ P₀, ∀ m : ℕ, s ≠ m := fun s hs m hEq => by
    rcases (mem_mellinBarnesLeftPoles.1 hs).2 with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ha₀ (k + m) (by push_cast; linear_combination -hEq)
    · exact hb₀ (k + m) (by push_cast; linear_combination -hEq)
  suffices ∀ Q : Finset ℂ, (∀ s ∈ Q, σ < s.re ∧ ∀ m : ℕ, s ≠ m) →
      ∃ r : ℝ, 0 < r ∧ (∀ s ∈ Q, σ + r < s.re) ∧ (∀ s ∈ Q, ∀ m : ℕ, r < ‖s - m‖) ∧
        (∀ s₁ ∈ Q, ∀ s₂ ∈ Q, s₁ ≠ s₂ → 2 * r < dist s₁ s₂) from
    this P₀ fun s hs => ⟨(mem_mellinBarnesLeftPoles.1 hs).1, hs_nat s hs⟩
  intro Q
  induction Q using Finset.cons_induction with
  | empty => exact fun _ => ⟨1, zero_lt_one, by simp, by simp, by simp⟩
  | cons s₀ Q hs₀ ih =>
    intro hQ
    obtain ⟨r₁, hr₁, hre₁, hnat₁, hsep₁⟩ := ih fun s hs => hQ s (Finset.mem_cons_of_mem hs)
    have hs₀Q := hQ s₀ (Finset.mem_cons_self s₀ Q)
    obtain ⟨r₂, hr₂, hnat₂⟩ := exists_pos_lt_norm_sub_nat hs₀Q.2
    let r₃ : ℝ := if hne : Q.Nonempty then Q.inf' hne fun s => dist s₀ s / 3 else 1
    have hr₃ : 0 < r₃ := by
      dsimp [r₃]; split_ifs with hne
      · exact (Finset.lt_inf'_iff hne).2 fun s hs =>
          div_pos (dist_pos.2 fun h => hs₀ (h ▸ hs)) (by norm_num)
      · exact zero_lt_one
    let r : ℝ := min (min r₁ r₂) (min ((s₀.re - σ) / 2) r₃)
    have hr : 0 < r := lt_min (lt_min hr₁ hr₂) (lt_min (by linarith [hs₀Q.1]) hr₃)
    have hr_le₁ : r ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hr_le₂ : r ≤ r₂ := (min_le_left _ _).trans (min_le_right _ _)
    have hr_le_re : r ≤ (s₀.re - σ) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hr_le₃ : r ≤ r₃ := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨r, hr, fun s hs => ?_, fun s hs m => ?_, fun s₁ hs₁ s₂ hs₂ hne => ?_⟩
    · rcases Finset.mem_cons.1 hs with rfl | hs <;> [linarith [hs₀Q.1]; linarith [hre₁ s hs]]
    · rcases Finset.mem_cons.1 hs with rfl | hs
      · exact hr_le₂.trans_lt (hnat₂ m)
      · exact hr_le₁.trans_lt (hnat₁ s hs m)
    · have hdist_s₀ (s : ℂ) (hs : s ∈ Q) : 2 * r < dist s₀ s := by
        have hle : r₃ ≤ dist s₀ s / 3 := by
          dsimp only [r₃]; rw [dite_eq_left_of_eq_true (eq_true ⟨s, hs⟩)]; exact Finset.inf'_le _ hs
        linarith [dist_pos.2 fun h : s₀ = s => hs₀ (h ▸ hs)]
      rcases Finset.mem_cons.1 hs₁ with h1 | hs₁ <;> rcases Finset.mem_cons.1 hs₂ with h2 | hs₂
      · exact absurd (h1.trans h2.symm) hne
      · exact h1 ▸ hdist_s₀ s₂ hs₂
      · rw [h2, dist_comm]; exact hdist_s₀ s₁ hs₁
      · linarith [hsep₁ s₁ hs₁ s₂ hs₂ hne]

private theorem mellinBarnesLeftPoles_cover {a₀ b₀ a b : ℂ} {σ r : ℝ}
    (ha₀_σ : ∀ k : ℕ, a₀.re + σ ≠ -k) (hb₀_σ : ∀ k : ℕ, b₀.re + σ ≠ -k)
    (ha_dist : ‖a - a₀‖ < r / 2) (hb_dist : ‖b - b₀‖ < r / 2)
    (ha_cross : ∀ k : ℕ, (-a₀ - k).re < σ → (-a - k).re < σ)
    (hb_cross : ∀ k : ℕ, (-b₀ - k).re < σ → (-b - k).re < σ) :
    ∀ w ∈ mellinBarnesLeftPoles a b σ, ∃ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, w ∈ ball s r := by
  intro w hw
  rcases mem_mellinBarnesLeftPoles.1 hw with ⟨hw_re, ⟨k, rfl⟩ | ⟨k, rfl⟩⟩
  · refine ⟨-a₀ - k, mem_mellinBarnesLeftPoles.2 ⟨lt_of_le_of_ne
      (not_lt.1 fun h => hw_re.not_gt (ha_cross k h)) (fun h => ha₀_σ k (by simp at h; linarith)),
      Or.inl ⟨k, rfl⟩⟩, ?_⟩
    rw [mem_ball_iff_norm, show (-a - (k : ℂ)) - (-a₀ - k) = -(a - a₀) by ring, norm_neg]
    linarith [norm_nonneg (a - a₀)]
  · refine ⟨-b₀ - k, mem_mellinBarnesLeftPoles.2 ⟨lt_of_le_of_ne
      (not_lt.1 fun h => hw_re.not_gt (hb_cross k h)) (fun h => hb₀_σ k (by simp at h; linarith)),
      Or.inr ⟨k, rfl⟩⟩, ?_⟩
    rw [mem_ball_iff_norm, show (-b - (k : ℂ)) - (-b₀ - k) = -(b - b₀) by ring, norm_neg]
    linarith [norm_nonneg (b - b₀)]

private theorem residueSum_eq_sum_circleIntegral_mellinBarnes {a₀ b₀ a b : ℂ} (c z : ℂ) {σ r : ℝ}
    (hr : 0 < r)
    (hre : ∀ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, σ + r < s.re)
    (hnat : ∀ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, ∀ m : ℕ, r < ‖s - m‖)
    (hsep : ∀ s₁ ∈ mellinBarnesLeftPoles a₀ b₀ σ, ∀ s₂ ∈ mellinBarnesLeftPoles a₀ b₀ σ,
      s₁ ≠ s₂ → 2 * r < dist s₁ s₂)
    (ha₀_σ : ∀ k : ℕ, a₀.re + σ ≠ -k) (hb₀_σ : ∀ k : ℕ, b₀.re + σ ≠ -k)
    (ha_dist : ‖a - a₀‖ < r / 2) (hb_dist : ‖b - b₀‖ < r / 2)
    (ha_cross : ∀ k : ℕ, (-a₀ - k).re < σ → (-a - k).re < σ)
    (hb_cross : ∀ k : ℕ, (-b₀ - k).re < σ → (-b - k).re < σ) :
    (∑ w ∈ mellinBarnesLeftPoles a b σ,
      TauCeti.Contour.residue (mellinBarnesIntegrand a b c z) w) =
      ∑ s ∈ mellinBarnesLeftPoles a₀ b₀ σ,
        (2 * (π : ℂ) * I)⁻¹ * ∮ ζ in C(s, r), mellinBarnesIntegrand a b c z ζ := by
  classical
  set P₀ : Finset ℂ := mellinBarnesLeftPoles a₀ b₀ σ
  set P : Finset ℂ := mellinBarnesLeftPoles a b σ
  let F : ℂ → Finset ℂ := fun s => P.filter (· ∈ ball s r)
  have hcover := mellinBarnesLeftPoles_cover ha₀_σ hb₀_σ ha_dist hb_dist ha_cross hb_cross
  have hdisj : (P₀ : Set ℂ).PairwiseDisjoint F := fun s₁ hs₁ s₂ hs₂ hne =>
    Finset.disjoint_left.2 fun w hw₁ hw₂ =>
      by linarith [mem_ball.1 (Finset.mem_filter.1 hw₁).2,
        mem_ball.1 (Finset.mem_filter.1 hw₂).2, dist_triangle_left s₁ s₂ w, hsep s₁ hs₁ s₂ hs₂ hne]
  have hbiU : P₀.biUnion F = P := by
    ext w; simp only [Finset.mem_biUnion, F, Finset.mem_filter]
    exact ⟨fun ⟨_, _, hw, _⟩ => hw, fun hw =>
      let ⟨s, hs, hws⟩ := hcover w hw; ⟨s, hs, hw, hws⟩⟩
  rw [← hbiU, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsupp : ∀ w ∈ closedBall s r,
      meromorphicOrderAt (mellinBarnesIntegrand a b c z) w < 0 → w ∈ F s := fun w hw hord => by
    have hpole : (∃ k : ℕ, w = -a - k) ∨ (∃ k : ℕ, w = -b - k) := by
      by_contra hno; push Not at hno
      refine hord.not_ge (analyticAt_mellinBarnesIntegrand a b c z hno.1 hno.2
        fun m hm => ?_).meromorphicOrderAt_nonneg
      have h1 : ‖s - m‖ ≤ r := by rw [← dist_eq_norm, dist_comm, ← hm]; exact hw
      linarith [hnat s hs m]
    have hw_re : σ < w.re := by
      have h1 : |w.re - s.re| ≤ r := (abs_re_le_norm (w - s)).trans (mem_closedBall_iff_norm.1 hw)
      linarith [(abs_le.1 h1).1, hre s hs]
    have hwP : w ∈ P := mem_mellinBarnesLeftPoles.2 ⟨hw_re, hpole⟩
    obtain ⟨s', hs', hws'⟩ := hcover w hwP
    have hs_eq : s' = s := by
      by_contra hne
      linarith [mem_closedBall.1 hw, mem_ball.1 hws', dist_triangle_left s' s w,
        hsep s' hs' s hs hne]
    subst hs_eq; exact Finset.mem_filter.2 ⟨hwP, hws'⟩
  have hcirc := TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hr (F s)
    (fun ζ _ => meromorphicAt_mellinBarnesIntegrand a b c z ζ)
    (fun ζ hζ => (Finset.mem_filter.1 hζ).2) hsupp
  have h2piI : (2 * (π : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)) I_ne_zero
  rw [hcirc, inv_mul_cancel_left₀ h2piI]

private theorem analyticAt_circleIntegral_mellinBarnes_term {v₀ : Fin 4 → ℂ} {σ r : ℝ}
    (hr : 0 < r)
    (hre : ∀ s ∈ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ, σ + r < s.re)
    (hnat : ∀ s ∈ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ, ∀ m : ℕ, r < ‖s - m‖)
    (hsep : ∀ s₁ ∈ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ,
      ∀ s₂ ∈ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ, s₁ ≠ s₂ → 2 * r < dist s₁ s₂)
    (hz₀ : -v₀ 3 ∈ slitPlane)
    {s : ℂ} (hs : s ∈ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ) :
    AnalyticAt ℂ (fun v : Fin 4 → ℂ =>
      (2 * (π : ℂ) * I)⁻¹ * ∮ ζ in C(s, r),
        mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) ζ) v₀ := by
  refine analyticAt_const.mul (TauCeti.analyticAt_circleIntegral (c := s) (R := r) (p₀ := v₀)
    (f := fun p : (Fin 4 → ℂ) × ℂ => mellinBarnesIntegrand (p.1 0) (p.1 1) (p.1 2) (p.1 3) p.2)
    fun ζ hζ => ?_)
  rw [abs_of_pos hr] at hζ
  have hζ_re : σ < ζ.re := by
    have h1 : |ζ.re - s.re| ≤ r := (abs_re_le_norm (ζ - s)).trans (mem_sphere_iff_norm.1 hζ).le
    linarith [(abs_le.1 h1).1, hre s hs]
  have hnot_P₀ : ζ ∉ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ := fun hζP => by
    by_cases heq : ζ = s
    · subst heq; simp at hζ; linarith
    · linarith [mem_sphere.1 hζ, hsep ζ hζP s hs heq]
  exact analyticAt_mellinBarnesIntegrand_uncurry
    (fun k hk => hnot_P₀ (mem_mellinBarnesLeftPoles.2
      ⟨hζ_re, Or.inl ⟨k, by linear_combination hk⟩⟩))
    (fun k hk => hnot_P₀ (mem_mellinBarnesLeftPoles.2
      ⟨hζ_re, Or.inr ⟨k, by linear_combination hk⟩⟩))
    (fun m hm => by
      have h1 : ‖s - m‖ = r := by
        rw [← dist_eq_norm, dist_comm, ← (by linear_combination -hm : ζ = m)]; exact hζ
      linarith [hnat s hs m]) hz₀

private theorem analyticAt_residueSum_mellinBarnes {v₀ : Fin 4 → ℂ} {σ : ℝ}
    (ha₀ : ∀ k : ℕ, v₀ 0 ≠ -k) (hb₀ : ∀ k : ℕ, v₀ 1 ≠ -k)
    (ha₀_σ : ∀ k : ℕ, (v₀ 0).re + σ ≠ -k) (hb₀_σ : ∀ k : ℕ, (v₀ 1).re + σ ≠ -k)
    (hz₀ : -v₀ 3 ∈ slitPlane) :
    AnalyticAt ℂ (fun v : Fin 4 → ℂ =>
      ∑ w ∈ mellinBarnesLeftPoles (v 0) (v 1) σ,
        TauCeti.Contour.residue (mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3)) w) v₀ := by
  obtain ⟨r, hr, hre, hnat, hsep⟩ := exists_isolating_radius_mellinBarnesLeftPoles σ ha₀ hb₀
  obtain ⟨δ₀, hδ₀, _, hav₀⟩ := exists_ball_abscissa_avoid (v₀ 0) ha₀_σ
  obtain ⟨δ₁, hδ₁, _, hav₁⟩ := exists_ball_abscissa_avoid (v₀ 1) hb₀_σ
  have hsum_an : ∀ Q : Finset ℂ,
      (∀ s ∈ Q, AnalyticAt ℂ (fun v : Fin 4 → ℂ =>
        (2 * (π : ℂ) * I)⁻¹ * ∮ ζ in C(s, r),
          mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) ζ) v₀) →
      AnalyticAt ℂ (fun v : Fin 4 → ℂ => ∑ s ∈ Q,
        (2 * (π : ℂ) * I)⁻¹ * ∮ ζ in C(s, r),
          mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) ζ) v₀ := by
    intro Q
    induction Q using Finset.cons_induction with
    | empty => exact fun _ => by simpa using analyticAt_const
    | cons s Q _ ih =>
      intro hQ; simp_rw [Finset.sum_cons]
      exact (hQ s (Finset.mem_cons_self s Q)).add
        (ih fun t ht => hQ t (Finset.mem_cons_of_mem ht))
  let δ_ab : ℝ := min (r / 2) (min δ₀ δ₁)
  have hδ_ab : 0 < δ_ab := lt_min (by positivity) (lt_min hδ₀ hδ₁)
  have hU_nhds : ((· 0) ⁻¹' ball (v₀ 0) δ_ab ∩ (· 1) ⁻¹' ball (v₀ 1) δ_ab) ∈ 𝓝 v₀ :=
    ((isOpen_ball.preimage (continuous_apply 0)).inter
      (isOpen_ball.preimage (continuous_apply 1))).mem_nhds
      ⟨mem_ball_self hδ_ab, mem_ball_self hδ_ab⟩
  refine (hsum_an (mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ) fun _ hs =>
    analyticAt_circleIntegral_mellinBarnes_term hr hre hnat hsep hz₀ hs).congr ?_
  filter_upwards [hU_nhds] with v hv
  exact (residueSum_eq_sum_circleIntegral_mellinBarnes (v 2) (v 3) hr hre hnat hsep ha₀_σ hb₀_σ
    ((mem_ball_iff_norm.1 hv.1).trans_le (min_le_left _ _))
    ((mem_ball_iff_norm.1 hv.2).trans_le (min_le_left _ _))
    (hav₀ (v 0) (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hv.1)).2
    (hav₁ (v 1) (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hv.2)).2).symm

private theorem analyticAt_mellinBarnesContour_pi {v₀ : Fin 4 → ℂ}
    (ha₀ : ∀ k : ℕ, v₀ 0 ≠ -k) (hb₀ : ∀ k : ℕ, v₀ 1 ≠ -k) (hz₀ : -v₀ 3 ∈ slitPlane) :
    AnalyticAt ℂ (fun v : Fin 4 → ℂ => mellinBarnesContour (v 0) (v 1) (v 2) (v 3)) v₀ := by
  let σ : ℝ := mellinBarnesAbscissa (v₀ 0) (v₀ 1)
  have hσ : σ < 0 := mellinBarnesAbscissa_lt_zero (v₀ 0) (v₀ 1)
  obtain ⟨ha₀_σ, hb₀_σ⟩ := mellinBarnesAbscissa_avoid (v₀ 0) (v₀ 1)
  obtain ⟨δ₀, hδ₀, _, hav₀⟩ := exists_ball_abscissa_avoid (v₀ 0) ha₀_σ
  obtain ⟨δ₁, hδ₁, _, hav₁⟩ := exists_ball_abscissa_avoid (v₀ 1) hb₀_σ
  have hz_open : IsOpen {v : Fin 4 → ℂ | -v 3 ∈ slitPlane} :=
    isOpen_slitPlane.preimage (continuous_neg.comp (continuous_apply 3))
  have hU_nhds : (((· 0) ⁻¹' ball (v₀ 0) δ₀ ∩ (· 1) ⁻¹' ball (v₀ 1) δ₁) ∩
      {v : Fin 4 → ℂ | -v 3 ∈ slitPlane}) ∈ 𝓝 v₀ :=
    (((isOpen_ball.preimage (continuous_apply 0)).inter
      (isOpen_ball.preimage (continuous_apply 1))).inter hz_open).mem_nhds
      ⟨⟨mem_ball_self hδ₀, mem_ball_self hδ₁⟩, hz₀⟩
  have hc : AnalyticAt ℂ (fun _ : Fin 4 → ℂ => (2 * π : ℂ)⁻¹) v₀ := analyticAt_const
  refine ((hc.mul (analyticAt_vertical_mellinBarnes hσ ha₀_σ hb₀_σ hz₀)).add
    (analyticAt_residueSum_mellinBarnes ha₀ hb₀ ha₀_σ hb₀_σ hz₀)).congr ?_
  filter_upwards [hU_nhds] with v hv
  dsimp only [Pi.add_apply, Pi.mul_apply]
  rw [mellinBarnesContour_eq_mellinBarnesSeparating (v 2) hσ (hav₀ (v 0) hv.1.1).1
    (hav₁ (v 1) hv.1.2).1 hv.2, mellinBarnesSeparating_def]

/-- **Joint four-variable holomorphy of the separating-contour Mellin–Barnes continuation.** On
`{p | (∀ k : ℕ, a ≠ -k) ∧ (∀ k : ℕ, b ≠ -k) ∧ -z ∈ slitPlane}`, `mellinBarnesContour a b c z` is
jointly analytic in `(a, b, c, z)` across all lower parameters `c : ℂ` and across integer
differences `a - b ∈ ℤ`. -/
theorem analyticOnNhd_mellinBarnesContour :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ × ℂ => mellinBarnesContour p.1 p.2.1 p.2.2.1 p.2.2.2)
      {p | (∀ k : ℕ, p.1 ≠ -k) ∧ (∀ k : ℕ, p.2.1 ≠ -k) ∧ -p.2.2.2 ∈ slitPlane} := by
  intro p ⟨ha, hb, hz⟩
  let emb : ℂ × ℂ × ℂ × ℂ → Fin 4 → ℂ :=
    fun q => fun | 0 => q.1 | 1 => q.2.1 | 2 => q.2.2.1 | 3 => q.2.2.2
  have hemb : AnalyticAt ℂ emb p := (differentiable_pi.2 fun i => by
    fin_cases i <;> dsimp [emb] <;> fun_prop).differentiableOn.analyticAt_of_finiteDimensional
    univ_mem
  exact ((analyticAt_mellinBarnesContour_pi (v₀ := emb p) ha hb hz).comp hemb).congr
    (Eventually.of_forall fun _ => rfl)

end Complex
