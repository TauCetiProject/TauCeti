/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.SeparatingContour.Basic
import Mathlib.Analysis.Analytic.Constructions
import TauCeti.Algebra.Order.Ring.Abs
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Canonical separating-contour continuation and joint four-variable holomorphy

This module defines the canonical abscissa-independent separating-contour Mellin–Barnes integral
`Complex.mellinBarnesIntegral` representing `Γ(a) Γ(b) 𝐅(a, b; c; z)` (and hence
`(Γ(a) Γ(b) / Γ(c)) ₂F₁(a, b; c; z)`) and proves its joint four-variable holomorphy
`Complex.analyticOnNhd_mellinBarnesIntegral` on
`{(a, b, c, z) | a ∉ -ℕ ∧ b ∉ -ℕ ∧ -z ∈ Complex.slitPlane}` across all lower parameters `c : ℂ`,
including resonant integer differences `a - b ∈ ℤ` where simple poles coalesce into double poles.

Locally around `(a₀, b₀, c₀, z₀)`, fixing `σ < 0` avoiding `-Re a₀ - ℕ` and `-Re b₀ - ℕ`, joint
holomorphy of the vertical integral follows from compact-segment holomorphy, uniform Stirling decay,
uniform limits of holomorphic maps (`TendstoUniformlyOn.differentiableOn`), and
`DifferentiableOn.analyticAt_of_finiteDimensional`; joint holomorphy of the finite residue sum
follows by rewriting it via
`TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg` as a sum of Cauchy
circle integrals around isolating circles.

## Main definitions and results

* `Complex.mellinBarnesIntegral`, `Complex.mellinBarnesIntegral_symm`,
  `Complex.mellinBarnesIntegral_eq_mellinBarnesSeparatingIntegral`,
  `Complex.exists_mellinBarnesIntegral_eq_mellinBarnesSeparatingIntegral`,
  `Complex.mellinBarnesIntegral_of_neg_re_lt`.
* `Complex.analyticOnNhd_integral_mellinBarnesIntegrand`: joint four-variable holomorphy of the
  vertical-line integral along any fixed `Re t = σ` (`σ ∉ ℕ`).
* `Complex.analyticOnNhd_mellinBarnesIntegral`: joint four-variable holomorphy of
  `mellinBarnesIntegral` in `(a, b, c, z)`.

## References

* NIST Digital Library of Mathematical Functions, §15.6(ii), equation 15.6.6.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.5.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 5.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Real Topology

namespace Complex

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
  · let cand : Finset ℝ := {-1 / 2, -1 / 4, -3 / 4}
    let bad (w : ℂ) : Finset ℝ := cand.filter fun x => ∃ k : ℕ, w.re + x = -k
    have hbad_le (w : ℂ) : (bad w).card ≤ 1 := Finset.card_le_one.2 fun x₁ hx₁ x₂ hx₂ => by
      simp only [bad, cand, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
      obtain ⟨hx₁c, k₁, hk₁⟩ := hx₁
      obtain ⟨hx₂c, k₂, hk₂⟩ := hx₂
      have hdist : |x₁ - x₂| < 1 := by
        rcases hx₁c with rfl | rfl | rfl <;> rcases hx₂c with rfl | rfl | rfl <;> norm_num
      exact TauCeti.eq_of_add_eq_intCast_of_abs_sub_lt_one (m₁ := -(k₁ : ℤ)) (m₂ := -(k₂ : ℤ))
        hdist (by simpa using hk₁) (by simpa using hk₂)
    have hcard : (bad a ∪ bad b).card < cand.card := by
      have h3 : cand.card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; norm_num),
          Finset.card_insert_of_notMem (by norm_num), Finset.card_singleton]
      linarith [Finset.card_union_le (bad a) (bad b), hbad_le a, hbad_le b]
    obtain ⟨x, hx, hx_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [bad, Finset.mem_union, Finset.mem_filter, not_or, not_and, not_exists] at hx_not
    have hx_av : (∀ k : ℕ, a.re + x ≠ -k) ∧ (∀ k : ℕ, b.re + x ≠ -k) :=
      ⟨fun k => hx_not.1 hx k, fun k => hx_not.2 hx k⟩
    simp only [cand, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact absurd hx_av h1
    · exact absurd hx_av h2
    · exact hx_av

/-- **Canonical separating-contour Mellin–Barnes integral**, representing
`Γ(a) Γ(b) 𝐅(a, b; c; z)` (and hence `(Γ(a) Γ(b) / Γ(c)) ₂F₁(a, b; c; z)`). Evaluated at a
canonical negative abscissa avoiding `-Re a - ℕ` and `-Re b - ℕ`, this agrees with
`mellinBarnesSeparatingIntegral a b c z σ` for every admissible negative abscissa `σ < 0` when
`-z ∈ slitPlane`. -/
def mellinBarnesIntegral (a b c z : ℂ) : ℂ :=
  mellinBarnesSeparatingIntegral a b c z (mellinBarnesAbscissa a b)

/-- Symmetry of `mellinBarnesIntegral` in `a` and `b`. -/
theorem mellinBarnesIntegral_symm (a b c z : ℂ) :
    mellinBarnesIntegral a b c z = mellinBarnesIntegral b a c z := by
  rw [mellinBarnesIntegral, mellinBarnesIntegral, mellinBarnesAbscissa_symm a b,
    mellinBarnesSeparatingIntegral_symm a b c z]

/-- On `-z ∈ slitPlane`, `mellinBarnesIntegral a b c z` equals
`mellinBarnesSeparatingIntegral a b c z σ` for every negative abscissa `σ < 0` avoiding
`-Re a - ℕ` and `-Re b - ℕ`. -/
theorem mellinBarnesIntegral_eq_mellinBarnesSeparatingIntegral {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (hσ : σ < 0) (ha : ∀ k : ℕ, a.re + σ ≠ -k) (hb : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz : -z ∈ slitPlane) :
    mellinBarnesIntegral a b c z = mellinBarnesSeparatingIntegral a b c z σ :=
  mellinBarnesSeparatingIntegral_eq_of_lt_zero c (mellinBarnesAbscissa_lt_zero a b) hσ
    (mellinBarnesAbscissa_avoid a b).1 (mellinBarnesAbscissa_avoid a b).2 ha hb hz

/-- Every `(a, b, c, z)` admits a negative abscissa `σ < 0` avoiding `-Re a - ℕ` and `-Re b - ℕ`
at which `mellinBarnesIntegral a b c z = mellinBarnesSeparatingIntegral a b c z σ`. -/
theorem exists_mellinBarnesIntegral_eq_mellinBarnesSeparatingIntegral (a b c z : ℂ) :
    ∃ σ : ℝ, σ < 0 ∧ (∀ k : ℕ, a.re + σ ≠ -k) ∧ (∀ k : ℕ, b.re + σ ≠ -k) ∧
      mellinBarnesIntegral a b c z = mellinBarnesSeparatingIntegral a b c z σ :=
  ⟨mellinBarnesAbscissa a b, mellinBarnesAbscissa_lt_zero a b,
    (mellinBarnesAbscissa_avoid a b).1, (mellinBarnesAbscissa_avoid a b).2, rfl⟩

/-- When `-Re a < σ`, `-Re b < σ`, `σ < 0`, and `-z ∈ slitPlane`, the canonical Mellin–Barnes
integral reduces to the straight vertical-line integral along `Re t = σ`. -/
theorem mellinBarnesIntegral_of_neg_re_lt {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (ha : -a.re < σ) (hb : -b.re < σ) (hσ : σ < 0) (hz : -z ∈ slitPlane) :
    mellinBarnesIntegral a b c z =
      (2 * π : ℂ)⁻¹ * ∫ y : ℝ, mellinBarnesIntegrand a b c z (σ + y * I) := by
  rw [mellinBarnesIntegral_eq_mellinBarnesSeparatingIntegral c hσ
      (fun k _ => by linarith [k.cast_nonneg (α := ℝ)])
      (fun k _ => by linarith [k.cast_nonneg (α := ℝ)]) hz,
    mellinBarnesSeparatingIntegral_of_neg_re_le c z ha.le hb.le]

private theorem analyticAt_truncated_vertical_mellinBarnes {p : ℂ × ℂ × ℂ × ℂ} {σ : ℝ}
    (hσ : ∀ m : ℕ, σ ≠ m) (ha : ∀ k : ℕ, p.1.re + σ ≠ -k) (hb : ∀ k : ℕ, p.2.1.re + σ ≠ -k)
    (hz : -p.2.2.2 ∈ slitPlane) (n : ℕ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      ∫ y : ℝ in (-(n : ℝ))..(n : ℝ),
        mellinBarnesIntegrand q.1 q.2.1 q.2.2.1 q.2.2.2 (σ + y * I)) p := by
  have hn_le : -(n : ℝ) ≤ (n : ℝ) := by linarith [n.cast_nonneg (α := ℝ)]
  let γ : ℝ → ℂ := fun y => (σ : ℂ) + (projIcc (-(n : ℝ)) n hn_le y : ℝ) * I
  let K : Set ℂ := (fun y : ℝ => (σ : ℂ) + y * I) '' Icc (-(n : ℝ)) n
  have hγ : Continuous γ :=
    continuous_const.add ((continuous_ofReal.comp
      (continuous_subtypeVal.comp continuous_projIcc)).mul continuous_const)
  have hkernel : ∀ t ∈ K, AnalyticAt ℂ
      (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        mellinBarnesIntegrand x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2)
      (p, t) := by
    rintro _ ⟨y, _, rfl⟩
    exact analyticAt_mellinBarnesIntegrand_uncurry_vertical ha hb hσ hz y
  refine (TauCeti.analyticAt_integral_smul (isCompact_Icc.image (by fun_prop)) hγ
    (fun y => ⟨_, (projIcc (-(n : ℝ)) n hn_le y).property, rfl⟩) hkernel
    (integrable_const (1 : ℂ) : Integrable _ (volume.restrict (Ioc (-(n : ℝ)) n)))).congr
    (Eventually.of_forall fun q => ?_)
  dsimp only
  rw [intervalIntegral.integral_of_le hn_le]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  simp only [one_smul, γ, projIcc_of_mem hn_le (Ioc_subset_Icc_self hy)]

private theorem tendstoUniformlyOn_truncated_vertical_mellinBarnes {p₀ : ℂ × ℂ × ℂ × ℂ}
    {σ δ₀ δ₁ ρ : ℝ} (hσ : ∀ m : ℕ, σ ≠ m) (hδ₀_le : δ₀ ≤ 1 / 2) (hδ₁_le : δ₁ ≤ 1 / 2)
    (hav₀ : ∀ w ∈ ball p₀.1 δ₀, ∀ k : ℕ, w.re + σ ≠ -k)
    (hav₁ : ∀ w ∈ ball p₀.2.1 δ₁, ∀ k : ℕ, w.re + σ ≠ -k)
    (hz₀ : -p₀.2.2.2 ∈ slitPlane)
    (hz_sub : ∀ z ∈ ball p₀.2.2.2 ρ, -z ∈ slitPlane ∧
      ‖p₀.2.2.2‖ / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * ‖p₀.2.2.2‖ ∧
        |(-z).arg| ≤ π - 2 * ((π - |(-p₀.2.2.2).arg|) / 4)) :
    TendstoUniformlyOn
      (fun (n : ℕ) (p : ℂ × ℂ × ℂ × ℂ) =>
        ∫ y : ℝ in (-(n : ℝ))..(n : ℝ),
          mellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2 (σ + y * I))
      (fun p : ℂ × ℂ × ℂ × ℂ =>
        ∫ y : ℝ, mellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2 (σ + y * I)) atTop
      (ball p₀.1 δ₀ ×ˢ ball p₀.2.1 δ₁ ×ˢ ball p₀.2.2.1 1 ×ˢ ball p₀.2.2.2 ρ) := by
  -- Fix a common parameter radius `R` and slit-plane sector margin `δ` on the product box.
  let δ : ℝ := (π - |(-p₀.2.2.2).arg|) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz₀]
  have hr₁ : 0 < ‖p₀.2.2.2‖ / 2 :=
    half_pos (norm_pos_iff.2 (neg_ne_zero.1 (slitPlane_ne_zero hz₀)))
  let R₁ : ℝ := max (‖p₀.1‖ + 1) (‖p₀.2.1‖ + 1)
  let R₂ : ℝ := max (‖p₀.2.2.1‖ + 1) |σ|
  let R : ℝ := max R₁ R₂ + 1
  obtain ⟨B, Y₀, _, _, hdom, htail⟩ := exists_norm_mellinBarnesIntegrand_vertical_le (R := R)
    (r₂ := 2 * ‖p₀.2.2.2‖) (by positivity) hr₁ hδ
  have hcov : AECover (volume : Measure ℝ) atTop (fun n : ℕ => Ioc (-(n : ℝ)) n) :=
    aecover_Ioc (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      tendsto_natCast_atTop_atTop
  -- Dominate the truncation tail `(-n, n)ᶜ` uniformly across the product box.
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(hcov.tendsto_setIntegral_compl_zero hdom).eventually (gt_mem_nhds hε),
    eventually_ge_atTop (⌈Y₀⌉₊ + 1)] with n hn_ε hn_Y p hp
  rw [dist_eq_norm]
  have hint_p : Integrable
      (fun y : ℝ => mellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2 (σ + y * I)) :=
    verticalIntegrable_mellinBarnesIntegrand p.2.2.1 (hav₀ p.1 hp.1) (hav₁ p.2.1 hp.2.1)
      hσ (hz_sub p.2.2.2 hp.2.2.2).1
  rw [intervalIntegral.integral_of_le (by linarith [n.cast_nonneg (α := ℝ)]),
    ← integral_add_compl (s := Ioc (-(n : ℝ)) n) measurableSet_Ioc hint_p, add_sub_cancel_left]
  refine (norm_integral_le_integral_norm _).trans_lt ((integral_mono_ae
    hint_p.norm.integrableOn hdom.integrableOn ?_).trans_lt hn_ε)
  filter_upwards [ae_restrict_mem measurableSet_Ioc.compl] with y hy
  have hyY : Y₀ ≤ |y| := by
    have hYN : Y₀ ≤ n := (Nat.le_ceil Y₀).trans
      (by exact_mod_cast (Nat.le_add_right _ 1).trans hn_Y)
    rw [mem_compl_iff, mem_Ioc, not_and_or] at hy
    rcases hy with h1 | h2
    · linarith [not_lt.1 h1, neg_le_abs y]
    · linarith [not_le.1 h2, le_abs_self y]
  have hR1 : R₁ ≤ R := (le_max_left R₁ R₂).trans (le_add_of_nonneg_right zero_le_one)
  have hR2 : R₂ ≤ R := (le_max_right R₁ R₂).trans (le_add_of_nonneg_right zero_le_one)
  have hp1R : ‖p.1‖ ≤ R := by
    linarith [norm_le_norm_sub_add p.1 p₀.1, (mem_ball_iff_norm.1 hp.1).le.trans hδ₀_le,
      (le_max_left (‖p₀.1‖ + 1) (‖p₀.2.1‖ + 1)).trans hR1]
  have hp2R : ‖p.2.1‖ ≤ R := by
    linarith [norm_le_norm_sub_add p.2.1 p₀.2.1, (mem_ball_iff_norm.1 hp.2.1).le.trans hδ₁_le,
      (le_max_right (‖p₀.1‖ + 1) (‖p₀.2.1‖ + 1)).trans hR1]
  have hp3R : ‖p.2.2.1‖ ≤ R := by
    linarith [norm_le_norm_sub_add p.2.2.1 p₀.2.2.1, (mem_ball_iff_norm.1 hp.2.2.1).le,
      (le_max_left (‖p₀.2.2.1‖ + 1) |σ|).trans hR2]
  have hσR : |σ| ≤ R := (le_max_right (‖p₀.2.2.1‖ + 1) |σ|).trans hR2
  have hzb := hz_sub p.2.2.2 hp.2.2.2
  exact htail p.1 p.2.1 p.2.2.1 p.2.2.2 σ y hp1R hp2R hp3R hzb.2.1 hzb.2.2.1 hzb.2.2.2 hσR hyY

private theorem analyticAt_vertical_mellinBarnes {p₀ : ℂ × ℂ × ℂ × ℂ} {σ : ℝ}
    (hσ : ∀ m : ℕ, σ ≠ m) (ha₀ : ∀ k : ℕ, p₀.1.re + σ ≠ -k)
    (hb₀ : ∀ k : ℕ, p₀.2.1.re + σ ≠ -k) (hz₀ : -p₀.2.2.2 ∈ slitPlane) :
    AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ × ℂ =>
      ∫ y : ℝ, mellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2 (σ + y * I)) p₀ := by
  obtain ⟨δ₀', hδ₀', hav₀'⟩ := p₀.1.exists_ball_re_add_ne_neg_natCast_and_lt_iff ha₀
  obtain ⟨δ₁', hδ₁', hav₁'⟩ := p₀.2.1.exists_ball_re_add_ne_neg_natCast_and_lt_iff hb₀
  let δ₀ : ℝ := min δ₀' (1 / 2)
  let δ₁ : ℝ := min δ₁' (1 / 2)
  have hδ₀ : 0 < δ₀ := lt_min hδ₀' (by norm_num)
  have hδ₁ : 0 < δ₁ := lt_min hδ₁' (by norm_num)
  have hav₀ (w : ℂ) (hw : w ∈ ball p₀.1 δ₀) := (hav₀' w (ball_subset_ball (min_le_left _ _) hw)).1
  have hav₁ (w : ℂ) (hw : w ∈ ball p₀.2.1 δ₁) := (hav₁' w (ball_subset_ball (min_le_left _ _) hw)).1
  let θ : ℝ := π - 2 * ((π - |(-p₀.2.2.2).arg|) / 4)
  obtain ⟨ρ, hρ, hsub⟩ := exists_ball_slitPlane_norm_arg_le (θ := θ) hz₀
    (by simp only [θ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz₀])
  have hz_sub (z : ℂ) (hz : z ∈ ball p₀.2.2.2 ρ) :
      -z ∈ slitPlane ∧ ‖p₀.2.2.2‖ / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * ‖p₀.2.2.2‖ ∧ |(-z).arg| ≤ θ := by
    simpa only [norm_neg] using hsub (-z) (by simpa [mem_ball, dist_neg_neg] using hz)
  let U : Set (ℂ × ℂ × ℂ × ℂ) :=
    ball p₀.1 δ₀ ×ˢ ball p₀.2.1 δ₁ ×ˢ ball p₀.2.2.1 1 ×ˢ ball p₀.2.2.2 ρ
  have hU_open : IsOpen U := isOpen_ball.prod (isOpen_ball.prod (isOpen_ball.prod isOpen_ball))
  have hp₀U : p₀ ∈ U :=
    ⟨mem_ball_self hδ₀, mem_ball_self hδ₁, mem_ball_self zero_lt_one, mem_ball_self hρ⟩
  have hunif := tendstoUniformlyOn_truncated_vertical_mellinBarnes hσ (min_le_right _ _)
    (min_le_right _ _) hav₀ hav₁ hz₀ hz_sub
  have hF_an (n : ℕ) (p : ℂ × ℂ × ℂ × ℂ) (hp : p ∈ U) :=
    analyticAt_truncated_vertical_mellinBarnes hσ (hav₀ p.1 hp.1)
      (hav₁ p.2.1 hp.2.1) (hz_sub p.2.2.2 hp.2.2.2).1 n
  exact (hunif.differentiableOn
    (Eventually.of_forall fun n p hp => (hF_an n p hp).differentiableAt.differentiableWithinAt)
    hU_open).analyticAt_of_finiteDimensional (hU_open.mem_nhds hp₀U)

/-- **Joint four-variable holomorphy of the vertical-line Mellin–Barnes integral.** For any
abscissa `σ : ℝ` avoiding `ℕ`, the vertical-line integral
`p ↦ ∫ y : ℝ, mellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2 (σ + y * I)` is jointly analytic on
`{p | (∀ k : ℕ, p.1.re + σ ≠ -k) ∧ (∀ k : ℕ, p.2.1.re + σ ≠ -k) ∧ -p.2.2.2 ∈ slitPlane}`. -/
theorem analyticOnNhd_integral_mellinBarnesIntegrand {σ : ℝ} (hσ : ∀ m : ℕ, σ ≠ m) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ × ℂ =>
      ∫ y : ℝ, mellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2 (σ + y * I))
      {p | (∀ k : ℕ, p.1.re + σ ≠ -k) ∧ (∀ k : ℕ, p.2.1.re + σ ≠ -k) ∧
        -p.2.2.2 ∈ slitPlane} :=
  fun _ ⟨ha₀, hb₀, hz₀⟩ => analyticAt_vertical_mellinBarnes hσ ha₀ hb₀ hz₀

private theorem exists_isolating_radius_mellinBarnesLeftPoles {a₀ b₀ : ℂ} (σ : ℝ)
    (ha₀ : ∀ k : ℕ, a₀ ≠ -k) (hb₀ : ∀ k : ℕ, b₀ ≠ -k) :
    ∃ r : ℝ, 0 < r ∧
      (∀ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, σ + r < s.re) ∧
      (∀ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, ∀ m : ℕ, r < ‖s - m‖) ∧
      (∀ s₁ ∈ mellinBarnesLeftPoles a₀ b₀ σ, ∀ s₂ ∈ mellinBarnesLeftPoles a₀ b₀ σ,
        s₁ ≠ s₂ → 2 * r < dist s₁ s₂) := by
  set P₀ : Finset ℂ := mellinBarnesLeftPoles a₀ b₀ σ
  let U : Set ℂ := {s : ℂ | σ < s.re} \ range ((↑) : ℕ → ℂ)
  have hU_open : IsOpen U := (isOpen_lt continuous_const continuous_re).sdiff isClosed_range_natCast
  have hU_mem : ∀ s ∈ P₀, U ∈ 𝓝 s := fun s hs => by
    refine hU_open.mem_nhds ⟨(mem_mellinBarnesLeftPoles.1 hs).1, ?_⟩
    rintro ⟨m, hm⟩
    rcases (mem_mellinBarnesLeftPoles.1 hs).2 with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ha₀ (k + m) (by push_cast; linear_combination hm)
    · exact hb₀ (k + m) (by push_cast; linear_combination hm)
  obtain ⟨r, hr, hsub, hsep⟩ := TauCeti.exists_pos_closedBall_subset_and_lt_dist (T := P₀) hU_mem
  refine ⟨r, hr, fun s hs => ?_, fun s hs m => ?_, hsep⟩
  · have hmem : s - (r : ℂ) ∈ U := hsub s hs (by simp [mem_closedBall, abs_of_pos hr])
    have hre : σ < (s - (r : ℂ)).re := hmem.1
    simp only [sub_re, ofReal_re] at hre
    linarith
  · by_contra! hle
    have hmem : (m : ℂ) ∈ U :=
      hsub s hs (by simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hle)
    exact hmem.2 ⟨m, rfl⟩

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
    rw [mem_ball_iff_norm, sub_sub_sub_cancel_right, neg_sub_neg, norm_sub_rev]
    linarith [norm_nonneg (a - a₀)]
  · refine ⟨-b₀ - k, mem_mellinBarnesLeftPoles.2 ⟨lt_of_le_of_ne
      (not_lt.1 fun h => hw_re.not_gt (hb_cross k h)) (fun h => hb₀_σ k (by simp at h; linarith)),
      Or.inr ⟨k, rfl⟩⟩, ?_⟩
    rw [mem_ball_iff_norm, sub_sub_sub_cancel_right, neg_sub_neg, norm_sub_rev]
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
  -- Partition `P` into the pairwise disjoint isolating balls `B(s, r)` centered at `s ∈ P₀`.
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
  -- Every negative-order pole in `closedBall s r` lies in `F s`, so the circle residue theorem
  -- applies.
  have hsupp : ∀ w ∈ closedBall s r,
      meromorphicOrderAt (mellinBarnesIntegrand a b c z) w < 0 → w ∈ F s := fun w hw hord => by
    have hpole : (∃ k : ℕ, w = -a - k) ∨ (∃ k : ℕ, w = -b - k) := by
      by_contra hno; push Not at hno
      refine hord.not_ge (analyticAt_mellinBarnesIntegrand a b c z hno.1 hno.2
        fun m hm => ?_).meromorphicOrderAt_nonneg
      have h1 : ‖s - m‖ ≤ r := by
        rw [← dist_eq_norm, dist_comm, ← hm]
        exact mem_closedBall.1 hw
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
  rw [hcirc, inv_mul_cancel_left₀ two_pi_I_ne_zero]

private theorem analyticAt_circleIntegral_mellinBarnes_term {p₀ : ℂ × ℂ × ℂ × ℂ} {σ r : ℝ}
    (hr : 0 < r)
    (hre : ∀ s ∈ mellinBarnesLeftPoles p₀.1 p₀.2.1 σ, σ + r < s.re)
    (hnat : ∀ s ∈ mellinBarnesLeftPoles p₀.1 p₀.2.1 σ, ∀ m : ℕ, r < ‖s - m‖)
    (hsep : ∀ s₁ ∈ mellinBarnesLeftPoles p₀.1 p₀.2.1 σ,
      ∀ s₂ ∈ mellinBarnesLeftPoles p₀.1 p₀.2.1 σ, s₁ ≠ s₂ → 2 * r < dist s₁ s₂)
    (hz₀ : -p₀.2.2.2 ∈ slitPlane)
    {s : ℂ} (hs : s ∈ mellinBarnesLeftPoles p₀.1 p₀.2.1 σ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ × ℂ =>
      (2 * (π : ℂ) * I)⁻¹ * ∮ ζ in C(s, r),
        mellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2 ζ) p₀ := by
  refine analyticAt_const.mul (TauCeti.analyticAt_circleIntegral (c := s) (R := r) (p₀ := p₀)
    (f := fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
      mellinBarnesIntegrand q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
    fun ζ hζ => ?_)
  rw [abs_of_pos hr] at hζ
  have hζ_re : σ < ζ.re := by
    have h1 : |ζ.re - s.re| ≤ r := (abs_re_le_norm (ζ - s)).trans (mem_sphere_iff_norm.1 hζ).le
    linarith [(abs_le.1 h1).1, hre s hs]
  have hnot_P₀ : ζ ∉ mellinBarnesLeftPoles p₀.1 p₀.2.1 σ := fun hζP => by
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
        rw [← dist_eq_norm, dist_comm, ← (by linear_combination -hm : ζ = m)]
        exact mem_sphere.1 hζ
      linarith [hnat s hs m]) hz₀

private theorem analyticAt_residueSum_mellinBarnes {p₀ : ℂ × ℂ × ℂ × ℂ} {σ : ℝ}
    (ha₀ : ∀ k : ℕ, p₀.1 ≠ -k) (hb₀ : ∀ k : ℕ, p₀.2.1 ≠ -k)
    (ha₀_σ : ∀ k : ℕ, p₀.1.re + σ ≠ -k) (hb₀_σ : ∀ k : ℕ, p₀.2.1.re + σ ≠ -k)
    (hz₀ : -p₀.2.2.2 ∈ slitPlane) :
    AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ × ℂ =>
      ∑ w ∈ mellinBarnesLeftPoles p.1 p.2.1 σ,
        TauCeti.Contour.residue (mellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2) w) p₀ := by
  obtain ⟨r, hr, hre, hnat, hsep⟩ := exists_isolating_radius_mellinBarnesLeftPoles σ ha₀ hb₀
  obtain ⟨δ₀, hδ₀, hav₀⟩ := p₀.1.exists_ball_re_add_ne_neg_natCast_and_lt_iff ha₀_σ
  obtain ⟨δ₁, hδ₁, hav₁⟩ := p₀.2.1.exists_ball_re_add_ne_neg_natCast_and_lt_iff hb₀_σ
  let δ_ab : ℝ := min (r / 2) (min δ₀ δ₁)
  have hδ_ab : 0 < δ_ab := lt_min (by positivity) (lt_min hδ₀ hδ₁)
  have hU_nhds : (ball p₀.1 δ_ab ×ˢ ball p₀.2.1 δ_ab ×ˢ (univ : Set (ℂ × ℂ))) ∈ 𝓝 p₀ :=
    (isOpen_ball.prod (isOpen_ball.prod isOpen_univ)).mem_nhds
      ⟨mem_ball_self hδ_ab, mem_ball_self hδ_ab, mem_univ _⟩
  refine (Finset.analyticAt_fun_sum (mellinBarnesLeftPoles p₀.1 p₀.2.1 σ) fun _ hs =>
    analyticAt_circleIntegral_mellinBarnes_term hr hre hnat hsep hz₀ hs).congr ?_
  filter_upwards [hU_nhds] with p hp
  exact (residueSum_eq_sum_circleIntegral_mellinBarnes p.2.2.1 p.2.2.2 hr hre hnat hsep ha₀_σ hb₀_σ
    ((mem_ball_iff_norm.1 hp.1).trans_le (min_le_left _ _))
    ((mem_ball_iff_norm.1 hp.2.1).trans_le (min_le_left _ _))
    (fun k =>
      ((hav₀ p.1 (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hp.1)).2 k).1)
    (fun k =>
      ((hav₁ p.2.1 (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hp.2.1)).2
        k).1)).symm

/-- **Joint four-variable holomorphy of the separating-contour Mellin–Barnes integral.** On
`{p | (∀ k : ℕ, a ≠ -k) ∧ (∀ k : ℕ, b ≠ -k) ∧ -z ∈ slitPlane}`, `mellinBarnesIntegral a b c z` is
jointly analytic in `(a, b, c, z)` across all lower parameters `c : ℂ` and across integer
differences `a - b ∈ ℤ`. -/
theorem analyticOnNhd_mellinBarnesIntegral :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ × ℂ => mellinBarnesIntegral p.1 p.2.1 p.2.2.1 p.2.2.2)
      {p | (∀ k : ℕ, p.1 ≠ -k) ∧ (∀ k : ℕ, p.2.1 ≠ -k) ∧ -p.2.2.2 ∈ slitPlane} := by
  rintro p₀ ⟨ha₀, hb₀, hz₀⟩
  let σ : ℝ := mellinBarnesAbscissa p₀.1 p₀.2.1
  have hσ : σ < 0 := mellinBarnesAbscissa_lt_zero p₀.1 p₀.2.1
  obtain ⟨ha₀_σ, hb₀_σ⟩ := mellinBarnesAbscissa_avoid p₀.1 p₀.2.1
  obtain ⟨δ₀, hδ₀, hav₀⟩ := p₀.1.exists_ball_re_add_ne_neg_natCast_and_lt_iff ha₀_σ
  obtain ⟨δ₁, hδ₁, hav₁⟩ := p₀.2.1.exists_ball_re_add_ne_neg_natCast_and_lt_iff hb₀_σ
  have hU_nhds : (ball p₀.1 δ₀ ×ˢ ball p₀.2.1 δ₁ ×ˢ univ ×ˢ {z : ℂ | -z ∈ slitPlane}) ∈ 𝓝 p₀ :=
    (isOpen_ball.prod (isOpen_ball.prod (isOpen_univ.prod
      (isOpen_slitPlane.preimage continuous_neg)))).mem_nhds
      ⟨mem_ball_self hδ₀, mem_ball_self hδ₁, mem_univ _, hz₀⟩
  refine (((analyticAt_const (v := (2 * π : ℂ)⁻¹)).mul
    (analyticAt_vertical_mellinBarnes (fun m _ => by linarith [m.cast_nonneg (α := ℝ)])
      ha₀_σ hb₀_σ hz₀)).add
    (analyticAt_residueSum_mellinBarnes ha₀ hb₀ ha₀_σ hb₀_σ hz₀)).congr ?_
  filter_upwards [hU_nhds] with p hp
  dsimp only [Pi.add_apply, Pi.mul_apply]
  rw [mellinBarnesIntegral_eq_mellinBarnesSeparatingIntegral p.2.2.1 hσ
    (hav₀ p.1 hp.1).1 (hav₁ p.2.1 hp.2.1).1 hp.2.2.2,
    mellinBarnesSeparatingIntegral_def]

end Complex
