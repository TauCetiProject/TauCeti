/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Barnes.IntegrandBounds
import Mathlib.Analysis.Analytic.Constructions
import TauCeti.Algebra.Order.Ring.Abs
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy
import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Canonical separating-contour continuation and joint four-variable holomorphy

This module defines the canonical abscissa-independent separating-contour Mellin–Barnes integral
`Complex.mellinBarnesIntegral`. In `Barnes/Continuation.lean`, for `a, b ∉ -ℕ` it is shown to
agree with `Γ(a) Γ(b) 𝐅(a, b; c; z)` (and hence `(Γ(a) Γ(b) / Γ(c)) ₂F₁(a, b; c; z)` when also
`c ∉ -ℕ`) on `‖z‖ < 1` with `-z ∈ Complex.slitPlane`, and for `a ∉ -ℕ` with
`Γ(a) Γ(b) Complex.eulerIntegral a b c z` when `0 < Re b < Re c` and `-z ∈ Complex.slitPlane`,
providing the analytic continuation of `Γ(a) Γ(b) 𝐅(a, b; c; z)` to the cut plane
`-z ∈ Complex.slitPlane` for `a, b ∉ -ℕ` and all `c : ℂ` (including resonant integer differences
`a - b ∈ ℤ`, where simple pole candidates coalesce, potentially producing double poles though
reciprocal Gamma zeros can lower their order or cancel the pole):
* for fixed `σ < 0`, `Complex.hypergeometricMellinBarnes` is jointly holomorphic on the domain
  where `a, b ∉ -ℕ`, `-z ∈ Complex.slitPlane`, and additionally `∀ k : ℕ, a.re + σ ≠ -k` and
  `∀ k : ℕ, b.re + σ ≠ -k` (avoiding poles on the vertical line `Re t = σ`);
* `Complex.mellinBarnesIntegral` is jointly holomorphic on
  `{(a, b, c, z) | a ∉ -ℕ ∧ b ∉ -ℕ ∧ -z ∈ Complex.slitPlane}`.

Locally around `(a₀, b₀, c₀, z₀)`, fixing `σ < 0` avoiding `-Re a₀ - ℕ` and `-Re b₀ - ℕ`, joint
holomorphy of the vertical integral follows from `TauCeti.analyticOnNhd_integral_of_dominated`,
combining uniform Stirling decay on the vertical tails with a uniform bound on the compact
central segment; joint holomorphy of the finite residue sum follows by rewriting it via
`TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg` as a sum of Cauchy
circle integrals around isolating circles.

## Main definitions and results

* `Complex.mellinBarnesIntegral`, `Complex.mellinBarnesIntegral_symm`,
  `Complex.mellinBarnesIntegral_eq_hypergeometricMellinBarnes`,
  `Complex.exists_mellinBarnesIntegral_eq_hypergeometricMellinBarnes`,
  `Complex.mellinBarnesIntegral_of_neg_re_lt`.
* `Complex.analyticOnNhd_integral_hypergeometricMellinBarnesIntegrand`: joint four-variable
  holomorphy of the vertical-line integral along any fixed `Re t = σ` (`σ ∉ ℕ`).
* `Complex.analyticOnNhd_hypergeometricMellinBarnes`,
  `Complex.analyticOnNhd_mellinBarnesIntegral`, `AnalyticAt.mellinBarnesIntegral`: joint
  four-variable holomorphy and analytic composition of `hypergeometricMellinBarnes` (for fixed
  `σ < 0`) and `mellinBarnesIntegral` in `(a, b, c, z)`.

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

/-- **Canonical separating-contour Mellin–Barnes integral**. For `a, b ∉ -ℕ`, it agrees with
`Γ(a) Γ(b) 𝐅(a, b; c; z)` (and `(Γ(a) Γ(b) / Γ(c)) ₂F₁(a, b; c; z)` when also `c ∉ -ℕ`) on
`‖z‖ < 1` with `-z ∈ Complex.slitPlane` (see
`Complex.regularizedGaussHGFun_eq_mellinBarnesRegularizedGaussHGFun` and
`Complex.ordinaryHypergeometric_eq_mellinBarnesOrdinaryHypergeometric` in
`Barnes/Continuation.lean`). For `a ∉ -ℕ`, it agrees with `Γ(a) Γ(b) eulerIntegral a b c z` when
`0 < Re b < Re c` and `-z ∈ Complex.slitPlane` (see
`Complex.eulerIntegral_eq_mellinBarnesRegularizedGaussHGFun` in `Barnes/Continuation.lean`). It
provides the analytic continuation of `Γ(a) Γ(b) 𝐅(a, b; c; z)` to the cut plane
`-z ∈ Complex.slitPlane` for `a, b ∉ -ℕ` and all `c : ℂ`. Evaluated at a canonical negative
abscissa avoiding `-Re a - ℕ` and `-Re b - ℕ`, this agrees with
`hypergeometricMellinBarnes a b c z σ` for every admissible negative abscissa `σ < 0` when
`-z ∈ slitPlane`. -/
def mellinBarnesIntegral (a b c z : ℂ) : ℂ :=
  hypergeometricMellinBarnes a b c z (mellinBarnesAbscissa a b)

/-- Symmetry of `mellinBarnesIntegral` in `a` and `b`. -/
theorem mellinBarnesIntegral_symm (a b c z : ℂ) :
    mellinBarnesIntegral a b c z = mellinBarnesIntegral b a c z := by
  rw [mellinBarnesIntegral, mellinBarnesIntegral, mellinBarnesAbscissa_symm a b,
    hypergeometricMellinBarnes_comm a b c z]

/-- On `-z ∈ slitPlane`, `mellinBarnesIntegral a b c z` equals
`hypergeometricMellinBarnes a b c z σ` for every negative abscissa `σ < 0` avoiding
`-Re a - ℕ` and `-Re b - ℕ`. -/
theorem mellinBarnesIntegral_eq_hypergeometricMellinBarnes {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (hσ : σ < 0) (ha : ∀ k : ℕ, a.re + σ ≠ -k) (hb : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz : -z ∈ slitPlane) :
    mellinBarnesIntegral a b c z = hypergeometricMellinBarnes a b c z σ :=
  hypergeometricMellinBarnes_eq a b c hz (mellinBarnesAbscissa_lt_zero a b) hσ
    (mellinBarnesAbscissa_avoid a b).1 (mellinBarnesAbscissa_avoid a b).2 ha hb

/-- Every `(a, b, c, z)` admits a negative abscissa `σ < 0` avoiding `-Re a - ℕ` and `-Re b - ℕ`
at which `mellinBarnesIntegral a b c z = hypergeometricMellinBarnes a b c z σ`. -/
theorem exists_mellinBarnesIntegral_eq_hypergeometricMellinBarnes (a b c z : ℂ) :
    ∃ σ : ℝ, σ < 0 ∧ (∀ k : ℕ, a.re + σ ≠ -k) ∧ (∀ k : ℕ, b.re + σ ≠ -k) ∧
      mellinBarnesIntegral a b c z = hypergeometricMellinBarnes a b c z σ :=
  ⟨mellinBarnesAbscissa a b, mellinBarnesAbscissa_lt_zero a b,
    (mellinBarnesAbscissa_avoid a b).1, (mellinBarnesAbscissa_avoid a b).2, rfl⟩

/-- When `-Re a < σ`, `-Re b < σ`, `σ < 0`, and `-z ∈ slitPlane`, the canonical Mellin–Barnes
integral reduces to the straight vertical-line integral along `Re t = σ`. -/
theorem mellinBarnesIntegral_of_neg_re_lt {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (ha : -a.re < σ) (hb : -b.re < σ) (hσ : σ < 0) (hz : -z ∈ slitPlane) :
    mellinBarnesIntegral a b c z =
      (2 * π : ℂ)⁻¹ * ∫ y : ℝ, hypergeometricMellinBarnesIntegrand a b c z (σ + y * I) := by
  rw [mellinBarnesIntegral_eq_hypergeometricMellinBarnes c hσ
      (fun k _ => by linarith [k.cast_nonneg (α := ℝ)])
      (fun k _ => by linarith [k.cast_nonneg (α := ℝ)]) hz,
    hypergeometricMellinBarnes_eq_integral a b c z ha.le hb.le]

/-- **Joint four-variable holomorphy of the vertical-line Mellin–Barnes integral.** For any
abscissa `σ : ℝ` avoiding `ℕ`, the vertical-line integral
`p ↦ ∫ y : ℝ, hypergeometricMellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2 (σ + y * I)` is
jointly analytic on
`{p | (∀ k : ℕ, p.1.re + σ ≠ -k) ∧ (∀ k : ℕ, p.2.1.re + σ ≠ -k) ∧ -p.2.2.2 ∈ slitPlane}`. -/
theorem analyticOnNhd_integral_hypergeometricMellinBarnesIntegrand {σ : ℝ} (hσ : ∀ m : ℕ, σ ≠ m) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ × ℂ =>
      ∫ y : ℝ, hypergeometricMellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2 (σ + y * I))
      {p | (∀ k : ℕ, p.1.re + σ ≠ -k) ∧ (∀ k : ℕ, p.2.1.re + σ ≠ -k) ∧
        -p.2.2.2 ∈ slitPlane} := by
  let S : Set (ℂ × ℂ × ℂ × ℂ) :=
    {p | (∀ k : ℕ, p.1.re + σ ≠ -k) ∧ (∀ k : ℕ, p.2.1.re + σ ≠ -k) ∧ -p.2.2.2 ∈ slitPlane}
  have hS_open : IsOpen S := by
    have hcl : IsClosed ((fun x : ℝ => -(x + σ)) ⁻¹' range ((↑) : ℕ → ℝ)) :=
      Nat.isClosedEmbedding_coe_real.isClosed_range.preimage
        (continuous_neg.comp (continuous_id.add continuous_const))
    have h_av (f : ℂ × ℂ × ℂ × ℂ → ℂ) (hf : Continuous f) :
        IsOpen {p | ∀ k : ℕ, (f p).re + σ ≠ -k} := by
      have : {p | ∀ k : ℕ, (f p).re + σ ≠ -k} =
          (fun p => (f p).re) ⁻¹' ((fun x : ℝ => -(x + σ)) ⁻¹' range ((↑) : ℕ → ℝ))ᶜ := by
        ext p
        simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff, mem_range, not_exists]
        exact ⟨fun h k hk => h k (by linarith), fun h k hk => h k (by linarith)⟩
      rw [this]
      exact hcl.isOpen_compl.preimage (continuous_re.comp hf)
    exact (h_av (fun p => p.1) (by fun_prop)).inter
      ((h_av (fun p => p.2.1) (by fun_prop)).inter
        (isOpen_slitPlane.preimage (by fun_prop : Continuous fun p : ℂ × ℂ × ℂ × ℂ => -p.2.2.2)))
  refine TauCeti.analyticOnNhd_integral_of_dominated hS_open ?_ ?_ ?_
  · rintro p ⟨ha, hb, hz⟩
    exact (integrable_hypergeometricMellinBarnesIntegrand p.1 p.2.1 p.2.2.1 hz ha hb
      hσ).aestronglyMeasurable
  · rintro p₀ ⟨ha₀, hb₀, hz₀⟩
    obtain ⟨δ₀', hδ₀', hav₀'⟩ := exists_ball_re_add_ne_neg_natCast_and_lt_iff p₀.1 ha₀
    obtain ⟨δ₁', hδ₁', hav₁'⟩ := exists_ball_re_add_ne_neg_natCast_and_lt_iff p₀.2.1 hb₀
    let δ₀ : ℝ := min δ₀' (1 / 2)
    let δ₁ : ℝ := min δ₁' (1 / 2)
    have hδ₀ : 0 < δ₀ := lt_min hδ₀' (by norm_num)
    have hδ₁ : 0 < δ₁ := lt_min hδ₁' (by norm_num)
    let δ : ℝ := (π - |(-p₀.2.2.2).arg|) / 4
    have hδ : 0 < δ := by dsimp [δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz₀]
    let θ : ℝ := π - 2 * δ
    obtain ⟨ρ, hρ, hsub⟩ := exists_ball_slitPlane_norm_arg_le (θ := θ) hz₀
      (by simp only [θ, δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz₀])
    have hr₁ : 0 < ‖p₀.2.2.2‖ / 2 :=
      half_pos (norm_pos_iff.2 (neg_ne_zero.1 (slitPlane_ne_zero hz₀)))
    let R : ℝ := max (max (‖p₀.1‖ + 1) (‖p₀.2.1‖ + 1)) (max (‖p₀.2.2.1‖ + 1) |σ|)
    obtain ⟨B, Y₀, hB, _, hdom, htail⟩ :=
      exists_norm_hypergeometricMellinBarnesIntegrand_vertical_le
        (R := R) (r₂ := 2 * ‖p₀.2.2.2‖) hr₁ hδ
    let U : Set (ℂ × ℂ × ℂ × ℂ) :=
      closedBall p₀.1 (δ₀ / 2) ×ˢ closedBall p₀.2.1 (δ₁ / 2) ×ˢ
        closedBall p₀.2.2.1 (1 / 2) ×ˢ closedBall p₀.2.2.2 (ρ / 2)
    have hU_nhds : U ∈ 𝓝 p₀ :=
      prod_mem_nhds (closedBall_mem_nhds _ (half_pos hδ₀))
        (prod_mem_nhds (closedBall_mem_nhds _ (half_pos hδ₁))
          (prod_mem_nhds (closedBall_mem_nhds _ (by norm_num))
            (closedBall_mem_nhds _ (half_pos hρ))))
    have hU_sub : ∀ q ∈ U,
        (∀ k : ℕ, q.1.re + σ ≠ -k) ∧ (∀ k : ℕ, q.2.1.re + σ ≠ -k) ∧
        -q.2.2.2 ∈ slitPlane ∧ ‖p₀.2.2.2‖ / 2 ≤ ‖q.2.2.2‖ ∧ ‖q.2.2.2‖ ≤ 2 * ‖p₀.2.2.2‖ ∧
        |(-q.2.2.2).arg| ≤ θ ∧ ‖q.1‖ ≤ R ∧ ‖q.2.1‖ ≤ R ∧ ‖q.2.2.1‖ ≤ R ∧ |σ| ≤ R := by
      intro q hq
      have hq1 : q.1 ∈ ball p₀.1 δ₀' :=
        ball_subset_ball (min_le_left _ _) (closedBall_subset_ball (half_lt_self hδ₀) hq.1)
      have hq2 : q.2.1 ∈ ball p₀.2.1 δ₁' :=
        ball_subset_ball (min_le_left _ _) (closedBall_subset_ball (half_lt_self hδ₁) hq.2.1)
      have hq4 : -q.2.2.2 ∈ ball (-p₀.2.2.2) ρ := by
        simpa [mem_ball, dist_neg_neg] using closedBall_subset_ball (half_lt_self hρ) hq.2.2.2
      obtain ⟨hzq, hzr1, hzr2, harg⟩ := hsub (-q.2.2.2) hq4
      simp only [norm_neg] at hzr1 hzr2
      have hq1_le : ‖q.1‖ ≤ ‖p₀.1‖ + 1 := norm_le_norm_add_const_of_dist_le <|
        (mem_closedBall.1 hq.1).trans
          ((half_le_self hδ₀.le).trans ((min_le_right _ _).trans (by norm_num)))
      have hq2_le : ‖q.2.1‖ ≤ ‖p₀.2.1‖ + 1 := norm_le_norm_add_const_of_dist_le <|
        (mem_closedBall.1 hq.2.1).trans
          ((half_le_self hδ₁.le).trans ((min_le_right _ _).trans (by norm_num)))
      have hq3_le : ‖q.2.2.1‖ ≤ ‖p₀.2.2.1‖ + 1 := norm_le_norm_add_const_of_dist_le <|
        (mem_closedBall.1 hq.2.2.1).trans (by norm_num)
      exact ⟨(hav₀' q.1 hq1).1, (hav₁' q.2.1 hq2).1, hzq, hzr1, hzr2, harg,
        hq1_le.trans (by simp [R]), hq2_le.trans (by simp [R]), hq3_le.trans (by simp [R]),
        by simp [R]⟩
    have hK_compact : IsCompact (U ×ˢ Icc (-Y₀) Y₀) :=
      ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
        ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))).prod isCompact_Icc
    have hK_cont : ContinuousOn
        (fun x : (ℂ × ℂ × ℂ × ℂ) × ℝ =>
          hypergeometricMellinBarnesIntegrand x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 (σ + x.2 * I))
        (U ×ˢ Icc (-Y₀) Y₀) := by
      refine continuousOn_of_forall_continuousAt fun ⟨q, y⟩ ⟨hq, _⟩ => ?_
      have hqs := hU_sub q hq
      have han := analyticAt_hypergeometricMellinBarnesIntegrand_uncurry_vertical
        hqs.1 hqs.2.1 hσ hqs.2.2.1 y
      exact han.continuousAt.comp_of_eq
        (f := fun x : (ℂ × ℂ × ℂ × ℂ) × ℝ => (x.1, (σ : ℂ) + x.2 * I)) (by fun_prop) rfl
    obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn hK_cont
    let bound : ℝ → ℝ := fun y =>
      Set.indicator (Icc (-Y₀) Y₀) (fun _ => max C 0) y + B * Real.exp (-δ * |y|)
    have hbound_int : Integrable bound volume :=
      ((integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
        measurableSet_Icc).add hdom
    refine ⟨U, hU_nhds, bound, hbound_int, Eventually.of_forall fun y q hq => ?_⟩
    by_cases hy : |y| ≤ Y₀
    · have hyI : y ∈ Icc (-Y₀) Y₀ := abs_le.1 hy
      have hCy := hC (q, y) ⟨hq, hyI⟩
      have hpos : 0 ≤ B * Real.exp (-δ * |y|) := mul_nonneg hB (Real.exp_pos _).le
      dsimp only [bound]
      rw [Set.indicator_of_mem hyI]
      linarith [le_max_left C 0]
    · have hqs := hU_sub q hq
      have hty := htail q.1 q.2.1 q.2.2.1 q.2.2.2 σ y
        hqs.2.2.2.2.2.2.1 hqs.2.2.2.2.2.2.2.1 hqs.2.2.2.2.2.2.2.2.1
        hqs.2.2.2.1 hqs.2.2.2.2.1 hqs.2.2.2.2.2.1 hqs.2.2.2.2.2.2.2.2.2 (le_of_not_ge hy)
      have hind_nonneg : 0 ≤ Set.indicator (Icc (-Y₀) Y₀) (fun _ => max C 0) y :=
        Set.indicator_nonneg (fun _ _ => le_max_right C 0) _
      dsimp only [bound]
      linarith
  · refine Eventually.of_forall fun y p hp => ?_
    exact ((analyticAt_hypergeometricMellinBarnesIntegrand_uncurry_vertical
      hp.1 hp.2.1 hσ hp.2.2 y).comp_of_eq (analyticAt_id.prod analyticAt_const)
      rfl).differentiableAt.differentiableWithinAt

private theorem exists_isolating_radius_gammaPolesRightOf_union {a₀ b₀ : ℂ} (σ : ℝ)
    (ha₀ : ∀ k : ℕ, a₀ ≠ -k) (hb₀ : ∀ k : ℕ, b₀ ≠ -k) :
    ∃ r : ℝ, 0 < r ∧
      (∀ s ∈ gammaPolesRightOf a₀ σ ∪ gammaPolesRightOf b₀ σ,
        closedBall s r ⊆ {t : ℂ | σ < t.re} \ range ((↑) : ℕ → ℂ)) ∧
      (∀ s₁ ∈ gammaPolesRightOf a₀ σ ∪ gammaPolesRightOf b₀ σ,
        ∀ s₂ ∈ gammaPolesRightOf a₀ σ ∪ gammaPolesRightOf b₀ σ,
        s₁ ≠ s₂ → 2 * r < dist s₁ s₂) := by
  set P₀ : Finset ℂ := gammaPolesRightOf a₀ σ ∪ gammaPolesRightOf b₀ σ
  let U : Set ℂ := {s : ℂ | σ < s.re} \ range ((↑) : ℕ → ℂ)
  have hU_open : IsOpen U := (isOpen_lt continuous_const continuous_re).sdiff isClosed_range_natCast
  have hU_mem : ∀ s ∈ P₀, U ∈ 𝓝 s := fun s hs => by
    refine hU_open.mem_nhds ⟨(mem_gammaPolesRightOf_union.1 hs).1, ?_⟩
    rintro ⟨m, hm⟩
    rcases (mem_gammaPolesRightOf_union.1 hs).2 with ⟨k, rfl | rfl⟩
    · exact ha₀ (k + m) (by push_cast; linear_combination hm)
    · exact hb₀ (k + m) (by push_cast; linear_combination hm)
  exact TauCeti.exists_pos_closedBall_subset_and_lt_dist (T := P₀) hU_mem

private theorem neg_sub_natCast_mem_ball_of_re_gt {w₀ w : ℂ} {σ r : ℝ} {k : ℕ}
    (hw₀_σ : w₀.re + σ ≠ -k) (hw_dist : ‖w - w₀‖ < r)
    (hw_cross : (-w₀ - k).re < σ → (-w - k).re < σ)
    (hk : σ < (-w - k).re) :
    σ < (-w₀ - k).re ∧ (-w - k : ℂ) ∈ Metric.ball (-w₀ - k) r := by
  refine ⟨lt_of_le_of_ne (not_lt.1 fun h => hk.not_gt (hw_cross h))
    (fun h => hw₀_σ (by simp at h; linarith)), ?_⟩
  rwa [mem_ball_iff_norm, sub_sub_sub_cancel_right, neg_sub_neg, norm_sub_rev]

private theorem gammaPolesRightOf_union_cover {a₀ b₀ a b : ℂ} {σ r : ℝ}
    (ha₀_σ : ∀ k : ℕ, a₀.re + σ ≠ -k) (hb₀_σ : ∀ k : ℕ, b₀.re + σ ≠ -k)
    (ha_dist : ‖a - a₀‖ < r / 2) (hb_dist : ‖b - b₀‖ < r / 2)
    (ha_cross : ∀ k : ℕ, (-a₀ - k).re < σ → (-a - k).re < σ)
    (hb_cross : ∀ k : ℕ, (-b₀ - k).re < σ → (-b - k).re < σ) :
    ∀ w ∈ gammaPolesRightOf a σ ∪ gammaPolesRightOf b σ,
      ∃ s ∈ gammaPolesRightOf a₀ σ ∪ gammaPolesRightOf b₀ σ, w ∈ ball s r := by
  intro w hw
  rcases mem_gammaPolesRightOf_union.1 hw with ⟨hw_re, k, rfl | rfl⟩
  · obtain ⟨hre, hball⟩ := neg_sub_natCast_mem_ball_of_re_gt (ha₀_σ k)
      (r := r) (by linarith [norm_nonneg (a - a₀)]) (ha_cross k) hw_re
    exact ⟨-a₀ - k, mem_gammaPolesRightOf_union.2 ⟨hre, k, Or.inl rfl⟩, hball⟩
  · obtain ⟨hre, hball⟩ := neg_sub_natCast_mem_ball_of_re_gt (hb₀_σ k)
      (r := r) (by linarith [norm_nonneg (b - b₀)]) (hb_cross k) hw_re
    exact ⟨-b₀ - k, mem_gammaPolesRightOf_union.2 ⟨hre, k, Or.inr rfl⟩, hball⟩

private theorem residueSum_eq_sum_circleIntegral_hypergeometricMellinBarnes {a₀ b₀ a b : ℂ}
    (c z : ℂ) {σ r : ℝ} (hr : 0 < r)
    (hsub : ∀ s ∈ gammaPolesRightOf a₀ σ ∪ gammaPolesRightOf b₀ σ,
      closedBall s r ⊆ {t : ℂ | σ < t.re} \ range ((↑) : ℕ → ℂ))
    (hsep : ∀ s₁ ∈ gammaPolesRightOf a₀ σ ∪ gammaPolesRightOf b₀ σ,
      ∀ s₂ ∈ gammaPolesRightOf a₀ σ ∪ gammaPolesRightOf b₀ σ,
      s₁ ≠ s₂ → 2 * r < dist s₁ s₂)
    (ha₀_σ : ∀ k : ℕ, a₀.re + σ ≠ -k) (hb₀_σ : ∀ k : ℕ, b₀.re + σ ≠ -k)
    (ha_dist : ‖a - a₀‖ < r / 2) (hb_dist : ‖b - b₀‖ < r / 2)
    (ha_cross : ∀ k : ℕ, (-a₀ - k).re < σ → (-a - k).re < σ)
    (hb_cross : ∀ k : ℕ, (-b₀ - k).re < σ → (-b - k).re < σ) :
    (∑ w ∈ gammaPolesRightOf a σ ∪ gammaPolesRightOf b σ,
      TauCeti.Contour.residue (hypergeometricMellinBarnesIntegrand a b c z) w) =
      ∑ s ∈ gammaPolesRightOf a₀ σ ∪ gammaPolesRightOf b₀ σ,
        (2 * (π : ℂ) * I)⁻¹ *
          ∮ ζ in C(s, r), hypergeometricMellinBarnesIntegrand a b c z ζ := by
  classical
  -- Partition `P` into the pairwise disjoint isolating balls `B(s, r)` centered at `s ∈ P₀`.
  set P₀ : Finset ℂ := gammaPolesRightOf a₀ σ ∪ gammaPolesRightOf b₀ σ
  set P : Finset ℂ := gammaPolesRightOf a σ ∪ gammaPolesRightOf b σ
  let F : ℂ → Finset ℂ := fun s => P.filter (· ∈ ball s r)
  have hcover := gammaPolesRightOf_union_cover ha₀_σ hb₀_σ ha_dist hb_dist ha_cross hb_cross
  have hclosed_disj : ∀ s₁ ∈ P₀, ∀ s₂ ∈ P₀, s₁ ≠ s₂ →
      Disjoint (closedBall s₁ r) (closedBall s₂ r) := fun s₁ hs₁ s₂ hs₂ hne =>
    closedBall_disjoint_closedBall (by linarith [hsep s₁ hs₁ s₂ hs₂ hne])
  have hdisj : (P₀ : Set ℂ).PairwiseDisjoint F := fun s₁ hs₁ s₂ hs₂ hne =>
    Finset.disjoint_left.2 fun w hw₁ hw₂ =>
      (hclosed_disj s₁ hs₁ s₂ hs₂ hne).notMem_of_mem_left
        (ball_subset_closedBall (Finset.mem_filter.1 hw₁).2)
        (ball_subset_closedBall (Finset.mem_filter.1 hw₂).2)
  have hbiU : P₀.biUnion F = P := by
    ext w; simp only [Finset.mem_biUnion, F, Finset.mem_filter]
    exact ⟨fun ⟨_, _, hw, _⟩ => hw, fun hw =>
      let ⟨s, hs, hws⟩ := hcover w hw; ⟨s, hs, hw, hws⟩⟩
  rw [← hbiU, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun s hs => ?_
  -- Every negative-order pole in `closedBall s r` lies in `F s`, so the circle residue theorem
  -- applies.
  have hsupp : ∀ w ∈ closedBall s r,
      meromorphicOrderAt (hypergeometricMellinBarnesIntegrand a b c z) w < 0 →
        w ∈ F s := fun w hw hord => by
    have hw_mem := hsub s hs hw
    have hpole : (∃ k : ℕ, w = -a - k) ∨ (∃ k : ℕ, w = -b - k) := by
      by_contra hno; push Not at hno
      exact hord.not_ge (analyticAt_hypergeometricMellinBarnesIntegrand a b c z hno.1 hno.2
        fun m hm => hw_mem.2 ⟨m, hm.symm⟩).meromorphicOrderAt_nonneg
    have hwP : w ∈ P := mem_gammaPolesRightOf_union.2
      ⟨hw_mem.1, by
        rcases hpole with ⟨k, h⟩ | ⟨k, h⟩ <;> [exact ⟨k, Or.inl h⟩; exact ⟨k, Or.inr h⟩]⟩
    obtain ⟨s', hs', hws'⟩ := hcover w hwP
    have hs_eq : s' = s := by
      by_contra hne
      exact (hclosed_disj s' hs' s hs hne).notMem_of_mem_left
        (ball_subset_closedBall hws') hw
    subst hs_eq; exact Finset.mem_filter.2 ⟨hwP, hws'⟩
  have hcirc := TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hr (F s)
    (fun ζ _ => meromorphicAt_hypergeometricMellinBarnesIntegrand a b c z ζ)
    (fun ζ hζ => (Finset.mem_filter.1 hζ).2) hsupp
  rw [hcirc, inv_mul_cancel_left₀ two_pi_I_ne_zero]

private theorem analyticAt_circleIntegral_hypergeometricMellinBarnes_term {p₀ : ℂ × ℂ × ℂ × ℂ}
    {σ r : ℝ} (hr : 0 < r)
    (hsub : ∀ s ∈ gammaPolesRightOf p₀.1 σ ∪ gammaPolesRightOf p₀.2.1 σ,
      closedBall s r ⊆ {t : ℂ | σ < t.re} \ range ((↑) : ℕ → ℂ))
    (hsep : ∀ s₁ ∈ gammaPolesRightOf p₀.1 σ ∪ gammaPolesRightOf p₀.2.1 σ,
      ∀ s₂ ∈ gammaPolesRightOf p₀.1 σ ∪ gammaPolesRightOf p₀.2.1 σ,
      s₁ ≠ s₂ → 2 * r < dist s₁ s₂)
    (hz₀ : -p₀.2.2.2 ∈ slitPlane)
    {s : ℂ} (hs : s ∈ gammaPolesRightOf p₀.1 σ ∪ gammaPolesRightOf p₀.2.1 σ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ × ℂ =>
      (2 * (π : ℂ) * I)⁻¹ *
        ∮ ζ in C(s, r), hypergeometricMellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2 ζ) p₀ := by
  refine analyticAt_const.mul (TauCeti.analyticAt_circleIntegral (c := s) (R := r) (p₀ := p₀)
    (f := fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
      hypergeometricMellinBarnesIntegrand q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
    fun ζ hζ => ?_)
  rw [abs_of_pos hr] at hζ
  have hζ_mem := hsub s hs (sphere_subset_closedBall hζ)
  have hnot_P₀ : ζ ∉ gammaPolesRightOf p₀.1 σ ∪ gammaPolesRightOf p₀.2.1 σ := fun hζP => by
    by_cases heq : ζ = s
    · subst heq; simp at hζ; linarith
    · linarith [mem_sphere.1 hζ, hsep ζ hζP s hs heq]
  exact analyticAt_hypergeometricMellinBarnesIntegrand_uncurry
    (fun k hk => hnot_P₀ (mem_gammaPolesRightOf_union.2
      ⟨hζ_mem.1, k, Or.inl (by linear_combination hk)⟩))
    (fun k hk => hnot_P₀ (mem_gammaPolesRightOf_union.2
      ⟨hζ_mem.1, k, Or.inr (by linear_combination hk)⟩))
    (fun m hm => hζ_mem.2 ⟨m, neg_inj.1 hm.symm⟩) hz₀

private theorem analyticAt_residueSum_hypergeometricMellinBarnes {p₀ : ℂ × ℂ × ℂ × ℂ} {σ : ℝ}
    (ha₀ : ∀ k : ℕ, p₀.1 ≠ -k) (hb₀ : ∀ k : ℕ, p₀.2.1 ≠ -k)
    (ha₀_σ : ∀ k : ℕ, p₀.1.re + σ ≠ -k) (hb₀_σ : ∀ k : ℕ, p₀.2.1.re + σ ≠ -k)
    (hz₀ : -p₀.2.2.2 ∈ slitPlane) :
    AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ × ℂ =>
      ∑ w ∈ gammaPolesRightOf p.1 σ ∪ gammaPolesRightOf p.2.1 σ,
        TauCeti.Contour.residue
          (hypergeometricMellinBarnesIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2) w) p₀ := by
  obtain ⟨r, hr, hsub, hsep⟩ := exists_isolating_radius_gammaPolesRightOf_union σ ha₀ hb₀
  obtain ⟨δ₀, hδ₀, hav₀⟩ := exists_ball_re_add_ne_neg_natCast_and_lt_iff p₀.1 ha₀_σ
  obtain ⟨δ₁, hδ₁, hav₁⟩ := exists_ball_re_add_ne_neg_natCast_and_lt_iff p₀.2.1 hb₀_σ
  let δ_ab : ℝ := min (r / 2) (min δ₀ δ₁)
  have hδ_ab : 0 < δ_ab := lt_min (by positivity) (lt_min hδ₀ hδ₁)
  have hU_nhds : (ball p₀.1 δ_ab ×ˢ ball p₀.2.1 δ_ab ×ˢ (univ : Set (ℂ × ℂ))) ∈ 𝓝 p₀ :=
    (isOpen_ball.prod (isOpen_ball.prod isOpen_univ)).mem_nhds
      ⟨mem_ball_self hδ_ab, mem_ball_self hδ_ab, mem_univ _⟩
  refine (Finset.analyticAt_fun_sum
    (gammaPolesRightOf p₀.1 σ ∪ gammaPolesRightOf p₀.2.1 σ) fun _ hs =>
      analyticAt_circleIntegral_hypergeometricMellinBarnes_term hr hsub hsep hz₀ hs).congr ?_
  filter_upwards [hU_nhds] with p hp
  exact (residueSum_eq_sum_circleIntegral_hypergeometricMellinBarnes p.2.2.1 p.2.2.2 hr hsub hsep
    ha₀_σ hb₀_σ ((mem_ball_iff_norm.1 hp.1).trans_le (min_le_left _ _))
    ((mem_ball_iff_norm.1 hp.2.1).trans_le (min_le_left _ _))
    (fun k =>
      ((hav₀ p.1 (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hp.1)).2 k).1)
    (fun k =>
      ((hav₁ p.2.1 (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hp.2.1)).2
        k).1)).symm

/-- **Joint four-variable holomorphy of the fixed-abscissa separating-contour Mellin–Barnes
integral.** For any fixed `σ < 0`, `hypergeometricMellinBarnes a b c z σ` is jointly analytic in
`(a, b, c, z)` on `{p | (∀ k : ℕ, p.1 ≠ -k) ∧ (∀ k : ℕ, p.2.1 ≠ -k) ∧
(∀ k : ℕ, p.1.re + σ ≠ -k) ∧ (∀ k : ℕ, p.2.1.re + σ ≠ -k) ∧ -p.2.2.2 ∈ slitPlane}`,
across all lower parameters `c : ℂ` and across integer differences `a - b ∈ ℤ`. -/
theorem analyticOnNhd_hypergeometricMellinBarnes {σ : ℝ} (hσ : σ < 0) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ × ℂ × ℂ => hypergeometricMellinBarnes p.1 p.2.1 p.2.2.1 p.2.2.2 σ)
      {p | (∀ k : ℕ, p.1 ≠ -k) ∧ (∀ k : ℕ, p.2.1 ≠ -k) ∧
        (∀ k : ℕ, p.1.re + σ ≠ -k) ∧ (∀ k : ℕ, p.2.1.re + σ ≠ -k) ∧
        -p.2.2.2 ∈ slitPlane} := by
  rintro p₀ ⟨ha₀, hb₀, ha₀_σ, hb₀_σ, hz₀⟩
  simp_rw [hypergeometricMellinBarnes_def]
  exact ((analyticAt_const (v := (2 * π : ℂ)⁻¹)).mul
    (analyticOnNhd_integral_hypergeometricMellinBarnesIntegrand
      (fun m _ => by linarith [m.cast_nonneg (α := ℝ)]) p₀ ⟨ha₀_σ, hb₀_σ, hz₀⟩)).add
    (analyticAt_residueSum_hypergeometricMellinBarnes ha₀ hb₀ ha₀_σ hb₀_σ hz₀)

/-- **Joint four-variable holomorphy of the separating-contour Mellin–Barnes integral.** On
`{p | (∀ k : ℕ, p.1 ≠ -k) ∧ (∀ k : ℕ, p.2.1 ≠ -k) ∧ -p.2.2.2 ∈ slitPlane}`,
`mellinBarnesIntegral a b c z` is jointly analytic in `(a, b, c, z)` across all lower parameters
`c : ℂ` and across integer differences `a - b ∈ ℤ`. -/
theorem analyticOnNhd_mellinBarnesIntegral :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ × ℂ => mellinBarnesIntegral p.1 p.2.1 p.2.2.1 p.2.2.2)
      {p | (∀ k : ℕ, p.1 ≠ -k) ∧ (∀ k : ℕ, p.2.1 ≠ -k) ∧ -p.2.2.2 ∈ slitPlane} := by
  rintro p₀ ⟨ha₀, hb₀, hz₀⟩
  let σ : ℝ := mellinBarnesAbscissa p₀.1 p₀.2.1
  have hσ : σ < 0 := mellinBarnesAbscissa_lt_zero p₀.1 p₀.2.1
  obtain ⟨ha₀_σ, hb₀_σ⟩ := mellinBarnesAbscissa_avoid p₀.1 p₀.2.1
  obtain ⟨δ₀, hδ₀, hav₀⟩ := exists_ball_re_add_ne_neg_natCast_and_lt_iff p₀.1 ha₀_σ
  obtain ⟨δ₁, hδ₁, hav₁⟩ := exists_ball_re_add_ne_neg_natCast_and_lt_iff p₀.2.1 hb₀_σ
  have hU_nhds : (ball p₀.1 δ₀ ×ˢ ball p₀.2.1 δ₁ ×ˢ univ ×ˢ {z : ℂ | -z ∈ slitPlane}) ∈ 𝓝 p₀ :=
    (isOpen_ball.prod (isOpen_ball.prod (isOpen_univ.prod
      (isOpen_slitPlane.preimage continuous_neg)))).mem_nhds
      ⟨mem_ball_self hδ₀, mem_ball_self hδ₁, mem_univ _, hz₀⟩
  refine (analyticOnNhd_hypergeometricMellinBarnes hσ p₀
    ⟨ha₀, hb₀, ha₀_σ, hb₀_σ, hz₀⟩).congr ?_
  filter_upwards [hU_nhds] with p hp
  exact (mellinBarnesIntegral_eq_hypergeometricMellinBarnes p.2.2.1 hσ
    (hav₀ p.1 hp.1).1 (hav₁ p.2.1 hp.2.1).1 hp.2.2.2).symm

/-- `Complex.mellinBarnesIntegral` composed with four analytic functions is analytic wherever
`fa x, fb x ∉ -ℕ` and `-fz x ∈ slitPlane`. -/
theorem _root_.AnalyticAt.mellinBarnesIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {fa fb fc fz : E → ℂ} {x : E}
    (hfa : AnalyticAt ℂ fa x) (hfb : AnalyticAt ℂ fb x) (hfc : AnalyticAt ℂ fc x)
    (hfz : AnalyticAt ℂ fz x) (ha : ∀ k : ℕ, fa x ≠ -k) (hb : ∀ k : ℕ, fb x ≠ -k)
    (hz : -fz x ∈ Complex.slitPlane) :
    AnalyticAt ℂ
      (fun w => Complex.mellinBarnesIntegral (fa w) (fb w) (fc w) (fz w)) x :=
  (Complex.analyticOnNhd_mellinBarnesIntegral (fa x, fb x, fc x, fz x)
    ⟨ha, hb, hz⟩).comp_of_eq (hfa.prod (hfb.prod (hfc.prod hfz))) rfl

end Complex
