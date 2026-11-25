/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.LSeries.HigherPole.PoleBoundary
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Contour.MeromorphicLaurent

/-!
# Compact `L¹` boundary convergence of Delange's regularised remainder

Given `F : ℂ → ℂ` satisfying `TauCeti.HigherPoleTauberian.PoleBoundary F a k A`, write the
model-subtracted remainder and its Delange regularisation as

* `R(s) = F(s) - A / (s - a) ^ (k + 1)`,
* `H(s) = -∫ u in (0 : ℝ)..1, deriv R (s + u) * (u ^ k / k!)`.

When `s = a + ε + i y` with `ε > 0` and `u ∈ (0, 1]`, the evaluation point `s + u` always lies in
the open half-plane `Re w > a`, so `deriv R` only sees the holomorphic restriction of `F` to
`Re w > a`. Removing the leading polar term `(A : ℂ) / (s - a) ^ (k + 1)` lowers the pole order of
`R` at `a` to at most `k`; integrating `deriv R (s + u)` against `u ^ k / k!` converts a residual
polar derivative of size `|s + u - a| ^ (-j - 1)` (`1 ≤ j ≤ k`) into at worst a logarithmic
singularity `O(|log |y||)` as `y → 0`, which is locally integrable on `ℝ`. Away from `y = 0`, the
holomorphic boundary germs of `PoleBoundary` give continuous boundary extensions.

This file proves `regularizedBoundaryL1`: there exists a single boundary function `b : ℝ → ℂ` such
that on every compact interval `[-L, L]` (`0 < L`), `b` is integrable and
`∫ y in Icc (-L) L, ‖H (a + ε + y * I) - b y‖ → 0` as `ε → 0⁺`. No Laplace representation or
positivity hypothesis is used; the result depends purely on `PoleBoundary`. We also record the
vanishing of the regularised integral whenever `F` agrees on `Re s > a` with the model pole, even
when `F` is redefined at the pole so that the raw remainder `R` is discontinuous at `a`.

## Main results

* `TauCeti.HigherPoleTauberian.regularizedBoundaryL1`: compact `L¹` boundary convergence of `H`
  as `ε → 0⁺` from `PoleBoundary F a k A`.
* `TauCeti.HigherPoleTauberian.regularizedRemainder_eq_zero_of_eq_on_re_gt`: if `F` agrees with
  `A / (s - a) ^ (k + 1)` on `Re s > a`, then the regularised integral vanishes at every `s` with
  `a ≤ s.re`.
* `TauCeti.HigherPoleTauberian.not_continuousAt_remainder_update_pole`: updating the model pole at
  `a` to a nonzero value breaks continuity of the raw remainder at `a`.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) 71 (1954),
  213–242 (§3.3.1–3.3.2, pp. 221–224; §4.1, pp. 228–229; §5.2.1, pp. 235–238).
-/

public section

open Complex Filter intervalIntegral MeasureTheory Metric Set
open scoped Topology

namespace TauCeti.HigherPoleTauberian

/-! ### Private analytic and integral helpers -/

/-- The raw (unregularised) model-subtracted remainder `R(s) = F(s) - A / (s - a) ^ (k + 1)`. -/
private noncomputable def poleSubtractedRemainder (F : ℂ → ℂ) (a : ℝ) (k : ℕ) (A : ℝ) (s : ℂ) :
    ℂ :=
  F s - (A : ℂ) / (s - a) ^ (k + 1)

/-- Function-level unfolding of `poleSubtractedRemainder`. -/
private theorem poleSubtractedRemainder_def (F : ℂ → ℂ) (a : ℝ) (k : ℕ) (A : ℝ) :
    poleSubtractedRemainder F a k A = fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1) :=
  (rfl)

/-- Evaluation of `poleSubtractedRemainder`. -/
private theorem poleSubtractedRemainder_apply (F : ℂ → ℂ) (a : ℝ) (k : ℕ) (A : ℝ) (s : ℂ) :
    poleSubtractedRemainder F a k A s = F s - (A : ℂ) / (s - a) ^ (k + 1) :=
  (rfl)

/-- Delange's regularised remainder integral
`H(s) = -∫ u in (0 : ℝ)..1, deriv R (s + u) * (u ^ k / k!)`, where
`R = poleSubtractedRemainder F a k A`. -/
private noncomputable def regularizedRemainder (F : ℂ → ℂ) (a : ℝ) (k : ℕ) (A : ℝ) (s : ℂ) : ℂ :=
  -∫ u : ℝ in (0 : ℝ)..1,
    deriv (poleSubtractedRemainder F a k A) (s + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)

/-- Evaluation of `regularizedRemainder`. -/
private theorem regularizedRemainder_apply (F : ℂ → ℂ) (a : ℝ) (k : ℕ) (A : ℝ) (s : ℂ) :
    regularizedRemainder F a k A s = -∫ u : ℝ in (0 : ℝ)..1,
      deriv (poleSubtractedRemainder F a k A) (s + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ) :=
  (rfl)

/-- On the open right half-plane `Re s > a`, `poleSubtractedRemainder F a k A` is analytic, so its
derivative is also analytic (hence continuous) there. -/
private theorem analyticOnNhd_deriv_remainder {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) :
    AnalyticOnNhd ℂ (deriv (poleSubtractedRemainder F a k A)) {s : ℂ | a < s.re} := by
  rw [poleSubtractedRemainder_def]
  exact (h.sub (poleBoundary_const_div_pow a A k)).interior.deriv

/-- Real part of `((a : ℂ) + ε + y * I) + u - (a + y₀ * I)`. -/
private theorem shift_sub_re (a ε y u y₀ : ℝ) :
    ((((a : ℂ) + ε + y * I) + u) - ((a : ℂ) + y₀ * I)).re = ε + u := by
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero]
  ring

/-- Imaginary part of `((a : ℂ) + ε + y * I) + u - (a + y₀ * I)`. -/
private theorem shift_sub_im (a ε y u y₀ : ℝ) :
    ((((a : ℂ) + ε + y * I) + u) - ((a : ℂ) + y₀ * I)).im = y - y₀ := by
  simp only [sub_im, add_im, ofReal_im, mul_im, I_re, mul_zero, ofReal_re, I_im, mul_one, add_zero,
    zero_add]

/-- Whenever `0 < ε + u`, the shifted boundary point `((a : ℂ) + ε + y * I) + u` lies in the open
right half-plane `{s : ℂ | a < s.re}`. -/
private theorem mem_re_gt_of_add_pos {a ε y u : ℝ} (h : 0 < ε + u) :
    (((a : ℂ) + ε + y * I) + u) ∈ {s : ℂ | a < s.re} := by
  have hre := shift_sub_re a ε y u 0
  simp only [ofReal_zero, zero_mul, add_zero, sub_re, ofReal_re] at hre
  rw [mem_ofPred_eq]
  linarith

/-- Whenever `0 ≤ ε + u` and `ε + u + |y - y₀| ≤ r`, the shifted point `((a : ℂ) + ε + y * I) + u`
lies in `closedBall ((a : ℂ) + y₀ * I) r`. -/
private theorem mem_closedBall_shift {a ε y u y₀ r : ℝ} (h0 : 0 ≤ ε + u)
    (hr : ε + u + |y - y₀| ≤ r) :
    (((a : ℂ) + ε + y * I) + u) ∈ closedBall ((a : ℂ) + y₀ * I) r := by
  rw [mem_closedBall, dist_eq_norm]
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  rw [shift_sub_re, shift_sub_im, abs_of_nonneg h0]
  exact hr

/-- Pointwise bound on `‖z * (u ^ k / k!)‖` for `u ∈ [0, 1]` when `‖z‖ ≤ B` (`0 ≤ B`). -/
private theorem norm_mul_pow_div_factorial_le {z : ℂ} {B u : ℝ} {k : ℕ} (hz : ‖z‖ ≤ B)
    (hB : 0 ≤ B) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖z * (((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤ B := by
  have hfac : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hwt : ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (pow_nonneg hu0 k) (by positivity))]
    exact div_le_one_of_le₀ ((pow_le_one₀ hu0 hu1).trans hfac) (by positivity)
  rw [norm_mul]
  simpa using mul_le_mul hz hwt (norm_nonneg _) hB

/-- Interval integral norm bound on `[c, 1]` (`0 ≤ c ≤ 1`) against the weight `u ^ k / k!`. -/
private theorem norm_intervalIntegral_mul_weight_le {f : ℝ → ℂ} {c B : ℝ} {k : ℕ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hB : 0 ≤ B) (hf : ∀ u ∈ Ioc c 1, ‖f u‖ ≤ B) :
    ‖∫ u : ℝ in c..1, f u * (((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤ B :=
  (norm_integral_le_of_norm_le_const fun u hu ↦ by
    rw [uIoc_of_le hc1] at hu
    exact norm_mul_pow_div_factorial_le (hf u hu) hB (hc0.trans hu.1.le) hu.2).trans
    (mul_le_of_le_one_right hB (by rw [abs_of_nonneg (by linarith)]; linarith))

/-- For every fixed `ε > 0`, `y ↦ regularizedRemainder F a k A (a + ε + y * I)` is continuous on
`ℝ`. -/
private theorem continuous_regularized_of_pos {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun y : ℝ ↦ regularizedRemainder F a k A ((a : ℂ) + ε + y * I) := by
  -- Clamp `u` to `max u 0` inside a globally continuous integrand that agrees on `[0, 1]`.
  have hR_cont : ContinuousOn (deriv (poleSubtractedRemainder F a k A)) {s : ℂ | a < s.re} :=
    (analyticOnNhd_deriv_remainder h).continuousOn
  let φ : ℝ × ℝ → ℂ := fun p ↦ ((a : ℂ) + ε + p.fst * I) + (max p.snd 0 : ℝ)
  have hφ_cont : Continuous φ := by fun_prop
  have hφ_mem : ∀ p : ℝ × ℝ, φ p ∈ {s : ℂ | a < s.re} := fun p ↦
    mem_re_gt_of_add_pos (add_pos_of_pos_of_nonneg hε (le_max_right _ _))
  have h_uncurry : Continuous fun p : ℝ × ℝ ↦
      deriv (poleSubtractedRemainder F a k A) (φ p) *
        (((p.snd ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) :=
    (hR_cont.comp_continuous hφ_cont hφ_mem).mul (by fun_prop)
  have h_param : Continuous fun y : ℝ ↦
      -∫ u : ℝ in (0 : ℝ)..1,
        deriv (poleSubtractedRemainder F a k A) (φ (y, u)) *
          (((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) :=
    (continuous_parametric_intervalIntegral_of_continuous' h_uncurry 0 1).neg
  refine h_param.congr fun y ↦ ?_
  rw [regularizedRemainder_apply]
  refine congrArg Neg.neg (integral_congr fun u hu ↦ ?_)
  rw [uIcc_of_le zero_le_one] at hu
  simp [φ, max_eq_left hu.1]

/-- Compactness bound on `‖deriv R (((a : ℂ) + ε + y * I) + u)‖` when `u ∈ [δ, 1]`, `ε ∈ [0, ε₁]`,
and `y ∈ [-L, L]` (`0 < δ`). -/
private theorem exists_tail_bound {R : ℂ → ℂ} {a : ℝ}
    (hR_cont : ContinuousOn (deriv R) {s : ℂ | a < s.re})
    {δ ε₁ L : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε ∈ Icc (0 : ℝ) ε₁, ∀ y ∈ Icc (-L) L, ∀ u ∈ Icc δ 1,
      ‖deriv R (((a : ℂ) + ε + y * I) + u)‖ ≤ B := by
  let S : Set (ℝ × ℝ × ℝ) := Icc 0 ε₁ ×ˢ (Icc (-L) L ×ˢ Icc δ 1)
  let ψ : ℝ × ℝ × ℝ → ℂ := fun p ↦ ((a : ℂ) + p.fst + p.snd.fst * I) + p.snd.snd
  have hS_comp : IsCompact (ψ '' S) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image (by fun_prop)
  have hS_sub : ψ '' S ⊆ {s : ℂ | a < s.re} := by
    rintro _ ⟨⟨ε, y, u⟩, ⟨hε, -, hu⟩, rfl⟩
    exact mem_re_gt_of_add_pos (by linarith [hε.1, hu.1])
  obtain ⟨B, hB⟩ := hS_comp.exists_bound_of_continuousOn (hR_cont.mono hS_sub)
  exact ⟨max B 0, le_max_right _ _, fun ε hε y hy u hu ↦
    (hB (ψ (ε, y, u)) ⟨(ε, y, u), ⟨hε, hy, hu⟩, rfl⟩).trans (le_max_left _ _)⟩

/-- Local analytic continuation of `poleSubtractedRemainder F a k A` around an off-pole boundary
point `a + y₀ * I` (`y₀ ≠ 0`) yields a radius `ρ > 0` and a uniform bound `B ≥ 0` on
`‖deriv (poleSubtractedRemainder F a k A) (((a : ℂ) + ε + y * I) + u)‖` for all `ε ∈ [0, ρ]`,
`y ∈ ball y₀ ρ`, and `u ∈ (0, 1]`. -/
private theorem exists_away_local_bound {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) {y₀ : ℝ} (hy₀ : y₀ ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ ε ∈ Icc (0 : ℝ) ρ, ∀ y ∈ ball y₀ ρ, ∀ u ∈ Ioc (0 : ℝ) 1,
        ‖deriv (poleSubtractedRemainder F a k A) (((a : ℂ) + ε + y * I) + u)‖ ≤ B := by
  obtain ⟨r, hr, R₀, hR₀_an, hR_eq⟩ := (h.sub (poleBoundary_const_div_pow a A k)).away y₀ hy₀
  let z₀ : ℂ := (a : ℂ) + y₀ * I
  have hderiv_eq : ∀ s ∈ ball z₀ r, a < s.re →
      deriv (poleSubtractedRemainder F a k A) s = deriv R₀ s := by
    intro s hs hsre
    have hopen : IsOpen (ball z₀ r ∩ {w : ℂ | a < w.re}) := isOpen_ball.inter (isOpen_re_gt a)
    exact (eventuallyEq_of_mem (hopen.mem_nhds ⟨hs, hsre⟩) fun w ⟨hw, hwre⟩ ↦ by
      rw [poleSubtractedRemainder_apply]
      exact hR_eq w hw hwre).deriv_eq
  let ρ : ℝ := min 1 (r / 6)
  have hρ : 0 < ρ := lt_min zero_lt_one (by positivity)
  obtain ⟨B₁, hB₁⟩ := (isCompact_closedBall z₀ (r / 2)).exists_bound_of_continuousOn
    (hR₀_an.deriv.continuousOn.mono (closedBall_subset_ball (half_lt_self hr)))
  obtain ⟨B₂, -, hB₂⟩ := exists_tail_bound (ε₁ := ρ) (L := |y₀| + ρ)
    (analyticOnNhd_deriv_remainder h).continuousOn hρ
  let B : ℝ := max (max B₁ 0) B₂
  refine ⟨ρ, hρ, B, le_trans (le_max_right _ _) (le_max_left _ _), fun ε hε y hy u ⟨hu0, hu1⟩ ↦ ?_⟩
  have hy' : |y - y₀| < ρ := by simpa [Real.dist_eq] using mem_ball.mp hy
  by_cases huρ : u ≤ ρ
  · have hρ_le : ρ ≤ r / 6 := min_le_right _ _
    have hdist : (((a : ℂ) + ε + y * I) + u) ∈ closedBall z₀ (r / 2) :=
      mem_closedBall_shift (add_nonneg hε.1 hu0.le) (by linarith [hε.2])
    rw [hderiv_eq _ (closedBall_subset_ball (half_lt_self hr) hdist)
      (mem_re_gt_of_add_pos (by linarith [hε.1]))]
    exact (hB₁ _ hdist).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have habs := abs_le.mp hy'.le
    have hy_Icc : y ∈ Icc (-(|y₀| + ρ)) (|y₀| + ρ) :=
      ⟨by linarith [neg_abs_le y₀], by linarith [le_abs_self y₀]⟩
    exact (hB₂ ε hε y hy_Icc u ⟨(lt_of_not_ge huρ).le, hu1⟩).trans (le_max_right _ _)

/-- Right-continuity of `regularizedRemainder F a k A (a + ε + y₀ * I)` as `ε → 0⁺` at any off-pole
point `y₀ ≠ 0`. -/
private theorem tendsto_regularized_of_ne_zero {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) {y₀ : ℝ} (hy₀ : y₀ ≠ 0) :
    Tendsto (fun ε : ℝ ↦ regularizedRemainder F a k A ((a : ℂ) + ε + y₀ * I))
      (𝓝[>] 0)
      (𝓝 (regularizedRemainder F a k A ((a : ℂ) + y₀ * I))) := by
  obtain ⟨ρ, hρ, B, hB0, hbound⟩ := exists_away_local_bound h hy₀
  have hR_cont : ContinuousOn (deriv (poleSubtractedRemainder F a k A)) {s : ℂ | a < s.re} :=
    (analyticOnNhd_deriv_remainder h).continuousOn
  have h_cwa : ContinuousWithinAt
      (fun ε : ℝ ↦ ∫ u : ℝ in (0 : ℝ)..1,
        deriv (poleSubtractedRemainder F a k A) (((a : ℂ) + ε + y₀ * I) + u) *
          ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))
      (Ici 0) 0 := by
    refine continuousWithinAt_of_dominated_interval (bound := fun _ ↦ B) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [Icc_mem_nhdsGE hρ] with ε hε
      rw [uIoc_of_le zero_le_one]
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact (hR_cont.comp (by fun_prop) fun u hu ↦
        mem_re_gt_of_add_pos (by linarith [hε.1, hu.1])).mul (by fun_prop)
    · filter_upwards [Icc_mem_nhdsGE hρ] with ε hε
      refine .of_forall fun u hu ↦ ?_
      rw [uIoc_of_le zero_le_one] at hu
      exact norm_mul_pow_div_factorial_le (hbound ε hε y₀ (mem_ball_self hρ) u hu) hB0
        hu.1.le hu.2
    · refine .of_forall fun u hu ↦ ?_
      rw [uIoc_of_le zero_le_one] at hu
      have hmem : (((a : ℂ) + (0 : ℝ) + y₀ * I) + u) ∈ {s : ℂ | a < s.re} := by simp [hu.1]
      have hinner : ContinuousAt (fun ε : ℝ ↦ (((a : ℂ) + ε + y₀ * I) + u)) 0 := by fun_prop
      exact ((((analyticOnNhd_deriv_remainder h _ hmem).continuousAt).comp_of_eq
        hinner rfl).mul continuousAt_const).continuousWithinAt
  have h_neg : ContinuousWithinAt
      (fun ε : ℝ ↦ regularizedRemainder F a k A ((a : ℂ) + ε + y₀ * I)) (Ici 0) 0 := by
    simp_rw [regularizedRemainder_apply]
    exact h_cwa.neg
  simpa only [ofReal_zero, add_zero] using
    h_neg.tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)

/-- Finite-subcover uniform bound on `‖regularizedRemainder F a k A (a + ε + y * I)‖` across the
compact off-pole set `{y ∈ [-L, L] | δ ≤ |y|}` (`0 < δ`). -/
private theorem exists_away_compact_bound {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) {δ L : ℝ} (hδ : 0 < δ) :
    ∃ ε_away : ℝ, 0 < ε_away ∧ ∃ B_away : ℝ, 0 ≤ B_away ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε_away, ∀ y ∈ Icc (-L) L, δ ≤ |y| →
        ‖regularizedRemainder F a k A ((a : ℂ) + ε + y * I)‖ ≤ B_away := by
  let K : Set ℝ := {y ∈ Icc (-L) L | δ ≤ |y|}
  have hK_comp : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hK_loc : ∀ y₀ : K, ∃ ρ : ℝ, 0 < ρ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ ε ∈ Icc (0 : ℝ) ρ, ∀ y ∈ ball (y₀ : ℝ) ρ, ∀ u ∈ Ioc (0 : ℝ) 1,
        ‖deriv (poleSubtractedRemainder F a k A) (((a : ℂ) + ε + y * I) + u)‖ ≤ B :=
    fun ⟨_, _, hy₀δ⟩ ↦ exists_away_local_bound h (abs_pos.mp (hδ.trans_le hy₀δ))
  choose ρ hρ B hB0 hB using hK_loc
  obtain ⟨t, ht_cov⟩ := hK_comp.elim_finite_subcover (fun y₀ : K ↦ ball (y₀ : ℝ) (ρ y₀))
    (fun _ ↦ isOpen_ball) fun y hy ↦ mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hρ ⟨y, hy⟩)⟩
  obtain ⟨ε_away, hε_away, hε_le⟩ : ∃ ε_away : ℝ, 0 < ε_away ∧ ∀ y₀ ∈ t, ε_away ≤ ρ y₀ := by
    rcases t.eq_empty_or_nonempty with rfl | ht
    · exact ⟨1, zero_lt_one, by simp⟩
    · obtain ⟨y₁, _, hy₁⟩ := t.exists_min_image ρ ht
      exact ⟨ρ y₁, hρ y₁, hy₁⟩
  refine ⟨ε_away, hε_away, ∑ y₀ ∈ t, B y₀, Finset.sum_nonneg (fun y₀ _ ↦ hB0 y₀),
    fun ε hε y hyL hyδ ↦ ?_⟩
  rcases mem_iUnion₂.mp (ht_cov ⟨hyL, hyδ⟩) with ⟨y₀, hy₀t, hy_ball⟩
  have hε_Icc : ε ∈ Icc (0 : ℝ) (ρ y₀) := ⟨hε.1.le, hε.2.le.trans (hε_le y₀ hy₀t)⟩
  rw [regularizedRemainder_apply, norm_neg]
  exact (norm_intervalIntegral_mul_weight_le le_rfl zero_le_one (hB0 y₀)
    (hB y₀ ε hε_Icc y hy_ball)).trans (Finset.single_le_sum (f := B) (fun z _ ↦ hB0 z) hy₀t)

/-- Laurent decomposition of `poleSubtractedRemainder F a k A` on a right half-disc near `a`: the
polar order is at most `k`, and its derivative decomposes into an analytic derivative plus at most
`k` polar derivative terms. -/
private theorem exists_near_pole_deriv_laurent {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∃ m : ℕ, m ≤ k ∧ ∃ (c : Fin m → ℂ) (q : ℂ → ℂ),
      AnalyticOnNhd ℂ q (ball (a : ℂ) r₁) ∧
      ∀ z ∈ ball (a : ℂ) r₁, a < z.re →
        deriv (poleSubtractedRemainder F a k A) z = deriv q z +
          ∑ i : Fin m, c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2)) := by
  obtain ⟨r₀, hr₀, g, hg, hga, hF⟩ := h.pole
  let f : ℂ → ℂ := fun z ↦ g z - (A : ℂ)
  let Q : ℂ → ℂ := fun z ↦ f z / (z - a) ^ (k + 1)
  have hf_an : AnalyticAt ℂ f a := (hg a (mem_ball_self hr₀)).sub analyticAt_const
  have hd_an : AnalyticAt ℂ (fun z : ℂ ↦ (z - a) ^ (k + 1)) a :=
    (analyticAt_id.sub analyticAt_const).pow (k + 1)
  have hQ : MeromorphicAt Q a := hf_an.meromorphicAt.fun_div hd_an.meromorphicAt
  have hord : TauCeti.Contour.meromorphicPolarOrderAt Q a ≤ k :=
    TauCeti.Contour.meromorphicPolarOrderAt_div_sub_pow_le_of_tendsto_zero hf_an.meromorphicAt
      (by simpa [f, hga] using hf_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  obtain ⟨r_q, hr_q, hq_ball⟩ :=
    (TauCeti.Contour.meromorphicAnalyticPartAt_analyticAt hQ).exists_ball_analyticOnNhd
  obtain ⟨r_e, hr_e, hlaur_ball⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp
      (TauCeti.Contour.eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt hQ))
  let r₁ : ℝ := min r₀ (min r_q r_e)
  have hsub₀ : ball (a : ℂ) r₁ ⊆ ball (a : ℂ) r₀ := ball_subset_ball (min_le_left _ _)
  have hsub_q : ball (a : ℂ) r₁ ⊆ ball (a : ℂ) r_q :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hsub_e : ball (a : ℂ) r₁ ⊆ ball (a : ℂ) r_e :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r₁, lt_min hr₀ (lt_min hr_q hr_e), _, hord,
    TauCeti.Contour.meromorphicPolarCoeffAt hQ, TauCeti.Contour.meromorphicAnalyticPartAt hQ,
    hq_ball.mono hsub_q, fun z hz hzre ↦ ?_⟩
  have hopen : IsOpen (ball (a : ℂ) r₁ ∩ {w : ℂ | a < w.re}) :=
    isOpen_ball.inter (isOpen_re_gt a)
  have hev : poleSubtractedRemainder F a k A =ᶠ[𝓝 z]
      fun w ↦ TauCeti.Contour.meromorphicAnalyticPartAt hQ w +
        TauCeti.Contour.meromorphicPolarPartAt hQ w := by
    refine eventuallyEq_of_mem (hopen.mem_nhds ⟨hz, hzre⟩) fun w ⟨hw, hwre⟩ ↦ ?_
    have hwa : w ≠ a := fun h0 ↦ by simp [h0] at hwre
    have hRw : poleSubtractedRemainder F a k A w = Q w := by
      simp only [poleSubtractedRemainder_apply, Q, f, hF w (hsub₀ hw) hwre, sub_div]
    exact hRw.trans (hlaur_ball w (hsub_e hw) hwa)
  rw [hev.deriv_eq]
  have hza : z ≠ a := fun h0 ↦ by simp [h0] at hzre
  exact (((hq_ball _ (hsub_q hz)).differentiableAt.hasDerivAt).add
    (TauCeti.Contour.hasDerivAt_meromorphicPolarPartAt hQ hza)).deriv

/-- Pointwise bound on a single weighted polar derivative term for `j + 1 ≤ k` and `u ∈ (0, 1]`. -/
private theorem norm_laurent_term_mul_weight_le {j k : ℕ} (hj : j + 1 ≤ k) {c w : ℂ} {u y : ℝ}
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hw : (u + |y|) / 2 ≤ ‖w‖) :
    ‖c * (-((j + 1 : ℕ) : ℂ) / w ^ (j + 2))‖ * ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤
      ‖c‖ * ((j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (j + 2) * (u + |y|)⁻¹ := by
  have hnorm_w : ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤ u ^ k := by
    have hfac : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact div_le_self (pow_nonneg hu0.le k) hfac
  have hu_pow : u ^ k ≤ (u + |y|) ^ (j + 1) :=
    (pow_le_pow_of_le_one hu0.le hu1 hj).trans
      (pow_le_pow_left₀ hu0.le (le_add_of_nonneg_right (abs_nonneg y)) _)
  have ht_pos : 0 < u + |y| := by linarith [abs_nonneg y]
  have hpow_ge : ((u + |y|) / 2) ^ (j + 2) ≤ ‖w‖ ^ (j + 2) :=
    pow_le_pow_left₀ (by positivity) hw _
  simp only [norm_mul, norm_div, norm_neg, Complex.norm_natCast, norm_pow]
  calc
    ‖c‖ * (((j + 1 : ℕ) : ℝ) / ‖w‖ ^ (j + 2)) * ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖
        ≤ ‖c‖ * (((j + 1 : ℕ) : ℝ) / ((u + |y|) / 2) ^ (j + 2)) * (u + |y|) ^ (j + 1) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow_ge) (norm_nonneg _))
        (hnorm_w.trans hu_pow) (norm_nonneg _) (by positivity)
    _ = ‖c‖ * ((j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (j + 2) * (u + |y|)⁻¹ := by
      rw [div_pow, div_div_eq_mul_div, pow_succ (u + |y|) (j + 1)]
      have ht_ne : u + |y| ≠ 0 := ht_pos.ne'
      field_simp

/-- Pointwise bound on the weighted Laurent derivative near `a` for `u ∈ (0, 1]`. -/
private theorem norm_laurent_integrand_le {m k : ℕ} (hm_le : m ≤ k) {c : Fin m → ℂ}
    {wq : ℂ} {M₀ a ε u y : ℝ} (hwq : ‖wq‖ ≤ M₀) (hM₀ : 0 ≤ M₀)
    (hε0 : 0 ≤ ε) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    let z : ℂ := ((a : ℂ) + ε + y * I) + u
    ‖(wq + ∑ i : Fin m, c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2))) *
      (((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤
      M₀ + (∑ i : Fin m, ‖c i‖ * ((i.val + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (i.val + 2)) * (u + |y|)⁻¹ := by
  intro z
  have hza : z - a = (((a : ℂ) + ε + y * I) + u) - ((a : ℂ) + (0 : ℝ) * I) := by
    simp only [z, ofReal_zero, zero_mul, add_zero]
  have hre : (z - a).re = ε + u := by rw [hza, shift_sub_re]
  have him : (z - a).im = y := by rw [hza, shift_sub_im, sub_zero]
  have hza_ge : (u + |y|) / 2 ≤ ‖z - a‖ := by
    linarith [hre ▸ re_le_norm (z - a), him ▸ abs_im_le_norm (z - a)]
  calc
    ‖(wq + ∑ i : Fin m, c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2))) *
        (((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖
        ≤ ‖wq * (((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ +
          ∑ i : Fin m, ‖c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2))‖ *
            ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ := by
      rw [add_mul]
      refine (norm_add_le _ _).trans ?_
      gcongr
      rw [Finset.sum_mul]
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ M₀ + (∑ i : Fin m, ‖c i‖ * ((i.val + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (i.val + 2)) *
        (u + |y|)⁻¹ := by
      refine add_le_add (norm_mul_pow_div_factorial_le hwq hM₀ hu0.le hu1) ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ ↦
        norm_laurent_term_mul_weight_le (Nat.succ_le_of_lt (i.isLt.trans_le hm_le)) hu0 hu1 hza_ge

/-- Logarithmic upper bound on the near-pole head integral
`∫ u in 0..δ, deriv R (((a : ℂ) + ε + y * I) + u) * (u ^ k / k!)` from the Laurent decomposition
of `deriv R` on the half-disc `ball a r₁ ∩ {z | a < z.re}`. -/
private theorem norm_integral_near_pole_head_le {R q : ℂ → ℂ} {m k : ℕ} (hm_le : m ≤ k)
    {c : Fin m → ℂ} {a r₁ M_q δ ε y : ℝ} (hr₁ : 0 < r₁)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδr : δ ≤ r₁ / 6) (hM_q : 0 ≤ M_q)
    (hε : ε ∈ Ioo (0 : ℝ) δ) (hy0 : y ≠ 0) (hyδ : |y| ≤ δ)
    (hMq : ∀ z ∈ closedBall (a : ℂ) (r₁ / 2), ‖deriv q z‖ ≤ M_q)
    (hderiv_laur : ∀ z ∈ ball (a : ℂ) r₁, a < z.re →
      deriv R z = deriv q z +
        ∑ i : Fin m, c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2))) :
    ‖∫ u : ℝ in (0 : ℝ)..δ,
      deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)‖ ≤
      M_q + (∑ i : Fin m, ‖c i‖ * ((i.val + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (i.val + 2)) *
        (Real.log 2 + |Real.log y|) := by
  let C_pole : ℝ := ∑ i : Fin m, ‖c i‖ * ((i.val + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (i.val + 2)
  have : 0 ≤ C_pole := Finset.sum_nonneg fun i _ ↦ by positivity
  have hy_pos : 0 < |y| := abs_pos.mpr hy0
  have hinv_int : IntervalIntegrable (fun u : ℝ ↦ (u + |y|)⁻¹) volume 0 δ :=
    intervalIntegral.intervalIntegrable_inv
      (fun u hu ↦ by rw [uIcc_of_le hδ.le] at hu; linarith [hu.1])
      (continuousOn_id.add continuousOn_const)
  have hmaj_int : IntervalIntegrable (fun u : ℝ ↦ M_q + C_pole * (u + |y|)⁻¹) volume 0 δ :=
    intervalIntegrable_const.add (hinv_int.const_mul C_pole)
  have hhead_le : ‖∫ u : ℝ in (0 : ℝ)..δ,
      deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)‖ ≤
      ∫ u : ℝ in (0 : ℝ)..δ, (M_q + C_pole * (u + |y|)⁻¹) :=
    norm_integral_le_of_norm_le hδ.le (.of_forall fun u ⟨hu0, huδ⟩ ↦ by
      set z : ℂ := ((a : ℂ) + ε + y * I) + u
      have hz_cb : z ∈ closedBall (a : ℂ) (r₁ / 2) := by
        have hr_le : ε + u + |y - 0| ≤ r₁ / 2 := by rw [sub_zero]; linarith [hε.2]
        simpa only [ofReal_zero, zero_mul, add_zero] using
          mem_closedBall_shift (a := a) (add_nonneg hε.1.le hu0.le) hr_le
      rw [hderiv_laur z (closedBall_subset_ball (half_lt_self hr₁) hz_cb)
        (mem_re_gt_of_add_pos (by linarith [hε.1]))]
      exact norm_laurent_integrand_le hm_le (hMq z hz_cb) hM_q hε.1.le hu0 (huδ.trans hδ1))
      hmaj_int
  have heval : ∫ u : ℝ in (0 : ℝ)..δ, (M_q + C_pole * (u + |y|)⁻¹) =
      M_q * δ + C_pole * Real.log ((δ + |y|) / |y|) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hinv_int.const_mul C_pole),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_comp_add_right (fun x : ℝ ↦ x⁻¹), zero_add,
      integral_inv_of_pos hy_pos (by positivity), smul_eq_mul]
    ring
  have hlog_le : Real.log ((δ + |y|) / |y|) ≤ Real.log 2 + |Real.log y| := by
    have h1 : Real.log ((δ + |y|) / |y|) ≤ Real.log (2 / |y|) :=
      Real.log_le_log (div_pos (by positivity) hy_pos)
        (div_le_div_of_nonneg_right (by linarith) hy_pos.le)
    rw [Real.log_div two_ne_zero hy_pos.ne', Real.log_abs] at h1
    linarith [neg_abs_le (Real.log y)]
  calc
    ‖∫ u : ℝ in (0 : ℝ)..δ,
        deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)‖
        ≤ M_q * δ + C_pole * Real.log ((δ + |y|) / |y|) := heval ▸ hhead_le
    _ ≤ M_q * 1 + C_pole * (Real.log 2 + |Real.log y|) := by gcongr
    _ = M_q + C_pole * (Real.log 2 + |Real.log y|) := by ring

/-- Logarithmic bound near the pole: there exist `δ > 0` and constants `C₁, C₂ ≥ 0` such that
for all `ε ∈ (0, δ)` and all `y` with `0 < |y| ≤ δ`,
`‖regularizedRemainder F a k A (a + ε + y * I)‖ ≤ C₁ + C₂ * |Real.log y|`. -/
private theorem exists_near_pole_log_bound {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ ε ∈ Ioo (0 : ℝ) δ, ∀ y : ℝ, y ≠ 0 → |y| ≤ δ →
        ‖regularizedRemainder F a k A ((a : ℂ) + ε + y * I)‖ ≤ C₁ + C₂ * |Real.log y| := by
  obtain ⟨r₁, hr₁, m, hm_le, c, q, hq_ball, hderiv_laur⟩ := exists_near_pole_deriv_laurent h
  let δ : ℝ := min 1 (r₁ / 6)
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  obtain ⟨M_q, hMq⟩ := (isCompact_closedBall (a : ℂ) (r₁ / 2)).exists_bound_of_continuousOn
    (hq_ball.deriv.continuousOn.mono (closedBall_subset_ball (half_lt_self hr₁)))
  have hR_cont : ContinuousOn (deriv (poleSubtractedRemainder F a k A)) {s : ℂ | a < s.re} :=
    (analyticOnNhd_deriv_remainder h).continuousOn
  obtain ⟨B_tail, hBt0, hBt⟩ := exists_tail_bound (ε₁ := δ) (L := δ) hR_cont hδ
  let C_pole : ℝ := ∑ i : Fin m, ‖c i‖ * ((i.val + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (i.val + 2)
  have hCp0 : 0 ≤ C_pole := Finset.sum_nonneg fun i _ ↦ by positivity
  let C₁ : ℝ := max M_q 0 + B_tail + C_pole * Real.log 2
  refine ⟨δ, hδ, C₁, C_pole, by have := Real.log_nonneg one_le_two; positivity, hCp0,
    fun ε hε y hy0 hyδ ↦ ?_⟩
  -- Split `[0, 1]` at `δ` into the Laurent-controlled head `[0, δ]` and compact tail `[δ, 1]`.
  let φ : ℝ → ℂ := fun u ↦
    deriv (poleSubtractedRemainder F a k A) (((a : ℂ) + ε + y * I) + u) *
      ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
  have hφ_cont : ContinuousOn φ (Icc 0 1) :=
    (hR_cont.comp (by fun_prop) fun u hu ↦ mem_re_gt_of_add_pos (by linarith [hε.1, hu.1])).mul
      (by fun_prop)
  rw [regularizedRemainder_apply, norm_neg, ← integral_add_adjacent_intervals
    ((hφ_cont.mono (Icc_subset_Icc_right hδ1)).intervalIntegrable_of_Icc hδ.le)
    ((hφ_cont.mono (Icc_subset_Icc_left hδ.le)).intervalIntegrable_of_Icc hδ1)]
  have htail_le : ‖∫ u : ℝ in δ..1, φ u‖ ≤ B_tail :=
    norm_intervalIntegral_mul_weight_le hδ.le hδ1 hBt0 fun u hu ↦
      hBt ε ⟨hε.1.le, hε.2.le⟩ y (abs_le.mp hyδ) u ⟨hu.1.le, hu.2⟩
  have hhead_le := norm_integral_near_pole_head_le hm_le hr₁ hδ hδ1 (min_le_right _ _)
    (le_max_right M_q 0) hε hy0 hyδ (fun z hz ↦ (hMq z hz).trans (le_max_left _ _)) hderiv_laur
  refine (norm_add_le _ _).trans ((add_le_add hhead_le htail_le).trans_eq ?_)
  simp only [C₁, C_pole]
  ring

/-- Uniform integrable majorant on `Icc (-L) L` (`0 < L`) combining the near-pole logarithmic
bound and the compact off-pole bound. -/
private theorem exists_compact_majorant {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) {L : ℝ} (hL : 0 < L) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ M : ℝ → ℝ, IntegrableOn M (Icc (-L) L) ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ y ∈ Icc (-L) L, y ≠ 0 →
        ‖regularizedRemainder F a k A ((a : ℂ) + ε + y * I)‖ ≤ M y := by
  obtain ⟨δ, hδ, C₁, C₂, hC₁0, hC₂0, hnear⟩ := exists_near_pole_log_bound h
  obtain ⟨ε_away, hε_away, B_away, hBa0, haway⟩ := exists_away_compact_bound h (L := L) hδ
  let M : ℝ → ℝ := fun y ↦ (C₁ + B_away) + C₂ * |Real.log y|
  have hM_int : IntegrableOn M (Icc (-L) L) := by
    have hlog_int : IntegrableOn (fun y : ℝ ↦ |Real.log y|) (Icc (-L) L) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
        intervalIntegrable_log'.abs
    exact (integrableOn_const (hs := measure_Icc_lt_top.ne)).add (hlog_int.const_mul C₂)
  refine ⟨min δ ε_away, lt_min hδ hε_away, M, hM_int, fun ε hε y hyL hy0 ↦ ?_⟩
  dsimp only [M]
  by_cases hyδ : |y| ≤ δ
  · linarith [hnear ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ y hy0 hyδ]
  · have hlog_nn : 0 ≤ C₂ * |Real.log y| := mul_nonneg hC₂0 (abs_nonneg _)
    linarith [haway ε ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩ y hyL (lt_of_not_ge hyδ).le]

/-! ### Main theorems -/

/-- **Locally integrable boundary values of Delange's regularised remainder.**
With `R(s) = F(s) - A / (s - a) ^ (k + 1)` and `H(s) = -∫₀¹ R'(s + u) u ^ k / k! du`, there exists
a boundary function `b : ℝ → ℂ` such that on every compact interval `[-L, L]` (`0 < L`), `b` is
integrable and `y ↦ H(a + ε + i y)` converges to `b` in `L¹([-L, L])` as `ε → 0⁺`. -/
theorem regularizedBoundaryL1 {F : ℂ → ℂ} {a A : ℝ} {k : ℕ} (h : PoleBoundary F a k A) :
    let R := fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1)
    let H := fun s : ℂ ↦ -∫ u : ℝ in (0 : ℝ)..1,
      deriv R (s + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
    ∃ b : ℝ → ℂ, ∀ L : ℝ, 0 < L →
      IntegrableOn b (Icc (-L) L) ∧
      Tendsto (fun ε : ℝ ↦ ∫ y in Icc (-L) L, ‖H ((a : ℂ) + ε + y * Complex.I) - b y‖)
        (𝓝[>] 0) (𝓝 0) := by
  intro R H
  have hH : H = regularizedRemainder F a k A := by
    ext s
    rw [regularizedRemainder_apply, poleSubtractedRemainder_def]
  rw [hH]
  let b : ℝ → ℂ := fun y ↦
    if y = 0 then 0 else regularizedRemainder F a k A ((a : ℂ) + y * I)
  have h_ptwise : ∀ y : ℝ, y ≠ 0 →
      Tendsto (fun ε : ℝ ↦ regularizedRemainder F a k A ((a : ℂ) + ε + y * I))
        (𝓝[>] 0) (𝓝 (b y)) := fun y hy ↦ by
    simpa [b, hy] using tendsto_regularized_of_ne_zero h hy
  refine ⟨b, fun L hL ↦ ?_⟩
  -- Dominated convergence on `[-L, L]` using the uniform `O(|log |y||)` majorant `M`.
  obtain ⟨ε₀, hε₀, M, hM_int, hH_le⟩ := exists_compact_majorant h hL
  have hae_ne : ∀ᵐ y ∂volume.restrict (Icc (-L) L), y ∈ Icc (-L) L ∧ y ≠ 0 :=
    (ae_restrict_mem measurableSet_Icc).and (ae_restrict_of_ae (by simp [ae_iff]))
  have hb_meas : AEStronglyMeasurable b (volume.restrict (Icc (-L) L)) := by
    let ε_seq : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
    have hseq_pos : ∀ n : ℕ, 0 < ε_seq n := fun _ ↦ by positivity
    have hseq_tend : Tendsto ε_seq atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        tendsto_one_div_add_atTop_nhds_zero_nat (.of_forall hseq_pos)
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) (y : ℝ) ↦ regularizedRemainder F a k A ((a : ℂ) + ε_seq n + y * I))
      (fun n ↦ (continuous_regularized_of_pos h (hseq_pos n)).aestronglyMeasurable)
      ?_
    filter_upwards [hae_ne] with y hy using (h_ptwise y hy.2).comp hseq_tend
  have hb_le : ∀ᵐ y ∂volume.restrict (Icc (-L) L), ‖b y‖ ≤ M y := by
    filter_upwards [hae_ne] with y hy
    refine le_of_tendsto (h_ptwise y hy.2).norm ?_
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε using hH_le ε hε y hy.1 hy.2
  have hb_int : IntegrableOn b (Icc (-L) L) := hM_int.mono' hb_meas hb_le
  refine ⟨hb_int, ?_⟩
  simpa only [MeasureTheory.integral_zero] using
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Icc (-L) L)) (l := 𝓝[>] (0 : ℝ))
      (f := fun _ ↦ (0 : ℝ)) (fun y ↦ M y + ‖b y‖)
      (by filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
          exact ((continuous_regularized_of_pos h hε.1).aestronglyMeasurable.sub
            hb_int.aestronglyMeasurable).norm)
      (by filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
          filter_upwards [hae_ne] with y hy
          rw [Real.norm_of_nonneg (norm_nonneg _)]
          exact (norm_sub_le _ _).trans (by gcongr; exact hH_le ε hε y hy.1 hy.2))
      (hM_int.add hb_int.norm)
      (by filter_upwards [hae_ne] with y hy
          simpa using ((h_ptwise y hy.2).sub_const (b y)).norm)

/-- If `F` agrees on the open right half-plane `Re s > a` with the model pole
`s ↦ A / (s - a) ^ (k + 1)`, then its regularised remainder integral vanishes at every `s` with
`a ≤ s.re` (including on the boundary line `Re s = a`). -/
theorem regularizedRemainder_eq_zero_of_eq_on_re_gt {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (hF : ∀ s : ℂ, a < s.re → F s = (A : ℂ) / (s - a) ^ (k + 1)) {s : ℂ} (hs : a ≤ s.re) :
    -∫ u : ℝ in (0 : ℝ)..1,
      deriv (fun z : ℂ ↦ F z - (A : ℂ) / (z - a) ^ (k + 1)) (s + u) *
        ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ) = 0 := by
  rw [neg_eq_zero]
  have hzero : ∫ _ : ℝ in (0 : ℝ)..1, (0 : ℂ) = 0 := intervalIntegral.integral_zero
  rw [← hzero]
  refine integral_congr_ae (.of_forall fun u hu ↦ ?_)
  rw [uIoc_of_le zero_le_one] at hu
  have hre : a < (s + u).re := by
    simp only [add_re, ofReal_re]
    linarith [hu.1]
  have hev : (fun z : ℂ ↦ F z - (A : ℂ) / (z - a) ^ (k + 1)) =ᶠ[𝓝 (s + u)] 0 :=
    eventuallyEq_of_mem ((isOpen_re_gt a).mem_nhds hre) fun z hz ↦ sub_eq_zero.mpr (hF z hz)
  simp [hev.deriv_eq]

/-- Updating the model pole `s ↦ A / (s - a) ^ (k + 1)` at `a` to any nonzero value `w` makes the
raw remainder `s ↦ F s - A / (s - a) ^ (k + 1)` discontinuous at `a` (it equals `w` at `a` and
`0` away from `a`). -/
theorem not_continuousAt_remainder_update_pole (a A : ℝ) (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    ¬ ContinuousAt
      (fun s : ℂ ↦ Function.update (fun z : ℂ ↦ (A : ℂ) / (z - a) ^ (k + 1)) (a : ℂ) w s -
        (A : ℂ) / (s - a) ^ (k + 1)) a := by
  have hR : (fun s : ℂ ↦ Function.update (fun z : ℂ ↦ (A : ℂ) / (z - a) ^ (k + 1)) (a : ℂ) w s -
      (A : ℂ) / (s - a) ^ (k + 1)) = Function.update (fun _ ↦ (0 : ℂ)) (a : ℂ) w := by
    ext s
    by_cases hs : s = a <;> simp [hs, zero_pow (Nat.succ_ne_zero k)]
  rw [hR, continuousAt_update_same, tendsto_const_nhds_iff]
  exact hw.symm

end TauCeti.HigherPoleTauberian
