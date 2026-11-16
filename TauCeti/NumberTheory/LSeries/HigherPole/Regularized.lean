/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.LSeries.HigherPole.Boundary
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242 (§3.3.1–3.3.2, pp. 221–224; §4.1, pp. 228–229; §5.2.1, pp. 237–238).
-/

public section

open Complex Filter intervalIntegral MeasureTheory Metric Set
open scoped Topology

namespace TauCeti.HigherPoleTauberian

/-! ### Private analytic and integral helpers -/

/-- On the open right half-plane `Re s > a`, the model-subtracted remainder
`R(s) = F(s) - A / (s - a) ^ (k + 1)` is analytic, so `deriv R` is also analytic (hence continuous)
there. -/
private theorem analyticOnNhd_deriv_remainder {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) :
    AnalyticOnNhd ℂ (deriv fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1))
      {s : ℂ | a < s.re} :=
  (h.sub (poleBoundary_div_sub_pow a A k)).interior.deriv

/-- Whenever `0 < ε + u`, the shifted boundary point `((a : ℂ) + ε + y * I) + u` lies in the open
right half-plane `{s : ℂ | a < s.re}`. -/
private theorem mem_re_gt_of_add_pos {a ε y u : ℝ} (h : 0 < ε + u) :
    (((a : ℂ) + ε + y * I) + u) ∈ {s : ℂ | a < s.re} := by
  simp
  linarith

/-- Triangle-inequality inclusion of `((a : ℂ) + ε + y * I) + u` into the closed ball around
`(a : ℂ) + y₀ * I` when `ε, u ≥ 0` and `ε + u + |y - y₀| ≤ r / 2`. -/
private theorem mem_closedBall_of_add_im_le {a ε u y y₀ r : ℝ} (hε0 : 0 ≤ ε) (hu0 : 0 ≤ u)
    (hsum : ε + u + |y - y₀| ≤ r / 2) :
    (((a : ℂ) + ε + y * I) + u) ∈ closedBall ((a : ℂ) + y₀ * I) (r / 2) := by
  rw [mem_closedBall, dist_eq_norm]
  have hsub : (((a : ℂ) + ε + y * I) + u) - ((a : ℂ) + y₀ * I) =
      ((ε + u : ℝ) : ℂ) + ((y - y₀ : ℝ) : ℂ) * I := by push_cast; ring
  have h1 : ‖((ε + u : ℝ) : ℂ)‖ = ε + u := Complex.norm_of_nonneg (add_nonneg hε0 hu0)
  have h2 : ‖((y - y₀ : ℝ) : ℂ) * I‖ = |y - y₀| := by simp [-ofReal_sub]
  calc
    ‖(((a : ℂ) + ε + y * I) + u) - ((a : ℂ) + y₀ * I)‖
        ≤ ‖((ε + u : ℝ) : ℂ)‖ + ‖((y - y₀ : ℝ) : ℂ) * I‖ := by rw [hsub]; exact norm_add_le _ _
    _ = ε + u + |y - y₀| := by rw [h1, h2]
    _ ≤ r / 2 := hsum

/-- Norm bound on the polynomial weight `((u ^ k / k! : ℝ) : ℂ)` for `u ∈ [0, 1]`. -/
private theorem norm_pow_div_factorial_le_one {k : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤ 1 := by
  have hfac : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hpow_nonneg : 0 ≤ u ^ k := pow_nonneg hu0 k
  have hpow_le : u ^ k ≤ 1 := pow_le_one₀ hu0 hu1
  rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg hpow_nonneg (by positivity))]
  exact div_le_one_of_le₀ (hpow_le.trans hfac) (by positivity)

/-- Pointwise bound on `‖z * (u ^ k / k!)‖` for `u ∈ [0, 1]` when `‖z‖ ≤ B` (`0 ≤ B`). -/
private theorem norm_mul_pow_div_factorial_le {z : ℂ} {B u : ℝ} {k : ℕ} (hz : ‖z‖ ≤ B)
    (hB : 0 ≤ B) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖z * (((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤ B := by
  rw [norm_mul]
  simpa using mul_le_mul hz (norm_pow_div_factorial_le_one hu0 hu1) (norm_nonneg _) hB

/-- Interval integral norm bound on `[c, 1]` (`0 ≤ c ≤ 1`) against the weight `u ^ k / k!`. -/
private theorem norm_intervalIntegral_mul_weight_le {f : ℝ → ℂ} {c B : ℝ} {k : ℕ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hB : 0 ≤ B) (hf : ∀ u ∈ Ioc c 1, ‖f u‖ ≤ B) :
    ‖∫ u : ℝ in c..1, f u * (((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤ B :=
  (norm_integral_le_of_norm_le_const fun u hu ↦ by
    rw [uIoc_of_le hc1] at hu
    exact norm_mul_pow_div_factorial_le (hf u hu) hB (hc0.trans hu.1.le) hu.2).trans
    (mul_le_of_le_one_right hB (by rw [abs_of_nonneg (by linarith)]; linarith))

/-- For every fixed `ε > 0`, `y ↦ H (a + ε + y * I)` is continuous on `ℝ`. -/
private theorem continuous_regularized_of_pos {R : ℂ → ℂ} {a : ℝ} {k : ℕ}
    (hR_cont : ContinuousOn (deriv R) {s : ℂ | a < s.re}) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun y : ℝ ↦
      -∫ u : ℝ in (0 : ℝ)..1,
        deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := by
  -- Clamp `u` to `max u 0` inside a globally continuous integrand that agrees on `[0, 1]`.
  let φ : ℝ × ℝ → ℂ := fun p ↦ ((a : ℂ) + ε + p.1 * I) + (max p.2 0 : ℝ)
  have hφ_cont : Continuous φ := by fun_prop
  have hφ_mem : ∀ p : ℝ × ℝ, φ p ∈ {s : ℂ | a < s.re} := fun p ↦
    mem_re_gt_of_add_pos (add_pos_of_pos_of_nonneg hε (le_max_right _ _))
  have h_uncurry : Continuous fun p : ℝ × ℝ ↦
      deriv R (φ p) * (((p.2 ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) :=
    (hR_cont.comp_continuous hφ_cont hφ_mem).mul (by fun_prop)
  have h_param : Continuous fun y : ℝ ↦
      -∫ u : ℝ in (0 : ℝ)..1,
        deriv R (φ (y, u)) * (((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) :=
    (continuous_parametric_intervalIntegral_of_continuous' h_uncurry 0 1).neg
  refine h_param.congr fun y ↦ congrArg Neg.neg (integral_congr fun u hu ↦ ?_)
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
  let ψ : ℝ × ℝ × ℝ → ℂ := fun p ↦ ((a : ℂ) + p.1 + p.2.1 * I) + p.2.2
  have hS_comp : IsCompact (ψ '' S) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image (by fun_prop)
  have hS_sub : ψ '' S ⊆ {s : ℂ | a < s.re} := by
    rintro _ ⟨⟨ε, y, u⟩, ⟨hε, -, hu⟩, rfl⟩
    exact mem_re_gt_of_add_pos (by linarith [hε.1, hu.1])
  obtain ⟨B, hB⟩ := hS_comp.exists_bound_of_continuousOn (hR_cont.mono hS_sub)
  exact ⟨max B 0, le_max_right _ _, fun ε hε y hy u hu ↦
    (hB (ψ (ε, y, u)) ⟨(ε, y, u), ⟨hε, hy, hu⟩, rfl⟩).trans (le_max_left _ _)⟩

/-- Local analytic continuation of `R` around an off-pole boundary point `a + y₀ * I` (`y₀ ≠ 0`)
yields a radius `ρ > 0` and a uniform bound `B ≥ 0` on `‖deriv R (((a : ℂ) + ε + y * I) + u)‖`
for all `ε ∈ [0, ρ]`, `y ∈ ball y₀ ρ`, and `u ∈ (0, 1]`. -/
private theorem exists_away_local_bound {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) {y₀ : ℝ} (hy₀ : y₀ ≠ 0) :
    let R := fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1)
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ ε ∈ Icc (0 : ℝ) ρ, ∀ y ∈ ball y₀ ρ, ∀ u ∈ Ioc (0 : ℝ) 1,
        ‖deriv R (((a : ℂ) + ε + y * I) + u)‖ ≤ B := by
  intro R
  obtain ⟨r, hr, R₀, hR₀_an, hR_eq⟩ := (h.sub (poleBoundary_div_sub_pow a A k)).away y₀ hy₀
  let z₀ : ℂ := (a : ℂ) + y₀ * I
  have hderiv_eq : ∀ s ∈ ball z₀ r, a < s.re → deriv R s = deriv R₀ s := by
    intro s hs hsre
    have hopen : IsOpen (ball z₀ r ∩ {w : ℂ | a < w.re}) := isOpen_ball.inter (isOpen_re_gt a)
    exact (eventuallyEq_of_mem (hopen.mem_nhds ⟨hs, hsre⟩)
      fun w ⟨hw, hwre⟩ ↦ hR_eq w hw hwre).deriv_eq
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
      mem_closedBall_of_add_im_le hε.1 hu0.le (by linarith [hε.2])
    rw [hderiv_eq _ (closedBall_subset_ball (half_lt_self hr) hdist)
      (mem_re_gt_of_add_pos (by linarith [hε.1]))]
    exact (hB₁ _ hdist).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have habs := abs_le.mp hy'.le
    have hy_Icc : y ∈ Icc (-(|y₀| + ρ)) (|y₀| + ρ) :=
      ⟨by linarith [neg_abs_le y₀], by linarith [le_abs_self y₀]⟩
    exact (hB₂ ε hε y hy_Icc u ⟨(lt_of_not_ge huρ).le, hu1⟩).trans (le_max_right _ _)

/-- Right-continuity of `H (a + ε + y₀ * I)` as `ε → 0⁺` at any off-pole point `y₀ ≠ 0`. -/
private theorem tendsto_regularized_of_ne_zero {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) {y₀ : ℝ} (hy₀ : y₀ ≠ 0) :
    let R := fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1)
    Tendsto (fun ε : ℝ ↦
        -∫ u : ℝ in (0 : ℝ)..1,
          deriv R (((a : ℂ) + ε + y₀ * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))
      (𝓝[>] 0)
      (𝓝 (-∫ u : ℝ in (0 : ℝ)..1,
        deriv R (((a : ℂ) + y₀ * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))) := by
  intro R
  obtain ⟨ρ, hρ, B, hB0, hbound⟩ := exists_away_local_bound h hy₀
  have hR_cont : ContinuousOn (deriv R) {s : ℂ | a < s.re} :=
    (analyticOnNhd_deriv_remainder h).continuousOn
  have h_cwa : ContinuousWithinAt
      (fun ε : ℝ ↦ ∫ u : ℝ in (0 : ℝ)..1,
        deriv R (((a : ℂ) + ε + y₀ * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))
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
      (fun ε : ℝ ↦ -∫ u : ℝ in (0 : ℝ)..1,
        deriv R (((a : ℂ) + ε + y₀ * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))
      (Ici 0) 0 := h_cwa.neg
  simpa using h_neg.tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)

/-- Finite-subcover uniform bound on `‖H (a + ε + y * I)‖` across the compact off-pole set
`{y ∈ [-L, L] | δ ≤ |y|}` (`0 < δ`). -/
private theorem exists_away_compact_bound {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) {δ L : ℝ} (hδ : 0 < δ) :
    let R := fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1)
    ∃ ε_away : ℝ, 0 < ε_away ∧ ∃ B_away : ℝ, 0 ≤ B_away ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε_away, ∀ y ∈ Icc (-L) L, δ ≤ |y| →
        ‖-∫ u : ℝ in (0 : ℝ)..1,
          deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)‖ ≤
          B_away := by
  intro R
  let K : Set ℝ := {y ∈ Icc (-L) L | δ ≤ |y|}
  have hK_comp : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hK_loc : ∀ y₀ : K, ∃ ρ : ℝ, 0 < ρ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ ε ∈ Icc (0 : ℝ) ρ, ∀ y ∈ ball (y₀ : ℝ) ρ, ∀ u ∈ Ioc (0 : ℝ) 1,
        ‖deriv R (((a : ℂ) + ε + y * I) + u)‖ ≤ B := fun ⟨_, _, hy₀δ⟩ ↦
    exists_away_local_bound h (abs_pos.mp (hδ.trans_le hy₀δ))
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
  rw [norm_neg]
  exact (norm_intervalIntegral_mul_weight_le le_rfl zero_le_one (hB0 y₀)
    (hB y₀ ε hε_Icc y hy_ball)).trans (Finset.single_le_sum (f := B) (fun z _ ↦ hB0 z) hy₀t)

/-- Subtracting `A` from an analytic numerator `g` with `g a = A` lowers the polar order of
`(g z - A) / (z - a) ^ (k + 1)` at `a` to at most `k`. -/
private theorem meromorphicPolarOrderAt_remainder_le {g : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (hg : AnalyticAt ℂ g a) (hga : g a = A) :
    TauCeti.Contour.meromorphicPolarOrderAt
      ((fun z : ℂ ↦ g z - (A : ℂ)) / fun z : ℂ ↦ (z - a) ^ (k + 1)) a ≤ k := by
  set f : ℂ → ℂ := fun z ↦ g z - (A : ℂ)
  set d : ℂ → ℂ := fun z ↦ (z - a) ^ (k + 1)
  have hf_an : AnalyticAt ℂ f a := hg.sub analyticAt_const
  have hd_an : AnalyticAt ℂ d a := (analyticAt_id.sub analyticAt_const).pow (k + 1)
  have hf_ord : (1 : WithTop ℤ) ≤ meromorphicOrderAt f a := by
    have hne0 : analyticOrderAt f a ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hf_an, sub_eq_zero.mpr hga⟩
    rw [hf_an.meromorphicOrderAt_eq]
    cases hord : analyticOrderAt f a with
    | top => exact le_top
    | coe n =>
      exact WithTop.coe_le_coe.mpr
        (Int.ofNat_le.mpr (Nat.pos_of_ne_zero fun h0 ↦ hne0 (by simp [hord, h0])))
  have hQ_ord : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (f / d) a := by
    rw [meromorphicOrderAt_div hf_an.meromorphicAt hd_an.meromorphicAt]
    have hd_ord : meromorphicOrderAt d a = (((k + 1 : ℕ) : ℤ) : WithTop ℤ) := by
      simp [d, fun_meromorphicOrderAt_pow_id_sub_const]
    rw [hd_ord]
    cases hx : meromorphicOrderAt f a with
    | top => simp
    | coe n =>
      rw [hx] at hf_ord
      have hn1 : (1 : ℤ) ≤ n := WithTop.coe_le_coe.mp hf_ord
      rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_le_coe]
      omega
  by_contra hlt
  have hpos : 0 < TauCeti.Contour.meromorphicPolarOrderAt (f / d) a := by omega
  have heq := TauCeti.Contour.meromorphicOrderAt_eq_neg_of_meromorphicPolarOrderAt_pos hpos
  rw [heq, ← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_le_coe] at hQ_ord
  omega

/-- Termwise derivative of a finite Laurent principal part `∑ i : Fin m, c i / (w - a) ^ (i + 1)`
away from `a`. -/
private theorem hasDerivAt_laurent_principal_part {m : ℕ} (c : Fin m → ℂ) {a : ℝ} {z : ℂ}
    (hza : z - (a : ℂ) ≠ 0) :
    HasDerivAt (fun w : ℂ ↦ ∑ i : Fin m, c i / (w - a) ^ (i.val + 1))
      (∑ i : Fin m, c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2))) z := by
  refine HasDerivAt.fun_sum fun i _ ↦ ?_
  have hp : HasDerivAt (fun w : ℂ ↦ (w - a) ^ (i.val + 1))
      (((i.val + 1 : ℕ) : ℂ) * (z - a) ^ i.val) z := by
    simpa only [add_tsub_cancel_right, mul_one, id_eq] using
      HasDerivAt.fun_pow ((hasDerivAt_id z).sub_const (a : ℂ)) (i.val + 1)
  have hmul : HasDerivAt (fun w : ℂ ↦ c i / (w - a) ^ (i.val + 1))
      (c i * (-(((i.val + 1 : ℕ) : ℂ) * (z - a) ^ i.val) /
        ((z - a) ^ (i.val + 1)) ^ 2)) z := by
    simpa [div_eq_mul_inv] using (hp.inv (pow_ne_zero _ hza)).const_mul (c i)
  refine hmul.congr_deriv (congrArg (c i * ·) ?_)
  have hsq : ((z - (a : ℂ)) ^ (i.val + 1)) ^ 2 = (z - a) ^ (i.val + 2) * (z - a) ^ i.val := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hsq, neg_div, mul_div_mul_right _ _ (pow_ne_zero _ hza), ← neg_div]

/-- Laurent decomposition of `R` on a right half-disc near `a`: the polar order is at most `k`,
and `deriv R` decomposes into an analytic derivative plus at most `k` polar derivative terms. -/
private theorem exists_near_pole_deriv_laurent {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) :
    let R := fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1)
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∃ m : ℕ, m ≤ k ∧ ∃ (c : Fin m → ℂ) (q : ℂ → ℂ),
      AnalyticOnNhd ℂ q (ball (a : ℂ) r₁) ∧
      ∀ z ∈ ball (a : ℂ) r₁, a < z.re →
        deriv R z = deriv q z +
          ∑ i : Fin m, c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2)) := by
  intro R
  obtain ⟨r₀, hr₀, g, hg, hga, hF⟩ := h.pole
  let f : ℂ → ℂ := fun z ↦ g z - (A : ℂ)
  let d : ℂ → ℂ := fun z ↦ (z - a) ^ (k + 1)
  let Q : ℂ → ℂ := f / d
  have hf_an : AnalyticAt ℂ f a := (hg a (mem_ball_self hr₀)).sub analyticAt_const
  have hd_an : AnalyticAt ℂ d a := (analyticAt_id.sub analyticAt_const).pow (k + 1)
  obtain ⟨c, q, hq_an, hQ_laur⟩ := TauCeti.Contour.exists_laurent_data_of_meromorphicAt
    (hf_an.meromorphicAt.div hd_an.meromorphicAt)
  obtain ⟨r_q, hr_q, hq_ball⟩ := hq_an.exists_ball_analyticOnNhd
  obtain ⟨r_e, hr_e, hlaur_ball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hQ_laur)
  let r₁ : ℝ := min r₀ (min r_q r_e)
  have hsub₀ : ball (a : ℂ) r₁ ⊆ ball (a : ℂ) r₀ := ball_subset_ball (min_le_left _ _)
  have hsub_q : ball (a : ℂ) r₁ ⊆ ball (a : ℂ) r_q :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hsub_e : ball (a : ℂ) r₁ ⊆ ball (a : ℂ) r_e :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r₁, lt_min hr₀ (lt_min hr_q hr_e), _,
    meromorphicPolarOrderAt_remainder_le (hg a (mem_ball_self hr₀)) hga,
    c, q, hq_ball.mono hsub_q, fun z hz hzre ↦ ?_⟩
  have hopen : IsOpen (ball (a : ℂ) r₁ ∩ {w : ℂ | a < w.re}) :=
    isOpen_ball.inter (isOpen_re_gt a)
  have hev : R =ᶠ[𝓝 z] fun w ↦ q w + ∑ i, c i / (w - a) ^ (i.val + 1) := by
    refine eventuallyEq_of_mem (hopen.mem_nhds ⟨hz, hzre⟩) fun w ⟨hw, hwre⟩ ↦ ?_
    have hwa : w ≠ a := fun h0 ↦ by simp [h0] at hwre
    have hRw : R w = Q w := by simp only [R, Q, Pi.div_apply, f, d, hF w (hsub₀ hw) hwre, sub_div]
    exact hRw.trans (hlaur_ball w (hsub_e hw) hwa)
  rw [hev.deriv_eq]
  have hza : z - (a : ℂ) ≠ 0 := sub_ne_zero.mpr fun h0 ↦ by simp [h0] at hzre
  exact (((hq_ball _ (hsub_q hz)).differentiableAt.hasDerivAt).add
    (hasDerivAt_laurent_principal_part c hza)).deriv

/-- Elementary norm lower bound `(u + |y|) / 2 ≤ ‖((ε + u : ℝ) : ℂ) + y * I‖` for `ε, u ≥ 0`. -/
private theorem half_add_abs_le_norm {ε u y : ℝ} (hε : 0 ≤ ε) (hu : 0 ≤ u) :
    (u + |y|) / 2 ≤ ‖((ε + u : ℝ) : ℂ) + y * I‖ := by
  let w : ℂ := ((ε + u : ℝ) : ℂ) + y * I
  have hre : u ≤ ‖w‖ := by
    have h1 : |w.re| ≤ ‖w‖ := abs_re_le_norm w
    have h2 : w.re = ε + u := by simp [w]
    rw [h2, abs_of_nonneg (by linarith)] at h1
    linarith
  have him : |y| ≤ ‖w‖ := by simpa [w] using abs_im_le_norm w
  linarith

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
  have hz_sub : z - a = ((ε + u : ℝ) : ℂ) + y * I := by simp only [z]; push_cast; ring
  have hza_ge : (u + |y|) / 2 ≤ ‖z - a‖ := hz_sub ▸ half_add_abs_le_norm hε0 hu0.le
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

/-- Interval integrability and logarithmic upper bound for `∫ u in 0..δ, (M₀ + C * (u + |y|)⁻¹)`
when `0 < δ ≤ 1` and `0 < |y| ≤ δ`. -/
private theorem integral_const_add_inv_le_log {M₀ C δ y : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hM₀ : 0 ≤ M₀) (hC : 0 ≤ C) (hy0 : y ≠ 0) (hyδ : |y| ≤ δ) :
    IntervalIntegrable (fun u : ℝ ↦ M₀ + C * (u + |y|)⁻¹) volume 0 δ ∧
      ∫ u : ℝ in (0 : ℝ)..δ, (M₀ + C * (u + |y|)⁻¹) ≤ M₀ + C * (Real.log 2 + |Real.log y|) := by
  have hy_pos : 0 < |y| := abs_pos.mpr hy0
  have hinv_int : IntervalIntegrable (fun u : ℝ ↦ (u + |y|)⁻¹) volume 0 δ := by
    refine ContinuousOn.intervalIntegrable_of_Icc hδ0.le
      ((continuousOn_id.add continuousOn_const).inv₀ fun u hu h0 ↦ ?_)
    simp only [Pi.add_apply, id_eq] at h0
    linarith [hu.1]
  have hmaj_int : IntervalIntegrable (fun u : ℝ ↦ M₀ + C * (u + |y|)⁻¹) volume 0 δ :=
    intervalIntegrable_const.add (hinv_int.const_mul C)
  refine ⟨hmaj_int, ?_⟩
  have heval : ∫ u : ℝ in (0 : ℝ)..δ, (M₀ + C * (u + |y|)⁻¹) =
      M₀ * δ + C * Real.log ((δ + |y|) / |y|) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hinv_int.const_mul C),
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
  rw [heval]
  calc
    M₀ * δ + C * Real.log ((δ + |y|) / |y|)
        ≤ M₀ * 1 + C * (Real.log 2 + |Real.log y|) := by gcongr
    _ = M₀ + C * (Real.log 2 + |Real.log y|) := by ring

/-- Logarithmic bound near the pole: there exist `δ > 0` and constants `C₁, C₂ ≥ 0` such that
for all `ε ∈ (0, δ)` and all `y` with `0 < |y| ≤ δ`,
`‖H (a + ε + y * I)‖ ≤ C₁ + C₂ * |Real.log y|`. -/
private theorem exists_near_pole_log_bound {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) :
    let R := fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1)
    ∃ δ : ℝ, 0 < δ ∧ ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ ε ∈ Ioo (0 : ℝ) δ, ∀ y : ℝ, y ≠ 0 → |y| ≤ δ →
        ‖-∫ u : ℝ in (0 : ℝ)..1,
          deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)‖ ≤
          C₁ + C₂ * |Real.log y| := by
  intro R
  obtain ⟨r₁, hr₁, m, hm_le, c, q, hq_ball, hderiv_laur⟩ := exists_near_pole_deriv_laurent h
  let δ : ℝ := min 1 (r₁ / 6)
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  obtain ⟨M_q, hMq⟩ := (isCompact_closedBall (a : ℂ) (r₁ / 2)).exists_bound_of_continuousOn
    (hq_ball.deriv.continuousOn.mono (closedBall_subset_ball (half_lt_self hr₁)))
  have hR_cont : ContinuousOn (deriv R) {s : ℂ | a < s.re} :=
    (analyticOnNhd_deriv_remainder h).continuousOn
  obtain ⟨B_tail, hBt0, hBt⟩ := exists_tail_bound (ε₁ := δ) (L := δ) hR_cont hδ
  let C_pole : ℝ := ∑ i : Fin m, ‖c i‖ * ((i.val + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (i.val + 2)
  have hCp0 : 0 ≤ C_pole := Finset.sum_nonneg fun i _ ↦ by positivity
  let C₁ : ℝ := max M_q 0 + B_tail + C_pole * Real.log 2
  refine ⟨δ, hδ, C₁, C_pole, by have := Real.log_nonneg one_le_two; positivity, hCp0,
    fun ε hε y hy0 hyδ ↦ ?_⟩
  -- Split `[0, 1]` at `δ` into the Laurent-controlled head `[0, δ]` and compact tail `[δ, 1]`.
  let φ : ℝ → ℂ := fun u ↦
    deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
  have hφ_cont : ContinuousOn φ (Icc 0 1) :=
    (hR_cont.comp (by fun_prop) fun u hu ↦ mem_re_gt_of_add_pos (by linarith [hε.1, hu.1])).mul
      (by fun_prop)
  rw [norm_neg, ← integral_add_adjacent_intervals
    ((hφ_cont.mono (Icc_subset_Icc_right hδ1)).intervalIntegrable_of_Icc hδ.le)
    ((hφ_cont.mono (Icc_subset_Icc_left hδ.le)).intervalIntegrable_of_Icc hδ1)]
  have htail_le : ‖∫ u : ℝ in δ..1, φ u‖ ≤ B_tail :=
    norm_intervalIntegral_mul_weight_le hδ.le hδ1 hBt0 fun u hu ↦
      hBt ε ⟨hε.1.le, hε.2.le⟩ y (abs_le.mp hyδ) u ⟨hu.1.le, hu.2⟩
  obtain ⟨hmaj_int, heval_le⟩ :=
    integral_const_add_inv_le_log hδ hδ1 (le_max_right M_q 0) hCp0 hy0 hyδ
  have hhead_le : ‖∫ u : ℝ in (0 : ℝ)..δ, φ u‖ ≤
      ∫ u : ℝ in (0 : ℝ)..δ, (max M_q 0 + C_pole * (u + |y|)⁻¹) :=
    norm_integral_le_of_norm_le hδ.le (.of_forall fun u ⟨hu0, huδ⟩ ↦ by
      set z : ℂ := ((a : ℂ) + ε + y * I) + u with hz
      have hz_cb : z ∈ closedBall (a : ℂ) (r₁ / 2) := by
        simpa using mem_closedBall_of_add_im_le (a := a) (y₀ := 0) hε.1.le hu0.le
          (by simpa using (by linarith [hε.2, min_le_right 1 (r₁ / 6)] : ε + u + |y| ≤ r₁ / 2))
      simp only [φ]
      rw [← hz, hderiv_laur z (closedBall_subset_ball (half_lt_self hr₁) hz_cb)
        (mem_re_gt_of_add_pos (by linarith [hε.1]))]
      exact norm_laurent_integrand_le hm_le ((hMq z hz_cb).trans (le_max_left _ _))
        (le_max_right _ _) hε.1.le hu0 (huδ.trans hδ1)) hmaj_int
  refine (norm_add_le _ _).trans ((add_le_add (hhead_le.trans heval_le) htail_le).trans_eq ?_)
  simp only [C₁]
  ring

/-- Uniform integrable majorant on `Icc (-L) L` (`0 < L`) combining the near-pole logarithmic
bound and the compact off-pole bound. -/
private theorem exists_compact_majorant {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) {L : ℝ} (hL : 0 < L) :
    let R := fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1)
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ M : ℝ → ℝ, IntegrableOn M (Icc (-L) L) ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ y ∈ Icc (-L) L, y ≠ 0 →
        ‖-∫ u : ℝ in (0 : ℝ)..1,
          deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)‖ ≤ M y := by
  intro R
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
  dsimp only [H]
  let b : ℝ → ℂ := fun y ↦ if y = 0 then 0 else
    -∫ u : ℝ in (0 : ℝ)..1, deriv R (((a : ℂ) + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
  have hR_cont : ContinuousOn (deriv R) {s : ℂ | a < s.re} :=
    (analyticOnNhd_deriv_remainder h).continuousOn
  have h_ptwise : ∀ y : ℝ, y ≠ 0 →
      Tendsto (fun ε : ℝ ↦ -∫ u : ℝ in (0 : ℝ)..1,
        deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))
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
      (f := fun (n : ℕ) (y : ℝ) ↦ -∫ u : ℝ in (0 : ℝ)..1,
        deriv R (((a : ℂ) + ε_seq n + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))
      (fun n ↦ (continuous_regularized_of_pos (k := k) hR_cont (hseq_pos n)).aestronglyMeasurable)
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
          exact ((continuous_regularized_of_pos (k := k) hR_cont hε.1).aestronglyMeasurable.sub
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
raw remainder `R(s) = F(s) - A / (s - a) ^ (k + 1)` discontinuous at `a` (it equals `w` at `a` and
`0` away from `a`). -/
theorem not_continuousAt_remainder_update_pole (a A : ℝ) (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    let F := Function.update (fun s : ℂ ↦ (A : ℂ) / (s - a) ^ (k + 1)) (a : ℂ) w
    let R := fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1)
    ¬ ContinuousAt R a := by
  intro F R
  have hR : R = Function.update (fun _ ↦ (0 : ℂ)) (a : ℂ) w := by
    ext s
    by_cases hs : s = a <;> simp [R, F, hs, zero_pow (Nat.succ_ne_zero k)]
  rw [hR, continuousAt_update_same, tendsto_const_nhds_iff]
  exact hw.symm

end TauCeti.HigherPoleTauberian
