/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.LSeries.HigherPole.Boundary
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
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
  `a` breaks continuity of the raw remainder at `a` while preserving `PoleBoundary` and the
  vanishing of the regularised integral on `Re s ≥ a`.

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

/-- Norm bound on the polynomial weight `((u ^ k / k! : ℝ) : ℂ)` for `u ∈ [0, 1]`. -/
private theorem norm_pow_div_factorial_le_one {k : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤ 1 := by
  have hfac : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hpow_nonneg : 0 ≤ u ^ k := pow_nonneg hu0 k
  have hpow_le : u ^ k ≤ 1 := pow_le_one₀ hu0 hu1
  rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg hpow_nonneg (by positivity))]
  exact div_le_one_of_le₀ (hpow_le.trans hfac) (by positivity)

/-- For every fixed `ε > 0`, `y ↦ H (a + ε + y * I)` is continuous on `ℝ`. -/
private theorem continuous_regularized_of_pos {R : ℂ → ℂ} {a : ℝ} {k : ℕ}
    (hR_cont : ContinuousOn (deriv R) {s : ℂ | a < s.re}) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun y : ℝ ↦
      -∫ u : ℝ in (0 : ℝ)..1,
        deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := by
  -- Clamp `u` to `max u 0` inside a globally continuous integrand that agrees on `[0, 1]`.
  let φ : ℝ × ℝ → ℂ := fun p ↦ ((a : ℂ) + ε + p.1 * I) + (max p.2 0 : ℝ)
  have hφ_cont : Continuous φ := by fun_prop
  have hφ_mem : ∀ p : ℝ × ℝ, φ p ∈ {s : ℂ | a < s.re} := by
    intro p
    have hm : 0 ≤ max p.2 0 := le_max_right _ _
    change a < (φ p).re
    simp only [φ, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]
    linarith
  have h_uncurry : Continuous fun p : ℝ × ℝ ↦
      deriv R (φ p) * (((p.2 ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) :=
    (hR_cont.comp_continuous hφ_cont hφ_mem).mul (by fun_prop)
  have h_param : Continuous fun y : ℝ ↦
      -∫ u : ℝ in (0 : ℝ)..1,
        deriv R (φ (y, u)) * (((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) :=
    (continuous_parametric_intervalIntegral_of_continuous' h_uncurry 0 1).neg
  refine h_param.congr fun y ↦ congrArg Neg.neg ?_
  refine integral_congr fun u hu ↦ ?_
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
    change a < (ψ (ε, y, u)).re
    simp only [ψ, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]
    linarith [hε.1, hu.1]
  obtain ⟨B, hB⟩ := hS_comp.exists_bound_of_continuousOn (hR_cont.mono hS_sub)
  refine ⟨max B 0, le_max_right _ _, fun ε hε y hy u hu ↦ ?_⟩
  exact (hB (ψ (ε, y, u)) ⟨(ε, y, u), ⟨hε, hy, hu⟩, rfl⟩).trans (le_max_left _ _)

/-- Local analytic continuation of `R` around an off-pole boundary point `a + y₀ * I` (`y₀ ≠ 0`)
yields a radius `ρ ∈ (0, 1]` and a uniform bound `B ≥ 0` on `‖deriv R (((a : ℂ) + ε + y * I) + u)‖`
for all `ε ∈ [0, ρ]`, `y ∈ ball y₀ ρ`, and `u ∈ (0, 1]`, together with right-continuity at `ε = 0`
at `y = y₀`. -/
private theorem exists_away_local_data {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) {y₀ : ℝ} (hy₀ : y₀ ≠ 0) :
    let R := fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1)
    (∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ ε ∈ Icc (0 : ℝ) ρ, ∀ y ∈ ball y₀ ρ, ∀ u ∈ Ioc (0 : ℝ) 1,
        ‖deriv R (((a : ℂ) + ε + y * I) + u)‖ ≤ B) ∧
    Tendsto (fun ε : ℝ ↦
        -∫ u : ℝ in (0 : ℝ)..1,
          deriv R (((a : ℂ) + ε + y₀ * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))
      (𝓝[>] 0)
      (𝓝 (-∫ u : ℝ in (0 : ℝ)..1,
        deriv R (((a : ℂ) + y₀ * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))) := by
  intro R
  obtain ⟨r₁, hr₁, g₁, hg₁, hF₁⟩ := h.away y₀ hy₀
  obtain ⟨r₂, hr₂, g₂, hg₂, hM₂⟩ := (poleBoundary_div_sub_pow a A k).away y₀ hy₀
  let z₀ : ℂ := (a : ℂ) + y₀ * I
  let r : ℝ := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  let R₀ : ℂ → ℂ := fun s ↦ g₁ s - g₂ s
  have hR₀_an : AnalyticOnNhd ℂ R₀ (ball z₀ r) :=
    (hg₁.mono (ball_subset_ball (min_le_left _ _))).sub
      (hg₂.mono (ball_subset_ball (min_le_right _ _)))
  have hderiv_eq : ∀ s ∈ ball z₀ r, a < s.re → deriv R s = deriv R₀ s := by
    intro s hs hsre
    have hopen : IsOpen (ball z₀ r ∩ {w : ℂ | a < w.re}) := isOpen_ball.inter (isOpen_re_gt a)
    have hev : R =ᶠ[𝓝 s] R₀ :=
      eventuallyEq_of_mem (hopen.mem_nhds ⟨hs, hsre⟩) fun w ⟨hw, hwre⟩ ↦ by
        simp [R, R₀, hF₁ w (ball_subset_ball (min_le_left _ _) hw) hwre,
          hM₂ w (ball_subset_ball (min_le_right _ _) hw) hwre]
    exact hev.deriv_eq
  let ρ : ℝ := min 1 (r / 6)
  have hρ : 0 < ρ := lt_min zero_lt_one (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  obtain ⟨B₁, hB₁⟩ := (isCompact_closedBall z₀ (r / 2)).exists_bound_of_continuousOn
    (hR₀_an.deriv.continuousOn.mono (closedBall_subset_ball (half_lt_self hr)))
  have hR_cont : ContinuousOn (deriv R) {s : ℂ | a < s.re} :=
    (analyticOnNhd_deriv_remainder h).continuousOn
  obtain ⟨B₂, -, hB₂⟩ := exists_tail_bound (ε₁ := ρ) (L := |y₀| + ρ) hR_cont hρ
  let B : ℝ := max (max B₁ 0) B₂
  have hB0 : 0 ≤ B := le_trans (le_max_right _ _) (le_max_left _ _)
  have hbound : ∀ ε ∈ Icc (0 : ℝ) ρ, ∀ y ∈ ball y₀ ρ, ∀ u ∈ Ioc (0 : ℝ) 1,
      ‖deriv R (((a : ℂ) + ε + y * I) + u)‖ ≤ B := by
    intro ε hε y hy u ⟨hu0, hu1⟩
    by_cases huρ : u ≤ ρ
    · have hre : a < (((a : ℂ) + ε + y * I) + u).re := by
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero]
        linarith [hε.1]
      have hdist : (((a : ℂ) + ε + y * I) + u) ∈ closedBall z₀ (r / 2) := by
        rw [mem_closedBall, dist_eq_norm]
        have hsub : (((a : ℂ) + ε + y * I) + u) - z₀ =
            ((ε + u : ℝ) : ℂ) + ((y - y₀ : ℝ) : ℂ) * I := by
          simp only [z₀]
          push_cast
          ring
        have hy' : |y - y₀| < ρ := by simpa [Real.dist_eq] using mem_ball.mp hy
        have hρ_le : ρ ≤ r / 6 := min_le_right _ _
        calc
          ‖(((a : ℂ) + ε + y * I) + u) - z₀‖
              ≤ ‖((ε + u : ℝ) : ℂ)‖ + ‖((y - y₀ : ℝ) : ℂ) * I‖ := by
            rw [hsub]; exact norm_add_le _ _
          _ = |ε + u| + |y - y₀| := by
            rw [Complex.norm_real, norm_mul, Complex.norm_real, norm_I, mul_one,
              Real.norm_eq_abs, Real.norm_eq_abs]
          _ = ε + u + |y - y₀| := by rw [abs_of_nonneg (by linarith [hε.1])]
          _ ≤ r / 2 := by linarith [hε.2]
      rw [hderiv_eq _ (closedBall_subset_ball (half_lt_self hr) hdist) hre]
      exact (hB₁ _ hdist).trans ((le_max_left _ _).trans (le_max_left _ _))
    · have huρ' : ρ < u := lt_of_not_ge huρ
      have hy_Icc : y ∈ Icc (-(|y₀| + ρ)) (|y₀| + ρ) := by
        have hy' : |y - y₀| < ρ := by simpa [Real.dist_eq] using mem_ball.mp hy
        have habs := abs_le.mp (le_of_lt hy')
        have hy₀_abs := neg_abs_le y₀
        have hy₀_abs' := le_abs_self y₀
        exact ⟨by linarith, by linarith⟩
      exact (hB₂ ε hε y hy_Icc u ⟨huρ'.le, hu1⟩).trans (le_max_right _ _)
  refine ⟨⟨ρ, hρ, hρ1, B, hB0, hbound⟩, ?_⟩
  -- Right-continuity at `ε = 0` follows from `continuousWithinAt_of_dominated_interval` on `Ici 0`.
  have h_cwa : ContinuousWithinAt
      (fun ε : ℝ ↦ ∫ u : ℝ in (0 : ℝ)..1,
        deriv R (((a : ℂ) + ε + y₀ * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))
      (Ici 0) 0 := by
    refine continuousWithinAt_of_dominated_interval (bound := fun _ ↦ B) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [Icc_mem_nhdsGE hρ] with ε hε
      rw [uIoc_of_le zero_le_one]
      have hcont_on : ContinuousOn
          (fun u : ℝ ↦ deriv R (((a : ℂ) + ε + y₀ * I) + u) *
            ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) (Ioc 0 1) := by
        refine (hR_cont.comp (by fun_prop) fun u hu ↦ ?_).mul (by fun_prop)
        change a < (((a : ℂ) + ε + y₀ * I) + u).re
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero]
        linarith [hε.1, hu.1]
      exact (hcont_on.aestronglyMeasurable measurableSet_Ioc)
    · filter_upwards [Icc_mem_nhdsGE hρ] with ε hε
      refine .of_forall fun u hu ↦ ?_
      rw [uIoc_of_le zero_le_one] at hu
      rw [norm_mul]
      calc
        ‖deriv R (((a : ℂ) + ε + y₀ * I) + u)‖ * ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖
            ≤ B * 1 := mul_le_mul (hbound ε hε y₀ (mem_ball_self hρ) u hu)
              (norm_pow_div_factorial_le_one hu.1.le hu.2) (norm_nonneg _) hB0
        _ = B := mul_one B
    · refine .of_forall fun u hu ↦ ?_
      rw [uIoc_of_le zero_le_one] at hu
      have hcont_at : ContinuousAt
          (fun ε : ℝ ↦ deriv R (((a : ℂ) + ε + y₀ * I) + u) *
            ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) 0 := by
        have hmem : (((a : ℂ) + (0 : ℝ) + y₀ * I) + u) ∈ {s : ℂ | a < s.re} := by
          simp [hu.1]
        have hinner : ContinuousAt (fun ε : ℝ ↦ (((a : ℂ) + ε + y₀ * I) + u)) 0 := by fun_prop
        exact (((analyticOnNhd_deriv_remainder h _ hmem).continuousAt).comp_of_eq
          hinner rfl).mul continuousAt_const
      exact hcont_at.continuousWithinAt
  have h_neg : ContinuousWithinAt
      (fun ε : ℝ ↦ -∫ u : ℝ in (0 : ℝ)..1,
        deriv R (((a : ℂ) + ε + y₀ * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))
      (Ici 0) 0 := h_cwa.neg
  simpa using h_neg.tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)

/-- Finite-subcover uniform bound on `‖H (a + ε + y * I)‖` across the compact off-pole set
`{y ∈ [-L, L] | δ ≤ |y|}` (`0 < δ`, `0 < L`). -/
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
        ‖deriv R (((a : ℂ) + ε + y * I) + u)‖ ≤ B := by
    rintro ⟨y₀, -, hy₀δ⟩
    have hy₀ : y₀ ≠ 0 := abs_pos.mp (hδ.trans_le hy₀δ)
    obtain ⟨⟨ρ, hρ, -, B, hB0, hb⟩, -⟩ := exists_away_local_data h hy₀
    exact ⟨ρ, hρ, B, hB0, hb⟩
  choose ρ hρ B hB0 hB using hK_loc
  have hcov : K ⊆ ⋃ y₀ : K, ball (y₀ : ℝ) (ρ y₀) := fun y hy ↦
    mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hρ ⟨y, hy⟩)⟩
  obtain ⟨t, ht_cov⟩ := hK_comp.elim_finite_subcover (fun y₀ : K ↦ ball (y₀ : ℝ) (ρ y₀))
    (fun _ ↦ isOpen_ball) hcov
  have hε_ex : ∀ s : Finset K, ∃ ε_away : ℝ, 0 < ε_away ∧ ∀ y₀ ∈ s, ε_away ≤ ρ y₀ :=
    fun s ↦ by
      classical
      induction s using Finset.induction with
      | empty => exact ⟨1, zero_lt_one, by simp⟩
      | insert a₀ s _ ih =>
        obtain ⟨ε_s, hε_s, hs⟩ := ih
        refine ⟨min (ρ a₀) ε_s, lt_min (hρ a₀) hε_s, fun z hz ↦ ?_⟩
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hs z hz)
  obtain ⟨ε_away, hε_away, hε_le⟩ := hε_ex t
  refine ⟨ε_away, hε_away, ∑ y₀ ∈ t, B y₀, Finset.sum_nonneg (fun y₀ _ ↦ hB0 y₀),
    fun ε hε y hyL hyδ ↦ ?_⟩
  have hy_mem : y ∈ ⋃ y₀ ∈ t, ball (y₀ : ℝ) (ρ y₀) := ht_cov ⟨hyL, hyδ⟩
  rcases mem_iUnion₂.mp hy_mem with ⟨y₀, hy₀t, hy_ball⟩
  have hε_Icc : ε ∈ Icc (0 : ℝ) (ρ y₀) := ⟨hε.1.le, hε.2.le.trans (hε_le y₀ hy₀t)⟩
  rw [norm_neg]
  have hint_le : ‖∫ u : ℝ in (0 : ℝ)..1,
      deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)‖ ≤
      B y₀ * |(1 : ℝ) - 0| := by
    refine norm_integral_le_of_norm_le_const fun u hu ↦ ?_
    rw [uIoc_of_le zero_le_one] at hu
    rw [norm_mul]
    calc
      ‖deriv R (((a : ℂ) + ε + y * I) + u)‖ * ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖
          ≤ B y₀ * 1 := mul_le_mul (hB y₀ ε hε_Icc y hy_ball u hu)
            (norm_pow_div_factorial_le_one hu.1.le hu.2) (norm_nonneg _) (hB0 y₀)
      _ = B y₀ := mul_one _
  have hint_le' : ‖∫ u : ℝ in (0 : ℝ)..1,
      deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)‖ ≤ B y₀ := by
    simpa using hint_le
  have hle_sum : B y₀ ≤ ∑ z ∈ t, B z :=
    Finset.single_le_sum (f := B) (fun z _ ↦ hB0 z) hy₀t
  exact hint_le'.trans hle_sum

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
  have hQ_mero : MeromorphicAt Q a := hf_an.meromorphicAt.div hd_an.meromorphicAt
  -- Since `f a = 0`, `1 ≤ meromorphicOrderAt f a`, hence `-(k : ℤ) ≤ meromorphicOrderAt Q a`.
  have hf_ord : (1 : WithTop ℤ) ≤ meromorphicOrderAt f a := by
    have hne0 : analyticOrderAt f a ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hf_an, sub_eq_zero.mpr hga⟩
    rw [hf_an.meromorphicOrderAt_eq]
    cases hord : analyticOrderAt f a with
    | top => exact le_top
    | coe n =>
      have hn : 1 ≤ n := Nat.pos_of_ne_zero fun h0 ↦ hne0 (by simp [hord, h0])
      exact WithTop.coe_le_coe.mpr (by exact_mod_cast hn)
  have hQ_ord : (-(k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Q a := by
    rw [meromorphicOrderAt_div hf_an.meromorphicAt hd_an.meromorphicAt]
    have hd_ord : meromorphicOrderAt d a = ((k + 1 : ℕ) : ℤ) := by
      change meromorphicOrderAt ((· - (a : ℂ)) ^ (k + 1)) (a : ℂ) = _
      rw [meromorphicOrderAt_pow_id_sub_const]
      norm_cast
    rw [hd_ord]
    cases hx : meromorphicOrderAt f a with
    | top => simp
    | coe n =>
      rw [hx] at hf_ord
      have hn1 : (1 : ℤ) ≤ n := WithTop.coe_le_coe.mp hf_ord
      rw [show (-(k : ℤ) : WithTop ℤ) = ((-(k : ℤ) : ℤ) : WithTop ℤ) by norm_cast,
        show (n : WithTop ℤ) - (((k + 1 : ℕ) : ℤ) : WithTop ℤ) =
          ((n - ((k + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) by norm_cast,
        WithTop.coe_le_coe]
      omega
  let m : ℕ := TauCeti.Contour.meromorphicPolarOrderAt Q a
  have hm_le : m ≤ k := by
    by_contra hlt
    have hpos : 0 < m := by omega
    have heq := TauCeti.Contour.meromorphicOrderAt_eq_neg_of_meromorphicPolarOrderAt_pos hpos
    rw [heq] at hQ_ord
    norm_cast at hQ_ord
    omega
  obtain ⟨c, q, hq_an, hQ_laur⟩ := TauCeti.Contour.exists_laurent_data_of_meromorphicAt hQ_mero
  obtain ⟨r_q, hr_q, hq_ball⟩ := hq_an.exists_ball_analyticOnNhd
  obtain ⟨r_e, hr_e, hlaur_ball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hQ_laur)
  let r₁ : ℝ := min r₀ (min r_q r_e)
  have hr₁ : 0 < r₁ := lt_min hr₀ (lt_min hr_q hr_e)
  have hsub₀ : ball (a : ℂ) r₁ ⊆ ball (a : ℂ) r₀ := ball_subset_ball (min_le_left _ _)
  have hsub_q : ball (a : ℂ) r₁ ⊆ ball (a : ℂ) r_q :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hsub_e : ball (a : ℂ) r₁ ⊆ ball (a : ℂ) r_e :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r₁, hr₁, m, hm_le, c, q, hq_ball.mono hsub_q, fun z hz hzre ↦ ?_⟩
  let L_fun : ℂ → ℂ := fun w ↦ q w + ∑ i : Fin m, c i / (w - a) ^ (i.val + 1)
  have hopen : IsOpen (ball (a : ℂ) r₁ ∩ {w : ℂ | a < w.re}) :=
    isOpen_ball.inter (isOpen_re_gt a)
  have hev : R =ᶠ[𝓝 z] L_fun := by
    refine eventuallyEq_of_mem (hopen.mem_nhds ⟨hz, hzre⟩) fun w ⟨hw, hwre⟩ ↦ ?_
    have hwa : w ≠ a := fun h0 ↦ by simp [h0] at hwre
    have hRw : R w = Q w := by
      simp only [R, Q, Pi.div_apply, f, d, hF w (hsub₀ hw) hwre, sub_div]
    exact hRw.trans (hlaur_ball w (hsub_e hw) hwa)
  rw [hev.deriv_eq]
  have hza : z - (a : ℂ) ≠ 0 := sub_ne_zero.mpr fun h0 ↦ by simp [h0] at hzre
  have h_sum_deriv : HasDerivAt (fun w : ℂ ↦ ∑ i : Fin m, c i / (w - a) ^ (i.val + 1))
      (∑ i : Fin m, c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2))) z := by
    have h_each : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        HasDerivAt (fun w : ℂ ↦ c i / (w - a) ^ (i.val + 1))
          (c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2))) z := by
      intro i _
      have hp : HasDerivAt (fun w : ℂ ↦ (w - a) ^ (i.val + 1))
          (((i.val + 1 : ℕ) : ℂ) * (z - a) ^ i.val) z := by
        simpa only [add_tsub_cancel_right, mul_one, id_eq] using
          HasDerivAt.fun_pow ((hasDerivAt_id z).sub_const (a : ℂ)) (i.val + 1)
      have hinv : HasDerivAt (fun w : ℂ ↦ ((w - a) ^ (i.val + 1))⁻¹)
          (-(((i.val + 1 : ℕ) : ℂ) * (z - a) ^ i.val) / ((z - a) ^ (i.val + 1)) ^ 2) z :=
        hp.inv (pow_ne_zero _ hza)
      have hmul : HasDerivAt (fun w : ℂ ↦ c i / (w - a) ^ (i.val + 1))
          (c i * (-(((i.val + 1 : ℕ) : ℂ) * (z - a) ^ i.val) /
            ((z - a) ^ (i.val + 1)) ^ 2)) z := by
        simpa [div_eq_mul_inv] using hinv.const_mul (c i)
      refine hmul.congr_deriv ?_
      congr 1
      have hsq : ((z - (a : ℂ)) ^ (i.val + 1)) ^ 2 =
          (z - a) ^ (i.val + 2) * (z - a) ^ i.val := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [hsq, neg_div, mul_div_mul_right _ _ (pow_ne_zero _ hza), ← neg_div]
    exact HasDerivAt.fun_sum h_each
  exact (((hq_ball _ (hsub_q hz)).differentiableAt.hasDerivAt).add h_sum_deriv).deriv

/-- Elementary norm lower bound `(u + |y|) / 2 ≤ ‖((ε + u : ℝ) : ℂ) + y * I‖` for `ε, u ≥ 0`. -/
private theorem half_add_abs_le_norm {ε u y : ℝ} (hε : 0 ≤ ε) (hu : 0 ≤ u) :
    (u + |y|) / 2 ≤ ‖((ε + u : ℝ) : ℂ) + y * I‖ := by
  let w : ℂ := ((ε + u : ℝ) : ℂ) + y * I
  have hre : u ≤ ‖w‖ := by
    have h1 : |w.re| ≤ ‖w‖ := abs_re_le_norm w
    have h2 : w.re = ε + u := by simp [w]
    rw [h2, abs_of_nonneg (by linarith)] at h1
    linarith
  have him : |y| ≤ ‖w‖ := by
    have h1 : |w.im| ≤ ‖w‖ := abs_im_le_norm w
    simpa [w] using h1
  linarith

/-- Logarithmic bound near the pole: there exist `δ ∈ (0, 1]` and constants `C₁, C₂ ≥ 0` such that
for all `ε ∈ (0, δ)` and all `y` with `0 < |y| ≤ δ`,
`‖H (a + ε + y * I)‖ ≤ C₁ + C₂ * |Real.log y|`. -/
private theorem exists_near_pole_log_bound {F : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (h : PoleBoundary F a k A) :
    let R := fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
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
  have hC₁0 : 0 ≤ C₁ := by
    have := Real.log_nonneg one_le_two
    positivity
  refine ⟨δ, hδ, hδ1, C₁, C_pole, hC₁0, hCp0, fun ε hε y hy0 hyδ ↦ ?_⟩
  let φ : ℝ → ℂ := fun u ↦
    deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
  have hφ_cont : ContinuousOn φ (Icc 0 1) := by
    refine (hR_cont.comp (by fun_prop) fun u hu ↦ ?_).mul (by fun_prop)
    change a < (((a : ℂ) + ε + y * I) + u).re
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    linarith [hε.1, hu.1]
  have hint_0δ : IntervalIntegrable φ volume 0 δ :=
    (hφ_cont.mono (Icc_subset_Icc_right hδ1)).intervalIntegrable_of_Icc hδ.le
  have hint_δ1 : IntervalIntegrable φ volume δ 1 :=
    (hφ_cont.mono (Icc_subset_Icc_left hδ.le)).intervalIntegrable_of_Icc hδ1
  rw [norm_neg, ← integral_add_adjacent_intervals hint_0δ hint_δ1]
  -- Bound the tail `[δ, 1]` by `B_tail`.
  have htail_le : ‖∫ u : ℝ in δ..1, φ u‖ ≤ B_tail := by
    have h1 : ‖∫ u : ℝ in δ..1, φ u‖ ≤ B_tail * |(1 : ℝ) - δ| := by
      refine norm_integral_le_of_norm_le_const fun u hu ↦ ?_
      rw [uIoc_of_le hδ1] at hu
      rw [norm_mul]
      have hy_Icc : y ∈ Icc (-δ) δ := abs_le.mp hyδ
      calc
        ‖deriv R (((a : ℂ) + ε + y * I) + u)‖ * ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖
            ≤ B_tail * 1 := mul_le_mul (hBt ε ⟨hε.1.le, hε.2.le⟩ y hy_Icc u ⟨hu.1.le, hu.2⟩)
              (norm_pow_div_factorial_le_one (hδ.trans hu.1).le hu.2) (norm_nonneg _) hBt0
        _ = B_tail := mul_one _
    have habs : |(1 : ℝ) - δ| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact h1.trans (mul_le_of_le_one_right hBt0 habs)
  -- Pointwise majorant on `(0, δ]` via the Laurent expansion at `a`.
  have hy_pos : 0 < |y| := abs_pos.mpr hy0
  have hmaj_int : IntervalIntegrable (fun u : ℝ ↦ max M_q 0 + C_pole * (u + |y|)⁻¹) volume 0 δ := by
    refine ContinuousOn.intervalIntegrable_of_Icc hδ.le ?_
    refine continuousOn_const.add (continuousOn_const.mul ((continuousOn_id.add
      continuousOn_const).inv₀ fun u hu h0 ↦ ?_))
    simp only [Pi.add_apply, id_eq] at h0
    linarith [hu.1]
  have hhead_le : ‖∫ u : ℝ in (0 : ℝ)..δ, φ u‖ ≤
      ∫ u : ℝ in (0 : ℝ)..δ, (max M_q 0 + C_pole * (u + |y|)⁻¹) := by
    refine norm_integral_le_of_norm_le hδ.le (.of_forall fun u ⟨hu0, huδ⟩ ↦ ?_) hmaj_int
    let z : ℂ := ((a : ℂ) + ε + y * I) + u
    have hz_sub : z - a = ((ε + u : ℝ) : ℂ) + y * I := by
      simp only [z]; push_cast; ring
    have hz_cb : z ∈ closedBall (a : ℂ) (r₁ / 2) := by
      rw [mem_closedBall, dist_eq_norm, hz_sub]
      have hδ_le : δ ≤ r₁ / 6 := min_le_right _ _
      calc
        ‖((ε + u : ℝ) : ℂ) + y * I‖ ≤ ‖((ε + u : ℝ) : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
        _ = ε + u + |y| := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [hε.1]), norm_mul,
            Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs]
        _ ≤ r₁ / 2 := by linarith [hε.2]
    have hz_re : a < z.re := by
      simp only [z, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero]
      linarith [hε.1]
    have hnorm_w : ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤ u ^ k := by
      have hfac : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact div_le_self (pow_nonneg hu0.le k) hfac
    have hnorm_w1 : ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ ≤ 1 :=
      norm_pow_div_factorial_le_one hu0.le (huδ.trans hδ1)
    have hd_eq := hderiv_laur z (closedBall_subset_ball (half_lt_self hr₁) hz_cb) hz_re
    simp only [φ, norm_mul]
    rw [show (((a : ℂ) + ε + y * I) + u) = z from rfl, hd_eq]
    calc
      ‖deriv q z + ∑ i : Fin m, c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2))‖ *
          ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖
          ≤ (‖deriv q z‖ +
              ∑ i : Fin m, ‖c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2))‖) *
            ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ := by
        gcongr
        exact (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
      _ = ‖deriv q z‖ * ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ +
          ∑ i : Fin m, ‖c i * (-((i.val + 1 : ℕ) : ℂ) / (z - a) ^ (i.val + 2))‖ *
            ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖ := by
        rw [add_mul, Finset.sum_mul]
      _ ≤ max M_q 0 + C_pole * (u + |y|)⁻¹ := by
        refine add_le_add ?_ ?_
        · calc
            ‖deriv q z‖ * ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖
                ≤ max M_q 0 * 1 := mul_le_mul ((hMq z hz_cb).trans (le_max_left _ _)) hnorm_w1
                  (norm_nonneg _) (le_max_right _ _)
            _ = max M_q 0 := mul_one _
        · rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hi_le : i.val + 1 ≤ k := Nat.succ_le_of_lt (i.isLt.trans_le hm_le)
          have hu_pow : u ^ k ≤ (u + |y|) ^ (i.val + 1) :=
            (pow_le_pow_of_le_one hu0.le (huδ.trans hδ1) hi_le).trans
              (pow_le_pow_left₀ hu0.le (by linarith) _)
          have hza_ge : (u + |y|) / 2 ≤ ‖z - a‖ := by
            rw [hz_sub]
            exact half_add_abs_le_norm hε.1.le hu0.le
          have ht_pos : 0 < u + |y| := by linarith
          have hpow_ge : ((u + |y|) / 2) ^ (i.val + 2) ≤ ‖z - a‖ ^ (i.val + 2) :=
            pow_le_pow_left₀ (by positivity) hza_ge _
          simp only [norm_mul, norm_div, norm_neg, Complex.norm_natCast, norm_pow]
          calc
            ‖c i‖ * (((i.val + 1 : ℕ) : ℝ) / ‖z - a‖ ^ (i.val + 2)) *
                ‖(((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ))‖
                ≤ ‖c i‖ * (((i.val + 1 : ℕ) : ℝ) / ((u + |y|) / 2) ^ (i.val + 2)) *
                  (u + |y|) ^ (i.val + 1) := by
              refine mul_le_mul ?_ (hnorm_w.trans hu_pow) (norm_nonneg _) (by positivity)
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpow_ge
            _ = ‖c i‖ * ((i.val + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (i.val + 2) * (u + |y|)⁻¹ := by
              rw [div_pow, div_div_eq_mul_div, pow_succ (u + |y|) (i.val + 1)]
              have ht_ne : u + |y| ≠ 0 := ht_pos.ne'
              have htp_ne : (u + |y|) ^ (i.val + 1) ≠ 0 := pow_ne_zero _ ht_ne
              push_cast
              field_simp
  -- Evaluate the elementary integral `∫ u in 0..δ, (max M_q 0 + C_pole * (u + |y|)⁻¹)`.
  have hinv_int : IntervalIntegrable (fun u : ℝ ↦ (u + |y|)⁻¹) volume 0 δ := by
    refine ContinuousOn.intervalIntegrable_of_Icc hδ.le
      ((continuousOn_id.add continuousOn_const).inv₀ fun u hu h0 ↦ ?_)
    simp only [Pi.add_apply, id_eq] at h0
    linarith [hu.1]
  have heval : ∫ u : ℝ in (0 : ℝ)..δ, (max M_q 0 + C_pole * (u + |y|)⁻¹) =
      max M_q 0 * δ + C_pole * Real.log ((δ + |y|) / |y|) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hinv_int.const_mul C_pole),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm δ,
      intervalIntegral.integral_const_mul, integral_comp_add_right (fun x : ℝ ↦ x⁻¹) |y|,
      zero_add, integral_inv_of_pos hy_pos (by positivity)]
  have hlog_le : Real.log ((δ + |y|) / |y|) ≤ Real.log 2 + |Real.log y| := by
    have hquot : (δ + |y|) / |y| ≤ 2 / |y| := by
      refine div_le_div_of_nonneg_right ?_ hy_pos.le
      linarith
    have h1 : Real.log ((δ + |y|) / |y|) ≤ Real.log (2 / |y|) :=
      Real.log_le_log (div_pos (by positivity) hy_pos) hquot
    rw [Real.log_div two_ne_zero hy_pos.ne', Real.log_abs] at h1
    linarith [neg_abs_le (Real.log y)]
  calc
    ‖(∫ u : ℝ in (0 : ℝ)..δ, φ u) + ∫ u : ℝ in δ..1, φ u‖
        ≤ ‖∫ u : ℝ in (0 : ℝ)..δ, φ u‖ + ‖∫ u : ℝ in δ..1, φ u‖ := norm_add_le _ _
    _ ≤ (max M_q 0 * δ + C_pole * Real.log ((δ + |y|) / |y|)) + B_tail :=
      add_le_add (heval ▸ hhead_le) htail_le
    _ ≤ (max M_q 0 * 1 + C_pole * (Real.log 2 + |Real.log y|)) + B_tail := by
      gcongr
    _ = C₁ + C_pole * |Real.log y| := by simp only [C₁]; ring

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
  let b : ℝ → ℂ := fun y ↦
    if y = 0 then 0
    else -∫ u : ℝ in (0 : ℝ)..1,
      deriv R (((a : ℂ) + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
  have hR_cont : ContinuousOn (deriv R) {s : ℂ | a < s.re} :=
    (analyticOnNhd_deriv_remainder h).continuousOn
  have h_ptwise : ∀ y : ℝ, y ≠ 0 →
      Tendsto (fun ε : ℝ ↦ H ((a : ℂ) + ε + y * I)) (𝓝[>] 0) (𝓝 (b y)) := by
    intro y hy
    obtain ⟨-, htend⟩ := exists_away_local_data h hy
    simpa [H, b, hy] using htend
  obtain ⟨δ, hδ, -, C₁, C₂, hC₁0, hC₂0, hnear⟩ := exists_near_pole_log_bound h
  refine ⟨b, fun L hL ↦ ?_⟩
  obtain ⟨ε_away, hε_away, B_away, hBa0, haway⟩ := exists_away_compact_bound h (L := L) hδ
  let ε₀ : ℝ := min δ ε_away
  have hε₀ : 0 < ε₀ := lt_min hδ hε_away
  let M : ℝ → ℝ := fun y ↦ (C₁ + B_away) + C₂ * |Real.log y|
  have hH_le : ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ y ∈ Icc (-L) L, y ≠ 0 →
      ‖H ((a : ℂ) + ε + y * I)‖ ≤ M y := by
    intro ε hε y hyL hy0
    by_cases hyδ : |y| ≤ δ
    · have h1 := hnear ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ y hy0 hyδ
      have hH_eq : H ((a : ℂ) + ε + y * I) = -∫ u : ℝ in (0 : ℝ)..1,
          deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := rfl
      rw [hH_eq]
      linarith
    · have hyδ' : δ < |y| := lt_of_not_ge hyδ
      have h2 := haway ε ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩ y hyL hyδ'.le
      have hH_eq : H ((a : ℂ) + ε + y * I) = -∫ u : ℝ in (0 : ℝ)..1,
          deriv R (((a : ℂ) + ε + y * I) + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := rfl
      rw [hH_eq]
      have hlog_nn : 0 ≤ C₂ * |Real.log y| := mul_nonneg hC₂0 (abs_nonneg _)
      linarith
  have hM_int : IntegrableOn M (Icc (-L) L) := by
    have hlog_int : IntegrableOn (fun y : ℝ ↦ |Real.log y|) (Icc (-L) L) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
        intervalIntegrable_log'.abs
    exact (integrableOn_const (hs := measure_Icc_lt_top.ne)).add (hlog_int.const_mul C₂)
  have hae_ne : ∀ᵐ y ∂volume.restrict (Icc (-L) L), y ∈ Icc (-L) L ∧ y ≠ 0 := by
    refine Filter.Eventually.and (ae_restrict_mem measurableSet_Icc) ?_
    refine ae_restrict_of_ae (mem_ae_iff.mpr ?_)
    have hcompl : {y : ℝ | y ≠ 0}ᶜ = ({0} : Set ℝ) := by ext y; simp
    rw [hcompl, measure_singleton]
  -- Establish `AEStronglyMeasurable b` via the sequence `ε_n = 1 / (n + 1) → 0⁺`.
  have hb_meas : AEStronglyMeasurable b (volume.restrict (Icc (-L) L)) := by
    let ε_seq : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
    have hseq_pos : ∀ n : ℕ, 0 < ε_seq n := fun n ↦ by positivity
    have hseq_tend : Tendsto ε_seq atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        tendsto_one_div_add_atTop_nhds_zero_nat (.of_forall hseq_pos)
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) (y : ℝ) ↦ H ((a : ℂ) + ε_seq n + y * I))
      (fun n ↦ (continuous_regularized_of_pos (k := k) hR_cont (hseq_pos n)).aestronglyMeasurable)
      ?_
    filter_upwards [hae_ne] with y hy
    exact (h_ptwise y hy.2).comp hseq_tend
  have hb_le : ∀ᵐ y ∂volume.restrict (Icc (-L) L), ‖b y‖ ≤ M y := by
    filter_upwards [hae_ne] with y hy
    refine le_of_tendsto (h_ptwise y hy.2).norm ?_
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    exact hH_le ε hε y hy.1 hy.2
  have hb_int : IntegrableOn b (Icc (-L) L) := hM_int.mono' hb_meas hb_le
  refine ⟨hb_int, ?_⟩
  -- Apply dominated convergence on `Icc (-L) L` as `ε → 0⁺` with majorant `M y + ‖b y‖`.
  rw [show (𝓝 (0 : ℝ)) = 𝓝 (∫ _ : ℝ in Icc (-L) L, (0 : ℝ)) by
    rw [MeasureTheory.integral_zero]]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc (-L) L)) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε y ↦ ‖H ((a : ℂ) + ε + y * I) - b y‖) (f := fun _ ↦ (0 : ℝ))
    (fun y ↦ M y + ‖b y‖) ?_ ?_ (hM_int.add hb_int.norm) ?_
  · filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    exact ((continuous_regularized_of_pos (k := k) hR_cont hε.1).aestronglyMeasurable.sub
      hb_int.aestronglyMeasurable).norm
  · filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    filter_upwards [hae_ne] with y hy
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by gcongr; exact hH_le ε hε y hy.1 hy.2)
  · filter_upwards [hae_ne] with y hy
    simpa using ((h_ptwise y hy.2).sub_const (b y)).norm

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
`0` on `Re s > a`), yet `PoleBoundary` and the vanishing of the regularised integral on `Re s ≥ a`
continue to hold. -/
theorem not_continuousAt_remainder_update_pole (a A : ℝ) (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    let F := Function.update (fun s : ℂ ↦ (A : ℂ) / (s - a) ^ (k + 1)) (a : ℂ) w
    let R := fun s : ℂ ↦ F s - (A : ℂ) / (s - a) ^ (k + 1)
    PoleBoundary F a k A ∧ ¬ ContinuousAt R a ∧
      ∀ s : ℂ, a ≤ s.re →
        -∫ u : ℝ in (0 : ℝ)..1,
          deriv R (s + u) * ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ) = 0 := by
  intro F R
  have hF_re : ∀ s : ℂ, a < s.re → F s = (A : ℂ) / (s - a) ^ (k + 1) := by
    intro s hs
    have hsa : s ≠ (a : ℂ) := fun h0 ↦ by simp [h0] at hs
    simp [F, Function.update_of_ne hsa]
  refine ⟨(poleBoundary_div_sub_pow a A k).update_of_re_le (by simp) w, ?_,
    fun s hs ↦ regularizedRemainder_eq_zero_of_eq_on_re_gt hF_re hs⟩
  intro hcont
  have hRa : R a = w := by simp [R, F, zero_pow (Nat.succ_ne_zero k)]
  have htend0 : Tendsto (fun ε : ℝ ↦ R ((a : ℂ) + ε)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hre : a < ((a : ℂ) + ε).re := by simp [hε]
    exact (sub_eq_zero.mpr (hF_re _ hre)).symm
  have htendw : Tendsto (fun ε : ℝ ↦ R ((a : ℂ) + ε)) (𝓝[>] 0) (𝓝 w) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ R ((a : ℂ) + ε)) 0 :=
      hcont.comp_of_eq (continuousAt_const.add Complex.continuous_ofReal.continuousAt) (by simp)
    simpa [hRa] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  exact hw (tendsto_nhds_unique htendw htend0)

end TauCeti.HigherPoleTauberian
