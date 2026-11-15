/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Boundary continuation on a vertical line with a pole of integer order

This file defines the boundary-continuation predicate `TauCeti.HigherPoleTauberian.PoleBoundary`
underlying the integer-order case of Delange's Tauberian theorem for Laplace transforms and
Dirichlet series, and develops its uniqueness, algebraic, scaling, and concrete L-series API.

Given `F : ℂ → ℂ`, an abscissa `a : ℝ`, a natural number `k : ℕ`, and a real leading coefficient
`A : ℝ`, `PoleBoundary F a k A` asserts that:
1. `F` is holomorphic on the open right half-plane `{s | a < s.re}`;
2. on a disc around `a`, `F` agrees on `{s | a < s.re}` with `g s / (s - a) ^ (k + 1)` for a
   holomorphic numerator `g` satisfying `g a = A`; and
3. around every other point `a + i y` (`y ≠ 0`) of the vertical line `Re s = a`, `F` agrees on
   `{s | a < s.re}` with a holomorphic germ.

All agreements with `F` are restricted to the open half-plane `Re s > a`, so arbitrary totalised
values on `Re s ≤ a` (such as `0` for a non-convergent `LSeries` or a redefined value at the pole)
never affect `PoleBoundary`. When `A ≠ 0`, the pole at `a` has exact order `k + 1`; `A = 0` records
a pole of order at most `k` (including analyticity across `a` when `k = 0`).

## Main definitions and results

* `TauCeti.HigherPoleTauberian.PoleBoundary`: holomorphic continuation across `Re s = a` with a
  pole of order `k + 1` and real leading coefficient `A` at `a`.
* Half-plane invariance: `PoleBoundary.congr`, `poleBoundary_congr`,
  `PoleBoundary.update_of_re_le`, and `poleBoundary_update_iff_of_re_le`.
* Uniqueness and order comparison: `PoleBoundary.unique` (uniqueness of `A` at fixed `k`),
  `PoleBoundary.eq_zero_of_lt`, `PoleBoundary.of_lt`, `PoleBoundary.order_unique` (uniqueness of
  `k` when leading coefficients are nonzero), and `poleBoundary_zero_iff`.
* Algebraic and analytic closure: `PoleBoundary.const_mul`, `PoleBoundary.neg`, `PoleBoundary.add`,
  `PoleBoundary.sub`, `PoleBoundary.comp_mul_left` and `PoleBoundary.comp_mul_self` (rescaling
  `s ↦ c * s` for `0 < c`, and rescaling `a` to `1`), `PoleBoundary.comp_add_right` (horizontal
  translation), `PoleBoundary.mul_analytic` and `PoleBoundary.analytic_mul` (multiplication by a
  function analytic on `Re s ≥ a` with real value at `a`), `PoleBoundary.div_id` (division by `s`
  for `0 < a`, dividing `A` by `a`), `PoleBoundary.mul` (products add pole orders),
  `PoleBoundary.pow_succ`, and `PoleBoundary.pow_succ_of_zero`.
* Analytic functions, model poles, and Riemann zeta: `poleBoundary_of_analyticOnNhd`,
  `poleBoundary_zero`, `poleBoundary_div_sub_pow`, `poleBoundary_div_sub_pow_iff`,
  `poleBoundary_riemannZeta`, and `poleBoundary_riemannZeta_pow`.
* Necessity of off-real continuation: `analyticOnNhd_inv_one_sub_cexp_log_two`,
  `exists_pole_germ_inv_one_sub_cexp_log_two`, and `not_poleBoundary_inv_one_sub_cexp_log_two`,
  showing that `(1 - exp ((1 - s) log 2))⁻¹` is holomorphic on `Re s > 1` with a simple pole of
  residue `(log 2)⁻¹` at `1`, yet satisfies no `PoleBoundary` at `1` because of its periodic poles
  at `1 + 2πi / log 2`.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242 (§5.2.1, Theorem III, pp. 235–238; §5.3, p. 242).
-/

public section

open Complex Filter Metric Set
open scoped Topology

namespace TauCeti.HigherPoleTauberian

/-- `PoleBoundary F a k A` states that `F` is holomorphic on the open half-plane `Re s > a`,
agrees near `a` on `Re s > a` with `g s / (s - a) ^ (k + 1)` for a function `g` holomorphic on a
disc about `a` with `g a = A`, and extends holomorphically from `Re s > a` across every point
`a + i y` (`y ≠ 0`) of the boundary line `Re s = a`.

All agreements are asserted only on `Re s > a`, so the values of `F` on `Re s ≤ a` are irrelevant.
When `A ≠ 0` the pole at `a` has exact order `k + 1`; when `A = 0` the pole has order at most `k`.
This is the integer-order boundary hypothesis of Delange (1954), Theorem III (§5.2.1,
pp. 235–236). -/
structure PoleBoundary (F : ℂ → ℂ) (a : ℝ) (k : ℕ) (A : ℝ) : Prop where
  /-- `F` is holomorphic on the open right half-plane `Re s > a`. -/
  interior : AnalyticOnNhd ℂ F {s : ℂ | a < s.re}
  /-- Near `a`, `F` is a holomorphic numerator with value `A` at `a` divided by
  `(s - a) ^ (k + 1)` on `Re s > a`. -/
  pole : ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball (a : ℂ) r) ∧
    g a = A ∧ ∀ s ∈ ball (a : ℂ) r, a < s.re → F s = g s / (s - a) ^ (k + 1)
  /-- `F` extends holomorphically across every point `a + i y` (`y ≠ 0`) of the line `Re s = a`. -/
  away : ∀ y : ℝ, y ≠ 0 → ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g (ball ((a : ℂ) + y * I) r) ∧
      ∀ s ∈ ball ((a : ℂ) + y * I) r, a < s.re → F s = g s

namespace PoleBoundary

variable {F G : ℂ → ℂ} {a A B : ℝ} {k l : ℕ}

/-- At every point `s` of the open right half-plane `Re s > a`, `F` is analytic. -/
theorem analyticAt (h : PoleBoundary F a k A) {s : ℂ} (hs : a < s.re) : AnalyticAt ℂ F s :=
  h.interior s hs

/-- On the open right half-plane `Re s > a`, `F` is complex differentiable. -/
theorem differentiableOn_re_gt (h : PoleBoundary F a k A) :
    DifferentiableOn ℂ F {s : ℂ | a < s.re} :=
  h.interior.differentiableOn

/-! ### Agreement on the open half-plane -/

/-- `PoleBoundary` depends on `F` only through its restriction to the open half-plane `Re s > a`. -/
theorem congr (h : PoleBoundary F a k A) (hFG : ∀ s : ℂ, a < s.re → F s = G s) :
    PoleBoundary G a k A where
  interior s hs :=
    (h.interior s hs).congr (eventuallyEq_of_mem ((isOpen_re_gt a).mem_nhds hs) hFG)
  pole := by
    obtain ⟨r, hr, g, hg, hga, hF⟩ := h.pole
    exact ⟨r, hr, g, hg, hga, fun s hs hsre ↦ (hFG s hsre).symm.trans (hF s hs hsre)⟩
  away y hy := by
    obtain ⟨r, hr, g, hg, hF⟩ := h.away y hy
    exact ⟨r, hr, g, hg, fun s hs hsre ↦ (hFG s hsre).symm.trans (hF s hs hsre)⟩

/-- Modifying `F` at a point `z` with `Re z ≤ a` preserves `PoleBoundary`. -/
theorem update_of_re_le (h : PoleBoundary F a k A) {z : ℂ} (hz : z.re ≤ a) (w : ℂ) :
    PoleBoundary (Function.update F z w) a k A :=
  h.congr fun s hs ↦ by
    rw [Function.update_of_ne]
    rintro rfl
    exact lt_irrefl _ (hs.trans_le hz)

/-! ### Uniqueness of leading coefficient and pole order -/

/-- Two analytic functions on `ball z₀ r` (`z₀.re = a`, `0 < r`) that agree on the right half-ball
`{s ∈ ball z₀ r | a < s.re}` agree throughout `ball z₀ r`, in particular at `z₀`. -/
private theorem eq_center_of_eq_on_re_gt {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hz₀ : a ≤ z₀.re)
    {g₁ g₂ : ℂ → ℂ} (hg₁ : AnalyticOnNhd ℂ g₁ (ball z₀ r))
    (hg₂ : AnalyticOnNhd ℂ g₂ (ball z₀ r))
    (heq : ∀ s ∈ ball z₀ r, a < s.re → g₁ s = g₂ s) :
    g₁ z₀ = g₂ z₀ := by
  let w₀ : ℂ := z₀ + ((r / 2 : ℝ) : ℂ)
  have hw₀_ball : w₀ ∈ ball z₀ r := by
    simp [w₀, dist_eq_norm, abs_of_pos hr, half_lt_self hr]
  have hw₀_re : a < w₀.re := by
    simp only [w₀, add_re, ofReal_re]
    linarith
  have hopen : IsOpen (ball z₀ r ∩ {s : ℂ | a < s.re}) :=
    isOpen_ball.inter (isOpen_re_gt a)
  have hev : g₁ =ᶠ[𝓝 w₀] g₂ :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨ball z₀ r ∩ {s : ℂ | a < s.re}, hopen.mem_nhds ⟨hw₀_ball, hw₀_re⟩,
        fun s hs ↦ heq s hs.1 hs.2⟩
  exact hg₁.eqOn_of_preconnected_of_eventuallyEq hg₂ (convex_ball z₀ r).isPreconnected
    hw₀_ball hev (mem_ball_self hr)

/-- At a fixed pole order `k + 1`, the leading coefficient `A` in `PoleBoundary F a k A` is
uniquely determined. -/
theorem unique (hA : PoleBoundary F a k A) (hB : PoleBoundary F a k B) : A = B := by
  obtain ⟨r₁, hr₁, g₁, hg₁, hga₁, hF₁⟩ := hA.pole
  obtain ⟨r₂, hr₂, g₂, hg₂, hga₂, hF₂⟩ := hB.pole
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hsub₁ : ball (a : ℂ) r ⊆ ball (a : ℂ) r₁ := ball_subset_ball (min_le_left _ _)
  have hsub₂ : ball (a : ℂ) r ⊆ ball (a : ℂ) r₂ := ball_subset_ball (min_le_right _ _)
  have hcenter : g₁ a = g₂ a :=
    eq_center_of_eq_on_re_gt (a := a) hr (by simp) (hg₁.mono hsub₁) (hg₂.mono hsub₂)
      fun s hs hsre ↦ by
        have hsa : (s - a) ^ (k + 1) ≠ 0 :=
          pow_ne_zero _ (sub_ne_zero.mpr fun h ↦ by simp [h] at hsre)
        have hdiv : g₁ s / (s - a) ^ (k + 1) = g₂ s / (s - a) ^ (k + 1) :=
          (hF₁ s (hsub₁ hs) hsre).symm.trans (hF₂ s (hsub₂ hs) hsre)
        exact (div_left_inj₀ hsa).mp hdiv
  exact Complex.ofReal_injective (hga₁.symm.trans (hcenter.trans hga₂))

/-- If `F` satisfies `PoleBoundary F a k A` and `PoleBoundary F a l B` with `k < l`, then the
higher-order numerator vanishes at `a`: `B = 0`. -/
theorem eq_zero_of_lt (hk : PoleBoundary F a k A) (hl : PoleBoundary F a l B) (hkl : k < l) :
    B = 0 := by
  obtain ⟨r₁, hr₁, g₁, hg₁, -, hF₁⟩ := hk.pole
  obtain ⟨r₂, hr₂, g₂, hg₂, hga₂, hF₂⟩ := hl.pole
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hsub₁ : ball (a : ℂ) r ⊆ ball (a : ℂ) r₁ := ball_subset_ball (min_le_left _ _)
  have hsub₂ : ball (a : ℂ) r ⊆ ball (a : ℂ) r₂ := ball_subset_ball (min_le_right _ _)
  have hg₁_mul : AnalyticOnNhd ℂ (fun s ↦ g₁ s * (s - a) ^ (l - k)) (ball (a : ℂ) r) :=
    (hg₁.mono hsub₁).mul ((analyticOnNhd_id.sub analyticOnNhd_const).pow _)
  have hcenter : g₁ a * ((a : ℂ) - a) ^ (l - k) = g₂ a :=
    eq_center_of_eq_on_re_gt (a := a) hr (by simp) hg₁_mul (hg₂.mono hsub₂) fun s hs hsre ↦ by
      have hsa : s - (a : ℂ) ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [h] at hsre
      have hsa_k : (s - (a : ℂ)) ^ (k + 1) ≠ 0 := pow_ne_zero _ hsa
      have hsa_l : (s - (a : ℂ)) ^ (l + 1) ≠ 0 := pow_ne_zero _ hsa
      have heq : g₁ s / (s - a) ^ (k + 1) = g₂ s / (s - a) ^ (l + 1) :=
        (hF₁ s (hsub₁ hs) hsre).symm.trans (hF₂ s (hsub₂ hs) hsre)
      have hexp : (k + 1) + (l - k) = l + 1 := by omega
      calc
        g₁ s * (s - a) ^ (l - k)
            = g₁ s / (s - a) ^ (k + 1) * ((s - a) ^ (k + 1) * (s - a) ^ (l - k)) := by
          rw [← mul_assoc, div_mul_cancel₀ _ hsa_k]
        _ = g₂ s / (s - a) ^ (l + 1) * (s - a) ^ (l + 1) := by
          rw [heq, ← pow_add, hexp]
        _ = g₂ s := div_mul_cancel₀ _ hsa_l
  have hzero : ((a : ℂ) - a) ^ (l - k) = 0 := by
    rw [sub_self, zero_pow (by omega)]
  rw [hzero, mul_zero, hga₂] at hcenter
  exact Complex.ofReal_injective hcenter.symm

/-- A pole of order at most `k + 1` is also a pole of order at most `l + 1` with leading
coefficient `0` whenever `k < l`. -/
theorem of_lt (h : PoleBoundary F a k A) (hkl : k < l) : PoleBoundary F a l 0 where
  interior := h.interior
  pole := by
    obtain ⟨r, hr, g, hg, -, hF⟩ := h.pole
    refine ⟨r, hr, fun s ↦ g s * (s - a) ^ (l - k),
      hg.mul ((analyticOnNhd_id.sub analyticOnNhd_const).pow _), ?_, fun s hs hsre ↦ ?_⟩
    · simp [zero_pow (show l - k ≠ 0 by omega)]
    · have hsa : s - (a : ℂ) ≠ 0 := sub_ne_zero.mpr fun hs' ↦ by simp [hs'] at hsre
      have hexp : l + 1 = (k + 1) + (l - k) := by omega
      dsimp only
      rw [hF s hs hsre, hexp, pow_add _ (k + 1) (l - k),
        mul_div_mul_right _ _ (pow_ne_zero _ hsa)]
  away := h.away

/-- When the leading coefficients `A` and `B` are both nonzero, the pole order parameter `k` in
`PoleBoundary F a k A` is uniquely determined. -/
theorem order_unique (hk : PoleBoundary F a k A) (hl : PoleBoundary F a l B)
    (hA : A ≠ 0) (hB : B ≠ 0) : k = l := by
  rcases lt_trichotomy k l with hlt | rfl | hgt
  · exact absurd (hk.eq_zero_of_lt hl hlt) hB
  · rfl
  · exact absurd (hl.eq_zero_of_lt hk hgt) hA

/-! ### Algebraic and scaling operations -/

/-- Multiplying `F` by a real constant `c` scales the leading coefficient by `c`. -/
theorem const_mul (h : PoleBoundary F a k A) (c : ℝ) :
    PoleBoundary (fun s ↦ (c : ℂ) * F s) a k (c * A) where
  interior := analyticOnNhd_const.mul h.interior
  pole := by
    obtain ⟨r, hr, g, hg, hga, hF⟩ := h.pole
    refine ⟨r, hr, fun s ↦ (c : ℂ) * g s, analyticOnNhd_const.mul hg, by simp [hga],
      fun s hs hsre ↦ ?_⟩
    rw [hF s hs hsre, mul_div_assoc]
  away y hy := by
    obtain ⟨r, hr, g, hg, hF⟩ := h.away y hy
    exact ⟨r, hr, fun s ↦ (c : ℂ) * g s, analyticOnNhd_const.mul hg,
      fun s hs hsre ↦ by rw [hF s hs hsre]⟩

/-- Negating `F` negates the leading coefficient. -/
theorem neg (h : PoleBoundary F a k A) : PoleBoundary (fun s ↦ -F s) a k (-A) := by
  simpa using h.const_mul (-1)

/-- Adding two functions with `PoleBoundary` at the same `(a, k)` adds their leading
coefficients. -/
theorem add (hF : PoleBoundary F a k A) (hG : PoleBoundary G a k B) :
    PoleBoundary (fun s ↦ F s + G s) a k (A + B) where
  interior := hF.interior.add hG.interior
  pole := by
    obtain ⟨r₁, hr₁, g₁, hg₁, hga₁, hF₁⟩ := hF.pole
    obtain ⟨r₂, hr₂, g₂, hg₂, hga₂, hG₂⟩ := hG.pole
    let r := min r₁ r₂
    have hsub₁ : ball (a : ℂ) r ⊆ ball (a : ℂ) r₁ := ball_subset_ball (min_le_left _ _)
    have hsub₂ : ball (a : ℂ) r ⊆ ball (a : ℂ) r₂ := ball_subset_ball (min_le_right _ _)
    refine ⟨r, lt_min hr₁ hr₂, fun s ↦ g₁ s + g₂ s, (hg₁.mono hsub₁).add (hg₂.mono hsub₂),
      by simp [hga₁, hga₂], fun s hs hsre ↦ ?_⟩
    rw [hF₁ s (hsub₁ hs) hsre, hG₂ s (hsub₂ hs) hsre, add_div]
  away y hy := by
    obtain ⟨r₁, hr₁, g₁, hg₁, hF₁⟩ := hF.away y hy
    obtain ⟨r₂, hr₂, g₂, hg₂, hG₂⟩ := hG.away y hy
    let r := min r₁ r₂
    have hsub₁ : ball ((a : ℂ) + y * I) r ⊆ ball ((a : ℂ) + y * I) r₁ :=
      ball_subset_ball (min_le_left _ _)
    have hsub₂ : ball ((a : ℂ) + y * I) r ⊆ ball ((a : ℂ) + y * I) r₂ :=
      ball_subset_ball (min_le_right _ _)
    exact ⟨r, lt_min hr₁ hr₂, fun s ↦ g₁ s + g₂ s, (hg₁.mono hsub₁).add (hg₂.mono hsub₂),
      fun s hs hsre ↦ by rw [hF₁ s (hsub₁ hs) hsre, hG₂ s (hsub₂ hs) hsre]⟩

/-- Subtracting two functions with `PoleBoundary` at the same `(a, k)` subtracts their leading
coefficients. -/
theorem sub (hF : PoleBoundary F a k A) (hG : PoleBoundary G a k B) :
    PoleBoundary (fun s ↦ F s - G s) a k (A - B) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

/-- Rescaling `s ↦ F (c * s)` by any positive real factor `c > 0` divides the abscissa by `c` and
divides the leading coefficient by `c ^ (k + 1)`. -/
theorem comp_mul_left (h : PoleBoundary F a k A) {c : ℝ} (hc : 0 < c) :
    PoleBoundary (fun s ↦ F (c * s)) (a / c) k (A / c ^ (k + 1)) where
  interior s hs := by
    have hre : a < ((c : ℂ) * s).re := by
      have hs' : a < s.re * c := (div_lt_iff₀ hc).mp hs
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      linarith
    exact (h.interior _ hre).fun_comp_of_eq (analyticAt_const.mul analyticAt_id) rfl
  pole := by
    obtain ⟨r, hr, g, hg, hga, hF⟩ := h.pole
    have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hball : ∀ s ∈ ball ((a / c : ℝ) : ℂ) (r / c), (c : ℂ) * s ∈ ball (a : ℂ) r := by
      intro s hs
      rw [mem_ball, dist_eq_norm] at hs ⊢
      have hmul : (c : ℂ) * s - a = c * (s - ((a / c : ℝ) : ℂ)) := by
        push_cast
        field_simp
      rw [hmul, norm_mul, norm_real, Real.norm_of_nonneg hc.le]
      exact (lt_div_iff₀' hc).mp hs
    have hg_inner : AnalyticOnNhd ℂ (fun s ↦ g ((c : ℂ) * s))
        (ball ((a / c : ℝ) : ℂ) (r / c)) :=
      fun s hs ↦ (hg _ (hball s hs)).fun_comp_of_eq (analyticAt_const.mul analyticAt_id) rfl
    have hg_comp : AnalyticOnNhd ℂ (fun s ↦ g ((c : ℂ) * s) / (c : ℂ) ^ (k + 1))
        (ball ((a / c : ℝ) : ℂ) (r / c)) :=
      hg_inner.div analyticOnNhd_const fun _ _ ↦ pow_ne_zero _ hc0
    refine ⟨r / c, div_pos hr hc, _, hg_comp, ?_, fun s hs hsre ↦ ?_⟩
    · rw [Complex.ofReal_div, mul_div_cancel₀ _ hc0, hga, Complex.ofReal_div, Complex.ofReal_pow]
    · have hre : a < ((c : ℂ) * s).re := by
        have hs' : a < s.re * c := (div_lt_iff₀ hc).mp hsre
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
        linarith
      rw [hF _ (hball s hs) hre, div_div, ← mul_pow]
      congr 2
      push_cast
      field_simp
  away y hy := by
    have hcy : c * y ≠ 0 := mul_ne_zero hc.ne' hy
    obtain ⟨r, hr, g, hg, hF⟩ := h.away (c * y) hcy
    have hball : ∀ s ∈ ball (((a / c : ℝ) : ℂ) + y * I) (r / c),
        (c : ℂ) * s ∈ ball ((a : ℂ) + (c * y : ℝ) * I) r := by
      intro s hs
      rw [mem_ball, dist_eq_norm] at hs ⊢
      have hmul : (c : ℂ) * s - ((a : ℂ) + (c * y : ℝ) * I) =
          c * (s - (((a / c : ℝ) : ℂ) + y * I)) := by
        have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
        push_cast
        field_simp
      rw [hmul, norm_mul, norm_real, Real.norm_of_nonneg hc.le]
      exact (lt_div_iff₀' hc).mp hs
    refine ⟨r / c, div_pos hr hc, fun s ↦ g ((c : ℂ) * s),
      fun s hs ↦ (hg _ (hball s hs)).fun_comp_of_eq (analyticAt_const.mul analyticAt_id) rfl,
      fun s hs hsre ↦ ?_⟩
    have hre : a < ((c : ℂ) * s).re := by
      have hs' : a < s.re * c := (div_lt_iff₀ hc).mp hsre
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      linarith
    exact hF _ (hball s hs) hre

/-- Rescaling `s ↦ F (a * s)` for `0 < a` moves the boundary line from `a` to `1` and divides the
leading coefficient by `a ^ (k + 1)`. -/
theorem comp_mul_self (h : PoleBoundary F a k A) (ha : 0 < a) :
    PoleBoundary (fun s ↦ F (a * s)) 1 k (A / a ^ (k + 1)) := by
  simpa [div_self ha.ne'] using h.comp_mul_left ha

/-- Horizontal translation `s ↦ F (s + c)` for real `c` shifts the abscissa from `a` to `a - c`
without changing the pole order or leading coefficient. -/
theorem comp_add_right (h : PoleBoundary F a k A) (c : ℝ) :
    PoleBoundary (fun s ↦ F (s + c)) (a - c) k A where
  interior s hs := by
    have hre : a < (s + c).re := by
      have hs' : a - c < s.re := hs
      simp only [add_re, ofReal_re]
      linarith
    exact (h.interior _ hre).fun_comp_of_eq (analyticAt_id.add analyticAt_const) rfl
  pole := by
    obtain ⟨r, hr, g, hg, hga, hF⟩ := h.pole
    have hball : ∀ s ∈ ball ((a - c : ℝ) : ℂ) r, s + c ∈ ball (a : ℂ) r := by
      intro s hs
      rw [mem_ball, dist_eq_norm] at hs ⊢
      convert hs using 2
      push_cast
      ring
    refine ⟨r, hr, fun s ↦ g (s + c),
      fun s hs ↦ (hg _ (hball s hs)).fun_comp_of_eq (analyticAt_id.add analyticAt_const) rfl,
      by simpa [sub_add_cancel] using hga, fun s hs hsre ↦ ?_⟩
    have hre : a < (s + c).re := by
      simp only [add_re, ofReal_re]
      linarith
    rw [hF _ (hball s hs) hre]
    congr 2
    push_cast
    ring
  away y hy := by
    obtain ⟨r, hr, g, hg, hF⟩ := h.away y hy
    have hball : ∀ s ∈ ball (((a - c : ℝ) : ℂ) + y * I) r,
        s + c ∈ ball ((a : ℂ) + y * I) r := by
      intro s hs
      rw [mem_ball, dist_eq_norm] at hs ⊢
      convert hs using 2
      push_cast
      ring
    refine ⟨r, hr, fun s ↦ g (s + c),
      fun s hs ↦ (hg _ (hball s hs)).fun_comp_of_eq (analyticAt_id.add analyticAt_const) rfl,
      fun s hs hsre ↦ ?_⟩
    have hre : a < (s + c).re := by
      simp only [add_re, ofReal_re]
      linarith
    exact hF _ (hball s hs) hre

/-- Multiplying `F` on the right by a function `H` analytic at every point of the closed half-plane
`Re s ≥ a` with real value `H a = C` preserves the pole order `k + 1` and multiplies the leading
coefficient by `C`. -/
theorem mul_analytic (h : PoleBoundary F a k A) {H : ℂ → ℂ} {C : ℝ}
    (hH : AnalyticOnNhd ℂ H {s : ℂ | a ≤ s.re}) (hHa : H a = C) :
    PoleBoundary (fun s ↦ F s * H s) a k (A * C) where
  interior := h.interior.mul (hH.mono fun _ (hs : a < _) ↦ hs.le)
  pole := by
    obtain ⟨r₁, hr₁, g, hg, hga, hF⟩ := h.pole
    obtain ⟨r₂, hr₂, hH_ball⟩ := (hH a (by simp)).exists_ball_analyticOnNhd
    let r := min r₁ r₂
    have hsub₁ : ball (a : ℂ) r ⊆ ball (a : ℂ) r₁ := ball_subset_ball (min_le_left _ _)
    have hsub₂ : ball (a : ℂ) r ⊆ ball (a : ℂ) r₂ := ball_subset_ball (min_le_right _ _)
    refine ⟨r, lt_min hr₁ hr₂, fun s ↦ g s * H s, (hg.mono hsub₁).mul (hH_ball.mono hsub₂),
      by simp [hga, hHa], fun s hs hsre ↦ ?_⟩
    rw [hF s (hsub₁ hs) hsre, div_mul_eq_mul_div]
  away y hy := by
    obtain ⟨r₁, hr₁, g, hg, hF⟩ := h.away y hy
    have hz : ((a : ℂ) + y * I) ∈ {s : ℂ | a ≤ s.re} := by simp
    obtain ⟨r₂, hr₂, hH_ball⟩ := (hH _ hz).exists_ball_analyticOnNhd
    let r := min r₁ r₂
    have hsub₁ : ball ((a : ℂ) + y * I) r ⊆ ball ((a : ℂ) + y * I) r₁ :=
      ball_subset_ball (min_le_left _ _)
    have hsub₂ : ball ((a : ℂ) + y * I) r ⊆ ball ((a : ℂ) + y * I) r₂ :=
      ball_subset_ball (min_le_right _ _)
    exact ⟨r, lt_min hr₁ hr₂, fun s ↦ g s * H s, (hg.mono hsub₁).mul (hH_ball.mono hsub₂),
      fun s hs hsre ↦ by rw [hF s (hsub₁ hs) hsre]⟩

/-- Multiplying `F` on the left by a function `H` analytic at every point of `Re s ≥ a` with real
value `H a = C` multiplies the leading coefficient by `C`. -/
theorem analytic_mul (h : PoleBoundary F a k A) {H : ℂ → ℂ} {C : ℝ}
    (hH : AnalyticOnNhd ℂ H {s : ℂ | a ≤ s.re}) (hHa : H a = C) :
    PoleBoundary (fun s ↦ H s * F s) a k (C * A) := by
  rw [mul_comm C A]
  exact (h.mul_analytic hH hHa).congr fun s _ ↦ mul_comm (F s) (H s)

/-- Dividing `F` by `s` at a positive abscissa `a > 0` preserves the pole order `k + 1` and divides
the leading coefficient by `a`. -/
theorem div_id (h : PoleBoundary F a k A) (ha : 0 < a) :
    PoleBoundary (fun s ↦ F s / s) a k (A / a) := by
  have hinv : AnalyticOnNhd ℂ (fun s : ℂ ↦ s⁻¹) {s : ℂ | a ≤ s.re} :=
    analyticOnNhd_id.inv fun s (hs : a ≤ s.re) h0 ↦ by simp [h0] at hs; linarith
  simpa [div_eq_mul_inv] using h.mul_analytic hinv (C := a⁻¹) (by simp)

/-- **Product rule for `PoleBoundary`.** Multiplying poles of orders `k + 1` and `l + 1` on the
same boundary line `Re s = a` produces a pole of order `(k + l + 1) + 1 = k + l + 2` with leading
coefficient `A * B`. -/
theorem mul (hF : PoleBoundary F a k A) (hG : PoleBoundary G a l B) :
    PoleBoundary (fun s ↦ F s * G s) a (k + l + 1) (A * B) where
  interior := hF.interior.mul hG.interior
  pole := by
    obtain ⟨r₁, hr₁, g₁, hg₁, hga₁, hF₁⟩ := hF.pole
    obtain ⟨r₂, hr₂, g₂, hg₂, hga₂, hG₂⟩ := hG.pole
    let r := min r₁ r₂
    have hsub₁ : ball (a : ℂ) r ⊆ ball (a : ℂ) r₁ := ball_subset_ball (min_le_left _ _)
    have hsub₂ : ball (a : ℂ) r ⊆ ball (a : ℂ) r₂ := ball_subset_ball (min_le_right _ _)
    refine ⟨r, lt_min hr₁ hr₂, fun s ↦ g₁ s * g₂ s, (hg₁.mono hsub₁).mul (hg₂.mono hsub₂),
      by simp [hga₁, hga₂], fun s hs hsre ↦ ?_⟩
    rw [hF₁ s (hsub₁ hs) hsre, hG₂ s (hsub₂ hs) hsre, div_mul_div_comm, ← pow_add]
    congr 2
    omega
  away y hy := by
    obtain ⟨r₁, hr₁, g₁, hg₁, hF₁⟩ := hF.away y hy
    obtain ⟨r₂, hr₂, g₂, hg₂, hG₂⟩ := hG.away y hy
    let r := min r₁ r₂
    have hsub₁ : ball ((a : ℂ) + y * I) r ⊆ ball ((a : ℂ) + y * I) r₁ :=
      ball_subset_ball (min_le_left _ _)
    have hsub₂ : ball ((a : ℂ) + y * I) r ⊆ ball ((a : ℂ) + y * I) r₂ :=
      ball_subset_ball (min_le_right _ _)
    exact ⟨r, lt_min hr₁ hr₂, fun s ↦ g₁ s * g₂ s, (hg₁.mono hsub₁).mul (hg₂.mono hsub₂),
      fun s hs hsre ↦ by rw [hF₁ s (hsub₁ hs) hsre, hG₂ s (hsub₂ hs) hsre]⟩

/-- Raising a function with a pole of order `k + 1` and leading coefficient `A` to the `(m + 1)`-th
power produces a pole of order `(m + 1) * (k + 1)` (parameter `m * (k + 1) + k`) with leading
coefficient `A ^ (m + 1)`. -/
theorem pow_succ (h : PoleBoundary F a k A) :
    ∀ m : ℕ, PoleBoundary (fun s ↦ F s ^ (m + 1)) a (m * (k + 1) + k) (A ^ (m + 1))
  | 0 => by simpa using h
  | m + 1 => by
    have ih := (h.pow_succ m).mul h
    have hexp : m * (k + 1) + k + k + 1 = (m + 1) * (k + 1) + k := by ring
    rw [hexp] at ih
    simpa only [← _root_.pow_succ] using ih

/-- Raising a function with a simple pole (`k = 0`) and residue `A` at `a` to the `(m + 1)`-th
power produces a pole of order `m + 1` with leading coefficient `A ^ (m + 1)`. -/
theorem pow_succ_of_zero (h : PoleBoundary F a 0 A) (m : ℕ) :
    PoleBoundary (fun s ↦ F s ^ (m + 1)) a m (A ^ (m + 1)) := by
  simpa using h.pow_succ m

end PoleBoundary

/-! ### Half-plane congruence, zero, and model poles -/

/-- `PoleBoundary` is invariant under equality on the open half-plane `Re s > a`. -/
theorem poleBoundary_congr {F G : ℂ → ℂ} {a A : ℝ} {k : ℕ}
    (hFG : ∀ s : ℂ, a < s.re → F s = G s) :
    PoleBoundary F a k A ↔ PoleBoundary G a k A :=
  ⟨fun h ↦ h.congr hFG, fun h ↦ h.congr fun s hs ↦ (hFG s hs).symm⟩

/-- Updating a function at any point `z` with `Re z ≤ a` leaves `PoleBoundary` unchanged. -/
@[simp]
theorem poleBoundary_update_iff_of_re_le {F : ℂ → ℂ} {a A : ℝ} {k : ℕ} {z : ℂ} (hz : z.re ≤ a)
    (w : ℂ) :
    PoleBoundary (Function.update F z w) a k A ↔ PoleBoundary F a k A :=
  ⟨fun h ↦ h.congr fun s hs ↦ by
      rw [Function.update_of_ne]
      rintro rfl
      exact lt_irrefl _ (hs.trans_le hz),
    fun h ↦ h.update_of_re_le hz w⟩

/-- Any function analytic at every point of the closed right half-plane `Re s ≥ a` satisfies
`PoleBoundary F a k 0` for every `k`. -/
theorem poleBoundary_of_analyticOnNhd {F : ℂ → ℂ} {a : ℝ}
    (hF : AnalyticOnNhd ℂ F {s : ℂ | a ≤ s.re}) (k : ℕ) :
    PoleBoundary F a k 0 where
  interior := hF.mono fun _ (hs : a < _) ↦ hs.le
  pole := by
    obtain ⟨r, hr, hF_ball⟩ := (hF a (by simp)).exists_ball_analyticOnNhd
    refine ⟨r, hr, fun s ↦ F s * (s - a) ^ (k + 1),
      hF_ball.mul ((analyticOnNhd_id.sub analyticOnNhd_const).pow _),
      by simp [zero_pow (Nat.succ_ne_zero k)], fun s _ hsre ↦ ?_⟩
    have hsa : (s - (a : ℂ)) ^ (k + 1) ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr fun h ↦ by simp [h] at hsre)
    exact (mul_div_cancel_right₀ _ hsa).symm
  away y _ := by
    obtain ⟨r, hr, hF_ball⟩ := (hF ((a : ℂ) + y * I) (by simp)).exists_ball_analyticOnNhd
    exact ⟨r, hr, F, hF_ball, fun _ _ _ ↦ rfl⟩

/-- The identically zero function satisfies `PoleBoundary 0 a k 0`. -/
theorem poleBoundary_zero (a : ℝ) (k : ℕ) : PoleBoundary 0 a k 0 :=
  poleBoundary_of_analyticOnNhd analyticOnNhd_const k

/-- The identically zero function satisfies `PoleBoundary 0 a k A` if and only if `A = 0`. -/
@[simp]
theorem poleBoundary_zero_iff {a A : ℝ} {k : ℕ} : PoleBoundary 0 a k A ↔ A = 0 :=
  ⟨fun h ↦ h.unique (poleBoundary_zero a k), fun h ↦ h ▸ poleBoundary_zero a k⟩

/-- The model pole `s ↦ A / (s - a) ^ (k + 1)` satisfies `PoleBoundary` at `a` of order `k + 1`
with leading coefficient `A` for all real `a`, `A` and natural `k`. -/
theorem poleBoundary_div_sub_pow (a A : ℝ) (k : ℕ) :
    PoleBoundary (fun s ↦ (A : ℂ) / (s - a) ^ (k + 1)) a k A where
  interior := analyticOnNhd_const.div
    ((analyticOnNhd_id.sub analyticOnNhd_const).pow _) fun s (hs : a < s.re) ↦
      pow_ne_zero _ (sub_ne_zero.mpr fun h ↦ by simp [h] at hs)
  pole := ⟨1, zero_lt_one, fun _ ↦ A, analyticOnNhd_const, rfl, fun _ _ _ ↦ rfl⟩
  away y hy := by
    let z₀ : ℂ := (a : ℂ) + y * I
    have hy0 : 0 < |y| := abs_pos.mpr hy
    have hne : ∀ s ∈ ball z₀ |y|, (s - a) ^ (k + 1) ≠ 0 := by
      intro s hs
      apply pow_ne_zero
      apply sub_ne_zero.mpr
      rintro rfl
      rw [mem_ball, dist_eq_norm] at hs
      have hnorm : ‖(a : ℂ) - z₀‖ = |y| := by
        simp [z₀]
      exact lt_irrefl _ (hnorm ▸ hs)
    exact ⟨|y|, hy0, fun s ↦ (A : ℂ) / (s - a) ^ (k + 1),
      analyticOnNhd_const.div ((analyticOnNhd_id.sub analyticOnNhd_const).pow _) hne,
      fun _ _ _ ↦ rfl⟩

/-- Characterization of `PoleBoundary` for the model pole `s ↦ A / (s - a) ^ (k + 1)`. -/
@[simp]
theorem poleBoundary_div_sub_pow_iff (a A B : ℝ) (k : ℕ) :
    PoleBoundary (fun s ↦ (A : ℂ) / (s - a) ^ (k + 1)) a k B ↔ B = A :=
  ⟨fun h ↦ h.unique (poleBoundary_div_sub_pow a A k), fun h ↦ h ▸ poleBoundary_div_sub_pow a A k⟩

/-! ### The Riemann zeta function and its powers -/

/-- Mathlib's `riemannZeta` satisfies `PoleBoundary riemannZeta 1 0 1`: it is holomorphic off `1`
and `(s - 1) * riemannZeta s` has a removable singularity at `1` with value `1`. -/
theorem poleBoundary_riemannZeta : PoleBoundary riemannZeta 1 0 1 where
  interior := analyticOn_riemannZeta.mono fun s (hs : 1 < s.re) (h1 : s ∈ ({1} : Set ℂ)) ↦ by
    rw [mem_singleton_iff] at h1
    simp [h1] at hs
  pole := by
    let g : ℂ → ℂ := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1
    have hg_an : AnalyticAt ℂ g 1 := by
      refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 1)
        have h_eq : g =ᶠ[𝓝 s] fun w ↦ (w - 1) * riemannZeta w := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w (hw : w ≠ 1)
          simp [g, hw]
        exact (((differentiableAt_id.sub (differentiableAt_const 1)).mul
          (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq h_eq)
      · simpa only [g, continuousAt_update_same] using riemannZeta_residue_one
    obtain ⟨r, hr, hg_ball⟩ := hg_an.exists_ball_analyticOnNhd
    refine ⟨r, hr, g, hg_ball, by simp [g], fun s _ hsre ↦ ?_⟩
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hsre
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    push_cast
    simp only [g, Function.update_of_ne hs1, pow_one]
    exact (mul_div_cancel_left₀ _ hsub).symm
  away y hy := by
    have hne1 : ((1 : ℂ) + y * I) ≠ 1 := by simp [hy]
    obtain ⟨r, hr, hball⟩ := (analyticOn_riemannZeta _ hne1).exists_ball_analyticOnNhd
    exact ⟨r, hr, riemannZeta, hball, fun _ _ _ ↦ rfl⟩

/-- Every positive integer power `riemannZeta ^ (k + 1)` satisfies `PoleBoundary` at abscissa `1`
with pole order `k + 1` and leading coefficient `1`. -/
theorem poleBoundary_riemannZeta_pow (k : ℕ) :
    PoleBoundary (fun s ↦ riemannZeta s ^ (k + 1)) 1 k 1 := by
  simpa using poleBoundary_riemannZeta.pow_succ_of_zero k

/-! ### Necessity of continuation away from the real pole: the dyadic denominator -/

/-- On `Re s > 1`, `1 - exp ((1 - s) * log 2)` is nonvanishing since
`‖exp ((1 - s) * log 2)‖ < 1`. -/
private theorem one_sub_cexp_log_two_ne_zero {s : ℂ} (hs : 1 < s.re) :
    1 - cexp ((1 - s) * Real.log 2) ≠ 0 := by
  intro h
  have heq : cexp ((1 - s) * Real.log 2) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖cexp ((1 - s) * Real.log 2)‖ = 1 := by rw [heq, norm_one]
  rw [norm_exp] at hnorm
  have hre : ((1 - s) * Real.log 2).re < 0 := by
    simp only [mul_re, sub_re, one_re, ofReal_re, sub_im, one_im, zero_sub, ofReal_im, mul_zero,
      sub_zero]
    exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos one_lt_two)
  have hlt : Real.exp (((1 - s) * Real.log 2).re) < 1 := Real.exp_lt_one_iff.mpr hre
  linarith

/-- The dyadic sum `s ↦ (1 - exp ((1 - s) * log 2))⁻¹` is holomorphic on `Re s > 1`, so it
satisfies the `interior` clause of `PoleBoundary` at abscissa `1`. -/
theorem analyticOnNhd_inv_one_sub_cexp_log_two :
    AnalyticOnNhd ℂ (fun s ↦ (1 - cexp ((1 - s) * Real.log 2))⁻¹) {s : ℂ | 1 < s.re} := by
  refine AnalyticOnNhd.inv (analyticOnNhd_const.sub ?_) fun s hs ↦
    one_sub_cexp_log_two_ne_zero hs
  exact fun s _ ↦ ((analyticAt_const.sub analyticAt_id).mul analyticAt_const).cexp

/-- Near `s = 1`, `s ↦ (1 - exp ((1 - s) * log 2))⁻¹` has the local simple-pole form
`g s / (s - 1)` on a disc about `1` with `g` holomorphic and `g 1 = (Real.log 2)⁻¹`, so it
satisfies the `pole` clause of `PoleBoundary` at `a = 1`, `k = 0`, `A = (Real.log 2)⁻¹`. -/
theorem exists_pole_germ_inv_one_sub_cexp_log_two :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball (1 : ℂ) r) ∧
      g 1 = ((Real.log 2)⁻¹ : ℝ) ∧
      ∀ s ∈ ball (1 : ℂ) r, 1 < s.re →
        (1 - cexp ((1 - s) * Real.log 2))⁻¹ = g s / (s - 1) := by
  let denom : ℂ → ℂ := fun s ↦ 1 - cexp ((1 - s) * Real.log 2)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_ne : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog2.ne'
  have hderiv : HasDerivAt denom (Real.log 2 : ℂ) 1 := by
    have h1 : HasDerivAt (fun s : ℂ ↦ (1 - s) * (Real.log 2 : ℂ)) (-(Real.log 2 : ℂ)) 1 := by
      simpa using ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hasDerivAt_id 1)).mul_const
        (Real.log 2 : ℂ)
    have h2 : HasDerivAt denom (0 - cexp ((1 - (1 : ℂ)) * Real.log 2) * -(Real.log 2 : ℂ)) 1 :=
      (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub h1.cexp
    simpa [denom] using h2
  have hdenom_an : AnalyticOnNhd ℂ denom univ := fun s _ ↦
    analyticAt_const.sub (((analyticAt_const.sub analyticAt_id).mul analyticAt_const).cexp)
  let q : ℂ → ℂ := dslope denom 1
  have hq_an : AnalyticOnNhd ℂ q univ := hdenom_an.dslope 1
  have hq1_val : q 1 = (Real.log 2 : ℂ) := by
    rw [show q 1 = deriv denom 1 from dslope_same denom 1, hderiv.deriv]
  have hq1 : q 1 ≠ 0 := hq1_val ▸ hlog2_ne
  obtain ⟨r, hr, hq_ne⟩ :=
    Metric.eventually_nhds_iff_ball.mp ((hq_an 1 (mem_univ 1)).continuousAt.eventually_ne hq1)
  refine ⟨r, hr, fun s ↦ (q s)⁻¹, (hq_an.mono (subset_univ _)).inv hq_ne,
    by simp [hq1_val], fun s _ hsre ↦ ?_⟩
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hsre
  have hsub0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hqs : q s = denom s / (s - 1) := by
    have hd1 : denom 1 = 0 := by simp [denom]
    rw [show q s = slope denom 1 s from dslope_of_ne denom hs1, slope_def_field, hd1, sub_zero]
  dsimp only
  rw [hqs, inv_div, div_right_comm, div_self hsub0, one_div]

/-- Despite being holomorphic on `Re s > 1` with a simple pole at `s = 1`, the dyadic function
`s ↦ (1 - exp ((1 - s) * log 2))⁻¹` satisfies `PoleBoundary` at abscissa `1` for **no** pole order
`k + 1` and **no** leading coefficient `A`: its pole at `1 + (2π / log 2) i` violates the `away`
condition. -/
theorem not_poleBoundary_inv_one_sub_cexp_log_two (k : ℕ) (A : ℝ) :
    ¬ PoleBoundary (fun s ↦ (1 - cexp ((1 - s) * Real.log 2))⁻¹) 1 k A := by
  intro h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  let y : ℝ := 2 * Real.pi / Real.log 2
  have hy : y ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hlog2.ne'
  obtain ⟨r, hr, g, hg, hF⟩ := h.away y hy
  let z₀ : ℂ := (1 : ℂ) + y * I
  -- Along `s_ε = z₀ + ε` (`ε → 0⁺`), `1 - exp ((1 - s_ε) * log 2) = 1 - exp (-ε * log 2) → 0`
  -- while `g (z₀ + ε) → g z₀`, so `(1 - exp (-ε * log 2)) * g (z₀ + ε)` tends both to `1` and `0`.
  have hlim_g : Tendsto (fun ε : ℝ ↦ g (z₀ + ε)) (𝓝[>] 0) (𝓝 (g z₀)) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ g (z₀ + ε)) 0 :=
      (hg z₀ (mem_ball_self hr)).continuousAt.comp_of_eq
        (continuousAt_const.add Complex.continuous_ofReal.continuousAt) (by simp)
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hlim_d : Tendsto (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ)) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hprod0 : Tendsto (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ) * g (z₀ + ε))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hlim_d.mul hlim_g
  have hev_one : (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ) * g (z₀ + ε)) =ᶠ[𝓝[>] 0]
      fun _ ↦ (1 : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT hr] with ε ⟨hε0, hεr⟩
    have hmem : z₀ + (ε : ℂ) ∈ ball z₀ r := by
      simp [dist_eq_norm, abs_of_pos hε0, hεr]
    have hre : 1 < (z₀ + (ε : ℂ)).re := by
      simp [z₀, hε0]
    have hFε := hF (z₀ + ε) hmem hre
    have hexp_eq : cexp ((1 - (z₀ + ε)) * Real.log 2) = (Real.exp (-ε * Real.log 2) : ℂ) := by
      have harg : (1 - (z₀ + (ε : ℂ))) * Real.log 2 =
          ((-ε * Real.log 2 : ℝ) : ℂ) - (2 * Real.pi * I) := by
        have hy_mul : (y : ℂ) * Real.log 2 = 2 * Real.pi := by
          simp only [y]
          push_cast
          exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hlog2.ne')
        calc
          (1 - (z₀ + (ε : ℂ))) * Real.log 2
              = -(ε : ℂ) * Real.log 2 - (y : ℂ) * Real.log 2 * I := by
            simp only [z₀]
            ring
          _ = ((-ε * Real.log 2 : ℝ) : ℂ) - (2 * Real.pi * I) := by
            rw [hy_mul]
            push_cast
            ring
      rw [harg, sub_eq_add_neg, Complex.exp_add, Complex.exp_neg, exp_two_pi_mul_I, inv_one,
        mul_one, Complex.ofReal_exp]
    rw [hexp_eq] at hFε
    have hd_ne : (1 - (Real.exp (-ε * Real.log 2) : ℂ)) ≠ 0 := by
      have hlt : Real.exp (-ε * Real.log 2) < 1 :=
        Real.exp_lt_one_iff.mpr (by nlinarith)
      exact sub_ne_zero.mpr (by exact_mod_cast hlt.ne')
    rw [← hFε, mul_inv_cancel₀ hd_ne]
  have h10 : (1 : ℂ) = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hev_one.symm) hprod0
  exact one_ne_zero h10

end TauCeti.HigherPoleTauberian
