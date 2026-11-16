/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.HalfPlane
import TauCeti.Analysis.Complex.HalfPlaneIdentity

/-!
# Boundary continuation on a vertical line with a pole of integer order

This file defines the boundary-continuation predicate `TauCeti.HigherPoleTauberian.PoleBoundary`
underlying the integer-order case of Delange's Tauberian theorem for Laplace transforms and
Dirichlet series, and develops its uniqueness, algebraic, scaling, and model-pole API.

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
  `PoleBoundary.of_lt`, `PoleBoundary.eq_zero_of_lt`, `PoleBoundary.order_unique` (uniqueness of
  `k` when leading coefficients are nonzero), and `poleBoundary_zero_iff`.
* Algebraic and analytic closure: `PoleBoundary.mul_analytic` and `PoleBoundary.analytic_mul`
  (multiplication by a function analytic on `Re s ≥ a` with real value at `a`),
  `PoleBoundary.const_mul`, `PoleBoundary.neg`, `PoleBoundary.add`, `PoleBoundary.sub`,
  `PoleBoundary.div_id` (division by `s` for `0 < a`, dividing `A` by `a`),
  `PoleBoundary.comp_mul_left` and `PoleBoundary.comp_mul_left_abscissa` (rescaling `s ↦ c * s` for
  `0 < c`, and rescaling `a` to `1`), `PoleBoundary.comp_add_right` (horizontal translation),
  `PoleBoundary.mul` (products add pole orders), `PoleBoundary.pow_succ`, and
  `PoleBoundary.pow_succ_of_zero`.
* Analytic functions and model poles: `poleBoundary_of_analyticOnNhd`, `poleBoundary_zero`,
  `poleBoundary_div_sub_pow`, and `poleBoundary_div_sub_pow_iff`.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242 (§5.2.1, Theorem III, pp. 235–238).
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
    (hg₁.mono hsub₁).eqOn_ball_of_eqOn_re_gt (a := a) (hg₂.mono hsub₂) (by simpa using hr)
      (fun s ⟨hs, hsre⟩ ↦ by
        have hsa : (s - a) ^ (k + 1) ≠ 0 :=
          pow_ne_zero _ (sub_ne_zero.mpr fun h ↦ by simp [h] at hsre)
        exact (div_left_inj₀ hsa).mp ((hF₁ s (hsub₁ hs) hsre).symm.trans (hF₂ s (hsub₂ hs) hsre)))
      (mem_ball_self hr)
  exact Complex.ofReal_injective (hga₁.symm.trans (hcenter.trans hga₂))

/-- A pole of order at most `k + 1` is also a pole of order at most `l + 1` with leading
coefficient `0` whenever `k < l`. -/
theorem of_lt (h : PoleBoundary F a k A) (hkl : k < l) : PoleBoundary F a l 0 where
  interior := h.interior
  pole := by
    obtain ⟨r, hr, g, hg, -, hF⟩ := h.pole
    refine ⟨r, hr, fun s ↦ g s * (s - a) ^ (l - k),
      hg.mul ((analyticOnNhd_id.sub analyticOnNhd_const).pow _), ?_, fun s hs hsre ↦ ?_⟩
    · simp [Nat.sub_ne_zero_of_lt hkl]
    · have hsa : s - (a : ℂ) ≠ 0 := sub_ne_zero.mpr fun hs' ↦ by simp [hs'] at hsre
      have hexp : l + 1 = (k + 1) + (l - k) := by omega
      dsimp only
      rw [hF s hs hsre, hexp, pow_add _ (k + 1) (l - k),
        mul_div_mul_right _ _ (pow_ne_zero _ hsa)]
  away := h.away

/-- If `F` satisfies `PoleBoundary F a k A` and `PoleBoundary F a l B` with `k < l`, then the
higher-order numerator vanishes at `a`: `B = 0`. -/
theorem eq_zero_of_lt (hk : PoleBoundary F a k A) (hl : PoleBoundary F a l B) (hkl : k < l) :
    B = 0 :=
  hl.unique (hk.of_lt hkl)

/-- When the leading coefficients `A` and `B` are both nonzero, the pole order parameter `k` in
`PoleBoundary F a k A` is uniquely determined. -/
theorem order_unique (hk : PoleBoundary F a k A) (hl : PoleBoundary F a l B)
    (hA : A ≠ 0) (hB : B ≠ 0) : k = l := by
  rcases lt_trichotomy k l with hlt | rfl | hgt
  · exact absurd (hk.eq_zero_of_lt hl hlt) hB
  · rfl
  · exact absurd (hl.eq_zero_of_lt hk hgt) hA

/-! ### Algebraic and scaling operations -/

/-- Multiplying `F` on the right by a function `H` analytic at every point of the closed half-plane
`Re s ≥ a` with real value `H a = C` preserves `PoleBoundary` at `(a, k)` (order at most `k + 1`)
and multiplies the leading coefficient by `C`. -/
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

/-- Multiplying `F` by a real constant `c` scales the leading coefficient by `c`. -/
theorem const_mul (h : PoleBoundary F a k A) (c : ℝ) :
    PoleBoundary (fun s ↦ (c : ℂ) * F s) a k (c * A) :=
  h.analytic_mul analyticOnNhd_const rfl

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

/-- Dividing `F` by `s` at a positive abscissa `a > 0` preserves `PoleBoundary` at `(a, k)` (order
at most `k + 1`) and divides the leading coefficient by `a`. -/
theorem div_id (h : PoleBoundary F a k A) (ha : 0 < a) :
    PoleBoundary (fun s ↦ F s / s) a k (A / a) := by
  have hinv : AnalyticOnNhd ℂ (fun s : ℂ ↦ s⁻¹) {s : ℂ | a ≤ s.re} :=
    analyticOnNhd_id.inv fun s (hs : a ≤ s.re) h0 ↦ by simp [h0] at hs; linarith
  simpa [div_eq_mul_inv] using h.mul_analytic hinv (C := a⁻¹) (by simp)

/-- Rescaling `s ↦ F (c * s)` by any positive real factor `c > 0` divides the abscissa by `c` and
divides the leading coefficient by `c ^ (k + 1)`. -/
theorem comp_mul_left (h : PoleBoundary F a k A) {c : ℝ} (hc : 0 < c) :
    PoleBoundary (fun s ↦ F (c * s)) (a / c) k (A / c ^ (k + 1)) := by
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hre {s : ℂ} (hs : a / c < s.re) : a < ((c : ℂ) * s).re := by
    simpa using (div_lt_iff₀' hc).mp hs
  have hball {r : ℝ} {z w s : ℂ} (hzw : (c : ℂ) * z = w) (hs : s ∈ ball z (r / c)) :
      (c : ℂ) * s ∈ ball w r := by
    rw [mem_ball, dist_eq_norm] at hs ⊢
    rw [← hzw, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
    exact (lt_div_iff₀' hc).mp hs
  refine ⟨fun s hs ↦ (h.interior _ (hre hs)).fun_comp_of_eq
    (analyticAt_const.mul analyticAt_id) rfl, ?_, fun y hy ↦ ?_⟩
  · obtain ⟨r, hr, g, hg, hga, hF⟩ := h.pole
    have hball₀ : ∀ s ∈ ball ((a / c : ℝ) : ℂ) (r / c), (c : ℂ) * s ∈ ball (a : ℂ) r :=
      fun s ↦ hball (by push_cast; exact mul_div_cancel₀ _ hc0)
    have hg_inner : AnalyticOnNhd ℂ (fun s ↦ g ((c : ℂ) * s)) (ball ((a / c : ℝ) : ℂ) (r / c)) :=
      fun s hs ↦ (hg _ (hball₀ s hs)).fun_comp_of_eq (analyticAt_const.mul analyticAt_id) rfl
    refine ⟨r / c, div_pos hr hc, _,
      hg_inner.div analyticOnNhd_const fun _ _ ↦ pow_ne_zero _ hc0,
      by rw [Complex.ofReal_div, mul_div_cancel₀ _ hc0, hga, Complex.ofReal_div,
        Complex.ofReal_pow],
      fun s hs hsre ↦ ?_⟩
    rw [hF _ (hball₀ s hs) (hre hsre), div_div, ← mul_pow]
    congr 2; push_cast; field_simp
  · obtain ⟨r, hr, g, hg, hF⟩ := h.away (c * y) (mul_ne_zero hc.ne' hy)
    have hball_y : ∀ s ∈ ball (((a / c : ℝ) : ℂ) + y * I) (r / c),
        (c : ℂ) * s ∈ ball ((a : ℂ) + (c * y : ℝ) * I) r :=
      fun s ↦ hball (by push_cast; field_simp)
    exact ⟨r / c, div_pos hr hc, fun s ↦ g ((c : ℂ) * s),
      fun s hs ↦ (hg _ (hball_y s hs)).fun_comp_of_eq (analyticAt_const.mul analyticAt_id) rfl,
      fun s hs hsre ↦ hF _ (hball_y s hs) (hre hsre)⟩

/-- Rescaling `s ↦ F (a * s)` for `0 < a` moves the boundary line from `a` to `1` and divides the
leading coefficient by `a ^ (k + 1)`. -/
theorem comp_mul_left_abscissa (h : PoleBoundary F a k A) (ha : 0 < a) :
    PoleBoundary (fun s ↦ F (a * s)) 1 k (A / a ^ (k + 1)) := by
  simpa [div_self ha.ne'] using h.comp_mul_left ha

/-- Horizontal translation `s ↦ F (s + c)` for real `c` shifts the abscissa from `a` to `a - c`
without changing the pole order or leading coefficient. -/
theorem comp_add_right (h : PoleBoundary F a k A) (c : ℝ) :
    PoleBoundary (fun s ↦ F (s + c)) (a - c) k A := by
  have hre {s : ℂ} (hs : a - c < s.re) : a < (s + c).re := by
    simpa using sub_lt_iff_lt_add.mp hs
  have hball {r : ℝ} {z w s : ℂ} (hzw : z + c = w) (hs : s ∈ ball z r) :
      s + c ∈ ball w r := by
    simpa [← hzw, dist_add_right] using hs
  refine ⟨fun s hs ↦ (h.interior _ (hre hs)).fun_comp_of_eq
    (analyticAt_id.add analyticAt_const) rfl, ?_, fun y hy ↦ ?_⟩
  · obtain ⟨r, hr, g, hg, hga, hF⟩ := h.pole
    have hball₀ : ∀ s ∈ ball ((a - c : ℝ) : ℂ) r, s + c ∈ ball (a : ℂ) r :=
      fun s ↦ hball (by push_cast; ring)
    refine ⟨r, hr, fun s ↦ g (s + c),
      fun s hs ↦ (hg _ (hball₀ s hs)).fun_comp_of_eq (analyticAt_id.add analyticAt_const) rfl,
      by simpa [sub_add_cancel] using hga, fun s hs hsre ↦ ?_⟩
    rw [hF _ (hball₀ s hs) (hre hsre)]
    congr 2; push_cast; ring
  · obtain ⟨r, hr, g, hg, hF⟩ := h.away y hy
    have hball_y : ∀ s ∈ ball (((a - c : ℝ) : ℂ) + y * I) r,
        s + c ∈ ball ((a : ℂ) + y * I) r :=
      fun s ↦ hball (by push_cast; ring)
    exact ⟨r, hr, fun s ↦ g (s + c),
      fun s hs ↦ (hg _ (hball_y s hs)).fun_comp_of_eq (analyticAt_id.add analyticAt_const) rfl,
      fun s hs hsre ↦ hF _ (hball_y s hs) (hre hsre)⟩

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

end TauCeti.HigherPoleTauberian
