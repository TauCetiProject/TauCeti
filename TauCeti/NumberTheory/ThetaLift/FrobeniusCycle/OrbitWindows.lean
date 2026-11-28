/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Window sizes on candidate Frobenius orbits

At selection density `δ = x ^ (-d)`, each cell has width `⌈1 / δ⌉`. The marked-tile
search uses logarithmically many tiles, so even its enlarged window fits several times in
an orbit of length at least `x ^ e`, provided `d < e`. The same comparison makes the expected
number of selected positions in the enlarged window logarithmic in the scale.

The window sizes are from Levent Alpöge's `Formalism.MainNotions.G.TopChoiceBounds`
in [`TopChoiceBounds.lean`][alpoege-rh].

[alpoege-rh]: https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/TopChoiceBounds.lean
-/

public section

open Filter Real

namespace TauCeti

/-- At density `x ^ (-d)`, the enlarged window of `⌈B log x⌉ + 5` tiles, each with `6r + 1`
cells, has expected count at most `2 (|B| + 6) (6r + 1) log x` when every position is
sampled at that density. This also bounds the expected count for smaller sampling rates. -/
theorem frobeniusOrbit_tileWindow_mul_rpow_neg_le (r : ℕ) (B : ℝ) {x d : ℝ}
    (hx : exp 1 ≤ x) (hd : 0 ≤ d) :
    let G : ℕ := (⌈B * log x⌉₊ + 5) * (6 * r + 1) * ⌈x ^ d⌉₊
    (G : ℝ) * x ^ (-d) ≤ 2 * (|B| + 6) * (6 * (r : ℝ) + 1) * log x := by
  intro G
  have hx₀ : 0 < x := (exp_pos 1).trans_le hx
  have hlog : 1 ≤ log x := (le_log_iff_exp_le hx₀).2 hx
  have hx₁ : 1 ≤ x := (one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hM : (⌈B * log x⌉₊ : ℝ) + 5 ≤ (|B| + 6) * log x := by
    have hb : B * log x ≤ |B| * log x :=
      mul_le_mul_of_nonneg_right (le_abs_self B) (by linarith)
    have hz := Nat.ceil_lt_add_one (show 0 ≤ |B| * log x by positivity)
    have hm : (⌈B * log x⌉₊ : ℝ) ≤ ⌈|B| * log x⌉₊ := by exact_mod_cast Nat.ceil_mono hb
    linarith [show 6 ≤ 6 * log x by linarith]
  have hu : (⌈x ^ d⌉₊ : ℝ) * x ^ (-d) ≤ 2 := by
    have h := (Nat.ceil_lt_add_one (rpow_nonneg hx₀.le d)).le
    calc
      _ ≤ (x ^ d + x ^ d) * x ^ (-d) := by
        gcongr
        linarith [one_le_rpow hx₁ hd]
      _ = 2 := by rw [add_mul, ← rpow_add hx₀, add_neg_cancel, rpow_zero]; norm_num
  dsimp only [G]
  push_cast
  calc
    _ = ((⌈B * log x⌉₊ : ℝ) + 5) * (6 * (r : ℝ) + 1) * ((⌈x ^ d⌉₊ : ℝ) * x ^ (-d)) := by
      ring
    _ ≤ ((|B| + 6) * log x) * (6 * (r : ℝ) + 1) * 2 := by gcongr
    _ = _ := by ring

/-- Uniformly over candidate orbit lengths `n ≥ x ^ e`, a fixed short window of length `L`
is shorter than a cell, the orbit fits three enlarged tile windows, and the expected count
using the minimum sampling rate `ω * x ^ (-d)` is at least `4r`. The number of searched tiles
is set by `⌈B log x⌉`, independently of the orbit. -/
theorem eventually_frobeniusOrbit_window_bounds (r L : ℕ) (B ω : ℝ) {d e : ℝ}
    (hd : 0 < d) (hde : d < e) (hω : 0 < ω) :
    ∀ᶠ x : ℝ in atTop,
      let u := ⌈x ^ d⌉₊
      let M := ⌈B * log x⌉₊
      let G := (M + 5) * (6 * r + 1) * u
      L < u ∧ 3 * (G : ℝ) ≤ x ^ e ∧
        ∀ n : ℕ, x ^ e ≤ (n : ℝ) → 4 * (r : ℝ) ≤ (n : ℝ) * x ^ (-d) * ω := by
  let C : ℝ := 6 * (|B| + 6) * (6 * (r : ℝ) + 1)
  have hgap : 0 < e - d := sub_pos.mpr hde
  have hlog : ∀ᶠ x : ℝ in atTop, ‖C * log x‖ ≤ ‖x ^ (e - d)‖ := by
    simpa only [one_mul] using ((isLittleO_log_rpow_atTop hgap).const_mul_left C).bound one_pos
  filter_upwards [eventually_ge_atTop (exp 1), (tendsto_rpow_atTop hd).eventually_gt_atTop (L : ℝ),
    hlog, (tendsto_rpow_atTop hgap).eventually_ge_atTop (4 * (r : ℝ) / ω)]
    with x hx hL hlog hmean
  intro u M G
  have hx₀ : 0 < x := (exp_pos 1).trans_le hx
  have hδ := rpow_pos_of_pos hx₀ (-d)
  have hscale : x ^ (e - d) = x ^ e * x ^ (-d) := by rw [sub_eq_add_neg, rpow_add hx₀]
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hL.trans_le (Nat.le_ceil (x ^ d))
  · have hG := frobeniusOrbit_tileWindow_mul_rpow_neg_le r B hx hd.le
    apply (mul_le_mul_iff_of_pos_right hδ).mp
    calc
      3 * (G : ℝ) * x ^ (-d) ≤ C * log x := by dsimp only [C, G, M, u]; linarith only [hG]
      _ ≤ x ^ (e - d) := by
        rw [norm_of_nonneg (rpow_nonneg hx₀.le _)] at hlog
        exact (le_abs_self _).trans hlog
      _ = x ^ e * x ^ (-d) := hscale
  · intro n hn
    apply (div_le_iff₀ hω).mp
    rw [hscale] at hmean
    exact hmean.trans (mul_le_mul_of_nonneg_right hn hδ.le)

/-- The long-window cutoff `⌈max(6 exp(1) G δ, H log₂ x)⌉ + 1` for the top count is
logarithmic in `x`, with a bound independent of the orbit length. Here `G` is the enlarged
tile window and `δ = x ^ (-d)` is the sampling density. -/
theorem frobeniusOrbit_topCutoff_le_log (r : ℕ) (B H : ℝ) {x d : ℝ}
    (hx : exp 1 ≤ x) (hd : 0 ≤ d) :
    let G : ℕ := (⌈B * log x⌉₊ + 5) * (6 * r + 1) * ⌈x ^ d⌉₊
    let N := ⌈max (6 * exp 1 * G * x ^ (-d)) (H * logb 2 x)⌉₊ + 1
    (N : ℝ) ≤ (max (12 * exp 1 * (|B| + 6) * (6 * (r : ℝ) + 1)) (H / log 2) + 2) * log x := by
  intro G N
  have hx₀ : 0 < x := (exp_pos 1).trans_le hx
  have hlog : 1 ≤ log x := (le_log_iff_exp_le hx₀).2 hx
  let A := 12 * exp 1 * (|B| + 6) * (6 * (r : ℝ) + 1)
  have hG : 6 * exp 1 * G * x ^ (-d) ≤ A * log x := by
    have h := mul_le_mul_of_nonneg_left (frobeniusOrbit_tileWindow_mul_rpow_neg_le r B hx hd)
      (show 0 ≤ 6 * exp 1 by positivity)
    dsimp only [G, A]
    linarith only [h]
  have hh : H * logb 2 x = (H / log 2) * log x := by rw [logb]; ring
  have hmax : max (6 * exp 1 * G * x ^ (-d)) (H * logb 2 x) ≤ max A (H / log 2) * log x := by
    rw [hh, max_mul_of_nonneg _ _ (by linarith : 0 ≤ log x)]
    exact max_le_max hG le_rfl
  have hn : 0 ≤ max (6 * exp 1 * G * x ^ (-d)) (H * logb 2 x) :=
    (by positivity : 0 ≤ 6 * exp 1 * G * x ^ (-d)).trans (le_max_left ..)
  have hceil := Nat.ceil_lt_add_one hn
  dsimp only [A] at hmax
  dsimp only [N]
  push_cast
  linarith only [hceil, hmax, hlog]

end TauCeti
