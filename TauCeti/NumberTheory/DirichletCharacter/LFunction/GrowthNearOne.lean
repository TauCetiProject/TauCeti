/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Growth of Dirichlet L-functions near the line `Re s = 1`

Let `χ` be a Dirichlet character modulo `N ≥ 1`, primitive or not, and `f_χ` its regularized
L-function (`DirichletCharacter.regularizedLFunction`: `L(s, χ)`, times `(s - 1) / s` if `χ` is
principal). Then:

* `‖f_χ(s)‖ ≤ 16 N ‖s‖` on `Re s ≥ 1 / 2`
  (`DirichletCharacter.norm_regularizedLFunction_le_mul_norm`);
* if `l ≥ 10¹⁰` and `N ≤ e^l`, then `‖f_χ(s)‖ ≤ l²` on `Re s ≥ 1 - 1 / l`, `‖s‖ ≤ 3 e^l`
  (`DirichletCharacter.norm_regularizedLFunction_le_sq`);
* under the same hypotheses, `‖f_χ'(s)‖ ≤ 2 l³` on `Re s ≥ 1 - 1 / (2 l)`, `‖s‖ ≤ 2 e^l`
  (`DirichletCharacter.norm_deriv_regularizedLFunction_le`).

The linear bound comes from the level-dependent bound `DirichletCharacter.norm_LFunction_le` for
the continued L-function. The bound near `Re s = 1` interpolates by the three-lines theorem on a
vertical strip of width `1 / 3` whose right edge lies in `Re z ≥ 1 + 1 / l`, between the linear
bound on the left edge and the comparison of the Dirichlet series with `ζ(Re z) ≤ 1 + l` on the
right edge (`DirichletCharacter.norm_LSeries_le_one_add`); the left edge has weight `6 / l` at `s`,
which reduces its size `e^{3l}` to a constant. The derivative bound is Cauchy's estimate on circles
of radius `1 / (2 l)`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean`
(`New.norm_LSeries_le_mul_norm_regularL`, `New.norm_regularL_le_sq`, `New.norm_deriv_regularL_le`);
`New.norm_LSeries_char_le` from the same file is `DirichletCharacter.norm_LSeries_le_one_add` in
`TauCeti/NumberTheory/DirichletCharacter/LFunction/Bounds.lean`. There the linear bound is proved by
partial summation; here it is derived from `DirichletCharacter.norm_LFunction_le`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Cambridge Studies in
  Advanced Mathematics 97 (2007), Lemma 10.15.
-/

public section

open Complex Real Set Filter Topology Metric HadamardThreeLines

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}

/-- The linear bound away from the pole: `‖f_χ(s)‖ ≤ 16 N ‖s‖` for `Re s ≥ 1 / 2`, when `s ≠ 1` or
`χ` is not principal. -/
private theorem norm_regularizedLFunction_le_of_ne (hs : 1 / 2 ≤ s.re) (h1 : s ≠ 1 ∨ χ ≠ 1) :
    ‖χ.regularizedLFunction s‖ ≤ 16 * N * ‖s‖ := by
  have hs_pos : 0 < s.re := by linarith
  have hs_norm : 1 / 2 ≤ ‖s‖ := hs.trans (re_le_norm s)
  by_cases hχ : χ = 1
  · subst hχ
    have hs_ne : s ≠ 1 := h1.resolve_right (not_not.2 rfl)
    have hs₁ : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hs_ne)
    have h_eq : (1 : DirichletCharacter ℂ N).regularizedLFunction s =
        (s - 1) / s * (1 : DirichletCharacter ℂ N).LFunction s := by
      rw [regularizedLFunction_one_apply, entireLFunction_one_apply hs_ne]
      ring
    have h_sub : ‖s - 1‖ ≤ 3 * ‖s‖ := by
      linarith [norm_sub_le s 1, norm_one (α := ℂ)]
    rw [h_eq, norm_mul, norm_div]
    calc ‖s - 1‖ / ‖s‖ * ‖(1 : DirichletCharacter ℂ N).LFunction s‖
      _ ≤ ‖s - 1‖ / ‖s‖ * (N * (‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re)) := by
        gcongr
        exact norm_LFunction_le _ hs_pos h1
      _ = N * (1 / ‖s‖ + ‖s - 1‖ / ‖s‖ + ‖s - 1‖ / s.re) := by field
      _ ≤ N * (4 * ‖s‖ + 3 + 2 * ‖s - 1‖) := by
        gcongr
        · rw [div_le_iff₀ (by linarith)]
          nlinarith
        · rw [div_le_iff₀ (by linarith)]
          linarith
        · rw [div_le_iff₀ hs_pos]
          nlinarith
      _ ≤ 16 * N * ‖s‖ := by nlinarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  · rw [regularizedLFunction_of_ne_one χ hχ]
    calc ‖χ.LFunction s‖ ≤ N * ‖s‖ / s.re := χ.norm_LFunction_le_level_mul_norm_div_re hχ hs_pos
      _ ≤ N * ‖s‖ / (1 / 2) := by gcongr
      _ ≤ 16 * N * ‖s‖ := by nlinarith [norm_nonneg s, (N.cast_nonneg : (0 : ℝ) ≤ N)]

/-- *Linear growth*: `‖f_χ(s)‖ ≤ 16 N ‖s‖` for `Re s ≥ 1 / 2`. -/
theorem norm_regularizedLFunction_le_mul_norm (hs : 1 / 2 ≤ s.re) :
    ‖χ.regularizedLFunction s‖ ≤ 16 * N * ‖s‖ := by
  by_cases h1 : s ≠ 1 ∨ χ ≠ 1
  · exact χ.norm_regularizedLFunction_le_of_ne hs h1
  -- At the pole of the principal character, pass to the limit from nearby points.
  obtain ⟨rfl, -⟩ : s = 1 ∧ χ = 1 := by simpa [not_or] using h1
  have h_cont : ContinuousAt (fun z ↦ ‖χ.regularizedLFunction z‖ - 16 * N * ‖z‖) 1 :=
    ((χ.differentiableAt_regularizedLFunction (.inl one_ne_zero)).continuousAt.norm).sub
      (continuous_const.mul continuous_norm).continuousAt
  have h_near : ∀ᶠ z in 𝓝[≠] (1 : ℂ), ‖χ.regularizedLFunction z‖ - 16 * N * ‖z‖ ≤ 0 := by
    have h_re : ∀ᶠ z in 𝓝 (1 : ℂ), 1 / 2 < z.re :=
      continuousAt_const.eventually_lt continuous_re.continuousAt (by norm_num)
    filter_upwards [nhdsWithin_le_nhds h_re, self_mem_nhdsWithin] with z hz (hz₁ : z ≠ 1)
    linarith [χ.norm_regularizedLFunction_le_of_ne hz.le (.inl hz₁)]
  linarith [le_of_tendsto (h_cont.tendsto.mono_left nhdsWithin_le_nhds) h_near]

/-- For `l ≥ 1` and `Re s > 1`, at distance at least `1 / l` from `1` if `χ` is principal,
`‖L(s, χ)‖ ≤ 2 l ‖f_χ(s)‖`. -/
theorem norm_LSeries_le_mul_norm_regularizedLFunction (hs : 1 < s.re) (hl : 1 ≤ l)
    (h_far : χ = 1 → 1 / l ≤ ‖s - 1‖) :
    ‖LSeries (fun n ↦ χ n) s‖ ≤ 2 * l * ‖χ.regularizedLFunction s‖ := by
  classical
  have hs_norm : 1 < ‖s‖ := hs.trans_le (re_le_norm s)
  have norm_le : ‖s‖ ≤ 2 * l * ‖s - if χ = 1 then 1 else 0‖ := by
    split_ifs with hχ
    · have h_one : 1 ≤ ‖s - 1‖ * l := (div_le_iff₀ (by linarith)).1 (h_far hχ)
      nlinarith [norm_nonneg (s - 1), norm_le_norm_sub_add s 1, norm_one (α := ℂ)]
    · simpa using le_mul_of_one_le_left (norm_nonneg s) (by linarith : 1 ≤ 2 * l)
  calc ‖LSeries (fun n ↦ χ n) s‖ = ‖LSeries (fun n ↦ χ n) s‖ / ‖s‖ * ‖s‖ := by field
    _ ≤ ‖LSeries (fun n ↦ χ n) s‖ / ‖s‖ * (2 * l * ‖s - if χ = 1 then 1 else 0‖) := by gcongr
    _ = 2 * l * ‖χ.regularizedLFunction s‖ := by
      rw [χ.regularizedLFunction_eq_LSeries hs, norm_mul, norm_div]
      ring

/-- If `Re z ≥ 1 / 2` and `‖z - (s - 2)‖ ≥ 1`, then `‖f_χ(z) / (z - (s - 2))‖ ≤ e^{3l}` when
`N ≤ e^l`, `‖s‖ ≤ 3 e^l` and `l ≥ 10¹⁰`. -/
private theorem norm_div_le_exp_cube (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_norm : ‖s‖ ≤ 3 * rexp l) {z : ℂ} (hz : 1 / 2 ≤ z.re) (h_denom : 1 ≤ ‖z - (s - 2)‖) :
    ‖χ.regularizedLFunction z / (z - (s - 2))‖ ≤ rexp l ^ 3 := by
  have exp_ge : l + 1 ≤ rexp l := add_one_le_exp l
  have hz_norm : ‖z‖ ≤ 4 * rexp l * ‖z - (s - 2)‖ := by
    nlinarith [norm_le_norm_sub_add z (s - 2), norm_sub_le s 2, Complex.norm_two]
  rw [norm_div, div_le_iff₀ (by linarith)]
  calc ‖χ.regularizedLFunction z‖ ≤ 16 * N * ‖z‖ := χ.norm_regularizedLFunction_le_mul_norm hz
    _ ≤ 16 * rexp l * (4 * rexp l * ‖z - (s - 2)‖) := by gcongr
    _ = 64 * rexp l ^ 2 * ‖z - (s - 2)‖ := by ring
    _ ≤ rexp l ^ 3 * ‖z - (s - 2)‖ := by
      gcongr
      nlinarith [sq_nonneg (rexp l), mul_le_mul exp_ge exp_ge (by linarith) (by positivity)]

/-- *Growth near `Re s = 1`*: if `l ≥ 10¹⁰` and `N ≤ e^l`, then `‖f_χ(s)‖ ≤ l²` for
`Re s ≥ 1 - 1 / l` and `‖s‖ ≤ 3 e^l`. -/
theorem norm_regularizedLFunction_le_sq (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_re : 1 - 1 / l ≤ s.re) (h_norm : ‖s‖ ≤ 3 * rexp l) : ‖χ.regularizedLFunction s‖ ≤ l ^ 2 := by
  -- Apply the three-lines theorem to `g(z) = f_χ(z) / (z - s + 2)` on the strip
  -- `a ≤ Re z ≤ a + 1 / 3` whose right edge lies at `Re s + 2 / l ≥ 1 + 1 / l`. The left edge,
  -- where `‖g‖ ≤ e^{3l}`, has the weight `6 / l` at `s`. The denominator makes `g` bounded; it has
  -- modulus at least `1` on the strip and is `2` at `s`.
  have inv_pos : 0 < 1 / l := by positivity
  have inv_le : 1 / l ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  set a : ℝ := s.re + 2 * (1 / l) - 1 / 3 with ha
  let g (z : ℂ) : ℂ := χ.regularizedLFunction z / (z - (s - 2))
  have denom_ge (z : ℂ) (hz : a ≤ z.re) : 1 ≤ ‖z - (s - 2)‖ :=
    le_trans (by simp; linarith) (re_le_norm _)
  have g_le (z : ℂ) (hz : a ≤ z.re) : ‖g z‖ ≤ rexp l ^ 3 :=
    χ.norm_div_le_exp_cube hl hN h_norm (by linarith) (denom_ge z hz)
  have right_edge (z : ℂ) (hz : z.re = a + 1 / 3) : ‖g z‖ ≤ 1 + l := by
    have hz_norm : 0 < ‖z‖ := by linarith [re_le_norm z]
    calc ‖g z‖ ≤ ‖χ.regularizedLFunction z‖ :=
          (norm_div _ _).trans_le (div_le_self (norm_nonneg _) (denom_ge z (by linarith)))
      _ ≤ ‖LSeries (fun n ↦ χ n) z‖ / ‖z‖ * ‖z‖ := by
        classical
        rw [χ.regularizedLFunction_eq_LSeries (by linarith), norm_mul, norm_div]
        gcongr
        split_ifs
        · rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
          simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, one_re, one_im]
          nlinarith
        · simp
      _ = ‖LSeries (fun n ↦ χ n) z‖ := div_mul_cancel₀ _ hz_norm.ne'
      _ ≤ 1 + l := χ.norm_LSeries_le_one_add (by linarith) (by linarith)
  have g_diff : DiffContOnCl ℂ g (verticalStrip a (a + 1 / 3)) := by
    refine DifferentiableOn.diffContOnCl fun z hz ↦ ?_
    rw [verticalStrip, closure_preimage_re, closure_Ioo (by linarith)] at hz
    obtain ⟨hz_left, -⟩ : a ≤ z.re ∧ z.re ≤ a + 1 / 3 := hz
    have h_denom : z - (s - 2) ≠ 0 := norm_pos_iff.1 (one_pos.trans_le (denom_ge z hz_left))
    have hz_ne : z ≠ 0 := ne_zero_of_re_pos (by linarith)
    exact ((χ.differentiableAt_regularizedLFunction (.inl hz_ne)).fun_div (by fun_prop)
      h_denom).differentiableWithinAt
  have weight : (s.re - a) / (a + 1 / 3 - a) = 1 - 6 / l := by rw [ha]; ring
  have three_lines : ‖g s‖ ≤ (rexp l ^ 3) ^ (1 - (1 - 6 / l)) * (1 + l) ^ (1 - 6 / l) := by
    have hs_strip : s ∈ verticalClosedStrip a (a + 1 / 3) := ⟨by linarith, by linarith⟩
    have g_bdd : BddAbove ((norm ∘ g) '' verticalClosedStrip a (a + 1 / 3)) :=
      ⟨rexp l ^ 3, forall_mem_image.2 fun z ⟨hz, _⟩ ↦ g_le z hz⟩
    rw [← weight]
    exact norm_le_interp_of_mem_verticalClosedStrip' (by linarith) hs_strip g_diff g_bdd
      (fun z hz ↦ g_le z hz.ge) right_edge
  have left_factor : (rexp l ^ 3) ^ (1 - (1 - 6 / l)) ≤ 3 ^ 18 := by
    have h_exp : ((3 : ℕ) * l) * (1 - (1 - 6 / l)) = (18 : ℕ) * 1 := by field
    rw [← Real.exp_natCast_mul, ← Real.exp_mul, h_exp, Real.exp_natCast_mul]
    exact pow_le_pow_left₀ (exp_nonneg 1) exp_one_lt_three.le 18
  have right_factor : (1 + l) ^ (1 - 6 / l) ≤ 1 + l :=
    rpow_le_self_of_one_le (by linarith) (sub_le_self 1 (by positivity))
  calc ‖χ.regularizedLFunction s‖ = 2 * ‖g s‖ := by simp [g, mul_div_cancel₀]
    _ ≤ 2 * (3 ^ 18 * (1 + l)) := by grw [three_lines, left_factor, right_factor]
    _ ≤ l ^ 2 := by nlinarith

/-- *Cauchy's estimate*: if `l ≥ 10¹⁰` and `N ≤ e^l`, then `‖f_χ'(s)‖ ≤ 2 l³` for
`Re s ≥ 1 - 1 / (2 l)` and `‖s‖ ≤ 2 e^l`. -/
theorem norm_deriv_regularizedLFunction_le (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_re : 1 - 1 / l / 2 ≤ s.re) (h_norm : ‖s‖ ≤ 2 * rexp l) :
    ‖deriv χ.regularizedLFunction s‖ ≤ 2 * l ^ 3 := by
  have inv_le : 1 / l ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have disc (z : ℂ) (hz : z ∈ closedBall s (1 / l / 2)) :
      1 - 1 / l ≤ z.re ∧ ‖z‖ ≤ 3 * rexp l := by
    rw [mem_closedBall_iff_norm] at hz
    exact ⟨by linarith [neg_le_of_abs_le (abs_re_le_norm (z - s)), sub_re z s],
      by linarith [norm_le_norm_sub_add z s, add_one_le_exp l]⟩
  have h_diff : DiffContOnCl ℂ χ.regularizedLFunction (ball s (1 / l / 2)) :=
    DifferentiableOn.diffContOnCl_ball (fun z hz ↦ (χ.differentiableAt_regularizedLFunction
      (.inl (ne_zero_of_re_pos (by linarith [(disc z hz).1])))).differentiableWithinAt) subset_rfl
  have h_sphere (z : ℂ) (hz : z ∈ sphere s (1 / l / 2)) : ‖χ.regularizedLFunction z‖ ≤ l ^ 2 := by
    obtain ⟨hz_re, hz_norm⟩ := disc z (sphere_subset_closedBall hz)
    exact χ.norm_regularizedLFunction_le_sq hl hN hz_re hz_norm
  calc ‖deriv χ.regularizedLFunction s‖ ≤ l ^ 2 / (1 / l / 2) :=
        norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) h_diff h_sphere
    _ = 2 * l ^ 3 := by field

end DirichletCharacter
