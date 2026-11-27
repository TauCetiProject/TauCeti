/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.PrimesInAP

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.NumberTheory.LSeries.Deriv

/-!
# Prime detection in a Gaussian logarithmic window

For a Dirichlet series of von Mangoldt coefficients in a residue class, subtract the initial
Dirichlet polynomial from its pole-cleared continuation and multiply by a Gaussian. The
maximum-modulus argument uses different representations on the two arcs of the circle:
continuation minus the initial polynomial on the left, and an absolutely convergent tail on
the right. The value at the center ultimately exceeds the boundary bound for a prime-free
window when the residue denominator and window location are polynomially bounded.

The normalization and two-arc argument are from `New.exists_prime_modEq_one_log_mem` in
`Lib/Analytic/Primes.lean` of <https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh>.
-/

public section

open Complex Filter Metric Set

namespace TauCeti.LSeries

private theorem norm_exp_gaussianWindow_le_one {X U : ℝ} {z : ℂ}
    (hU : X ^ 2 ≤ U) (hz : ‖(X : ℂ) * z‖ = 1) (hre : z.re ≤ U⁻¹) :
    ‖Complex.exp ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2)‖ ≤ 1 := by
  have hreal : |X * z.re| ≤ 1 := by
    simpa only [re_ofReal_mul, hz] using ((X : ℂ) * z).abs_re_le_norm
  have hsq := normSq_eq_norm_sq ((X : ℂ) * z)
  rw [normSq_mul, normSq_ofReal, normSq_apply, hz, one_pow] at hsq
  let D := X ^ 2 / 2 * (1 + X * z.re)
  have hD₀ : 0 ≤ D := by
    exact mul_nonneg (by positivity) (by linarith [(abs_le.mp hreal).1])
  have hD : D ≤ X ^ 2 := by
    have h := (abs_le.mp hreal).2
    dsimp only [D]
    nlinarith [mul_nonneg (sq_nonneg X) (sub_nonneg.mpr h)]
  have hX : X ≠ 0 := by rintro rfl; simp at hz
  have hU₀ : 0 < U := (sq_pos_of_ne_zero hX).trans_le hU
  have hprod : (U + D) * z.re ≤ 2 := calc
    _ ≤ (U + D) * U⁻¹ := mul_le_mul_of_nonneg_left hre (by positivity)
    _ ≤ 2 := by rw [← div_eq_mul_inv, div_le_iff₀ hU₀]; linarith
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have heq :
      ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2).re = (U + D) * z.re - 2 := by
    have hcoef : (X : ℂ) / 4 = ((X / 4 : ℝ) : ℂ) := (by push_cast; rfl)
    simp only [hcoef, sub_re, add_re, pow_two, mul_re, add_im, mul_im, ofReal_re, ofReal_im,
      one_re, one_im, zero_add, zero_mul, add_zero, sub_zero, re_ofNat, D]
    linear_combination -(X / 4) * hsq
  rw [heq]
  linarith

private theorem eventually_gaussian_center_gt (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 3 * X ^ (A + A) < Real.exp (X / 4 - 2) := by
  have hε : 0 < (6 * Real.exp 2)⁻¹ := by positivity
  have h := (isLittleO_pow_exp_pos_mul_atTop (A + A) (b := 1 / 4) (by norm_num)).bound hε
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with X hX hX₀
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hX₀ _), Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hX
  rw [← div_eq_inv_mul, le_div_iff₀ (by positivity)] at hX
  rw [Real.exp_sub, lt_div_iff₀ (Real.exp_pos _), div_eq_mul_inv X, mul_comm X (4 : ℝ)⁻¹]
  nlinarith [Real.exp_pos (1 / 4 * X)]

private theorem norm_gaussianWindow_boundary {X U : ℝ} {z F : ℂ} {S M : Finset ℕ}
    {t : ℕ → ℂ} (hX : 1 ≤ X) (hU : X ^ 2 ≤ U) (hz : ‖(X : ℂ) * z‖ = 1)
    (hSM : Disjoint S M) :
    let G := Complex.exp ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2)
    (z.re ≤ U⁻¹ → ‖F‖ ≤ 2 ∧ ‖G * ∑ n ∈ S, t n‖ ≤ U) →
    (U⁻¹ < z.re → HasSum t (F / z) ∧ ‖G * ∑ n ∈ M, t n‖ ≤ 1 ∧
      ‖G * ∑' n : ↥((↑(S ∪ M) : Set ℕ)ᶜ), t n‖ ≤ U) →
    ‖G * (F - z * ∑ n ∈ S, t n)‖ ≤ 3 * U := by
  intro G hleft hright
  have hX₀ : 0 < X := by positivity
  have hU₀ : 1 ≤ U := by nlinarith
  have hzn : ‖z‖ ≤ 1 := by
    rw [norm_mul, norm_real, Real.norm_of_nonneg hX₀.le] at hz
    nlinarith [mul_nonneg (sub_nonneg.mpr hX) (norm_nonneg z)]
  by_cases hr : z.re ≤ U⁻¹
  · obtain ⟨hF, hS⟩ := hleft hr
    have hG : ‖G‖ ≤ 1 := norm_exp_gaussianWindow_le_one hU hz hr
    have h₁ := (mul_le_of_le_one_left (norm_nonneg F) hG).trans hF
    have h₂ := (mul_le_of_le_one_left (norm_nonneg (G * ∑ n ∈ S, t n)) hzn).trans hS
    rw [mul_sub, mul_left_comm G z]
    refine (norm_sub_le ..).trans ?_
    rw [norm_mul G F, norm_mul z]
    linarith
  · obtain ⟨hs, hM, hT⟩ := hright (lt_of_not_ge hr)
    have hne : z ≠ 0 := by rintro rfl; simp at hz
    have hsplit := hs.summable.sum_add_tsum_compl (s := S ∪ M)
    rw [Finset.sum_union hSM, hs.tsum_eq] at hsplit
    have heq : F = z * ((∑ n ∈ S, t n) + (∑ n ∈ M, t n) +
        ∑' n : ↥((↑(S ∪ M) : Set ℕ)ᶜ), t n) := by
      rw [hsplit, mul_comm z, div_mul_cancel₀ _ hne]
    have hcancel : F - z * (∑ n ∈ S, t n) = z * ((∑ n ∈ M, t n) +
        ∑' n : ↥((↑(S ∪ M) : Set ℕ)ᶜ), t n) := by
      rw [heq]
      ring
    rw [hcancel, mul_left_comm G z, norm_mul z]
    refine (mul_le_of_le_one_left (norm_nonneg _) hzn).trans ?_
    rw [mul_add]
    exact (norm_add_le ..).trans (by linarith)

/-- A Gaussian boundary estimate forces a prime of the prescribed residue class into the
logarithmic window. Use disjoint finite index sets `S` (the initial part of the series) and `M`
(the middle part, with log indices in the window). The numerator `F` is holomorphic inside the
disk and continuous on its closure. On the right arc `Re z > 1 / U` it agrees with `z` times the
Dirichlet series at `1 + z`, and at the center it has the residue value `1 / φ(q)`. On the left
arc require bounds on `F` and the Gaussian-weighted initial part; on the right arc require a
bound on the weighted tail outside `S ∪ M` and that the weighted middle sum would be bounded by
`1` if `M` contained no primes of the prescribed class.
The threshold for `X` depends only on `A`. -/
theorem eventually_exists_prime_log_mem_Icc_of_gaussian_bounds (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ {U : ℝ} {q : ℕ}, q ≠ 0 → X ^ 2 ≤ U → U ≤ X ^ A →
      (q.totient : ℝ) ≤ X ^ A → ∀ (a : ZMod q) (S M : Finset ℕ), Disjoint S M →
      (∀ n ∈ M, Real.log n ∈ Icc U (U + X ^ 2)) →
      ∀ (F : ℂ → ℂ), DiffContOnCl ℂ F (ball 0 X⁻¹) →
      F 0 = (q.totient : ℂ)⁻¹ →
      let G : ℂ → ℂ := fun z ↦ Complex.exp ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2)
      let t : ℂ → ℕ → ℂ := fun z ↦
        _root_.LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt.residueClass a n : ℂ)) (1 + z)
      (∀ z : ℂ, ‖(X : ℂ) * z‖ = 1 → z.re ≤ U⁻¹ → ‖F z‖ ≤ 2) →
      (∀ z : ℂ, ‖(X : ℂ) * z‖ = 1 → z.re ≤ U⁻¹ → ‖G z * ∑ n ∈ S, t z n‖ ≤ U) →
      (∀ z : ℂ, ‖(X : ℂ) * z‖ = 1 → U⁻¹ < z.re → HasSum (t z) (F z / z)) →
      (∀ z : ℂ, ‖(X : ℂ) * z‖ = 1 → U⁻¹ < z.re →
        ‖G z * ∑' n : ↥((↑(S ∪ M) : Set ℕ)ᶜ), t z n‖ ≤ U) →
      ((∀ n ∈ M, ¬ (n.Prime ∧ (n : ZMod q) = a)) →
        ∀ z : ℂ, ‖(X : ℂ) * z‖ = 1 → U⁻¹ < z.re → ‖G z * ∑ n ∈ M, t z n‖ ≤ 1) →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ Real.log p ∈ Icc U (U + X ^ 2) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_gaussian_center_gt A] with X hX hcenter
  intro U q hq hU hUA hqA a S M hSM hM F hF hF₀ G t hLeft hInitial hSeries hTail hMiddle
  have hX₀ : 0 < X := by positivity
  have hXinv : 0 < X⁻¹ := inv_pos.mpr hX₀
  let H : ℂ → ℂ := fun z ↦ G z * (F z - z * ∑ n ∈ S, t z n)
  have hG : Differentiable ℂ G := by dsimp only [G]; fun_prop
  have hshift : Differentiable ℂ (fun z : ℂ ↦ 1 + z) := by fun_prop
  have hP : Differentiable ℂ (fun z ↦ ∑ n ∈ S, t z n) :=
    (_root_.LSeries.differentiable_sum_term _ S).comp hshift
  have hH : DiffContOnCl ℂ H (ball 0 X⁻¹) :=
    hG.diffContOnCl.smul (hF.sub (differentiable_id.mul hP).diffContOnCl)
  by_contra! hno
  have hMfree (n : ℕ) (hn : n ∈ M) : ¬ (n.Prime ∧ (n : ZMod q) = a) :=
    fun h ↦ hno n h.1 h.2 (hM n hn)
  have hb (z : ℂ) (hz : z ∈ sphere (0 : ℂ) X⁻¹) : ‖H z‖ ≤ 3 * U := by
    have hzn : ‖z‖ = X⁻¹ := by simpa [mem_sphere, dist_zero_right] using hz
    have hzX : ‖(X : ℂ) * z‖ = 1 := by simp [hzn, abs_of_pos hX₀, hX₀.ne']
    exact norm_gaussianWindow_boundary hX.le hU hzX hSM
      (fun hr ↦ ⟨hLeft z hzX hr, hInitial z hzX hr⟩)
      (fun hr ↦ ⟨hSeries z hzX hr, hMiddle hMfree z hzX hr, hTail z hzX hr⟩)
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hH
    (by simpa only [frontier_ball _ hXinv.ne'] using hb)
    (subset_closure (mem_ball_self hXinv))
  have hval : ‖H 0‖ = Real.exp (X / 4 - 2) * (q.totient : ℝ)⁻¹ := by
    simp [H, G, hF₀, Complex.norm_exp]
  rw [hval] at hmax
  have hq₀ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  rw [← div_eq_mul_inv, div_le_iff₀ hq₀] at hmax
  have hpoly := mul_le_mul hUA hqA (by positivity) (by positivity)
  rw [← pow_add] at hpoly
  linarith

end TauCeti.LSeries
