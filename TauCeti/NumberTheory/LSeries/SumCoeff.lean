/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.NumberTheory.AbelSummation

/-!
# Analytic continuation of an L-series from a bound on its partial sums

If the partial sums `A(n) = ∑_{k=1}^n f k` of a sequence `f : ℕ → ℂ` are `O(n ^ r)`, Mathlib's
`LSeries_eq_mul_integral` (from `Mathlib/NumberTheory/LSeries/SumCoeff.lean`)
writes the L-series of `f` as

`LSeries f s = s * ∫ t in Set.Ioi 1, A(⌊t⌋₊) * t ^ (-(s + 1))`

wherever `LSeries f` converges and `r < Re s`. The right-hand side makes sense on the whole
half-plane `r < Re s`, independently of the convergence of the series, and this file proves that it
is holomorphic there: it is `s` times the Mellin transform of the step function `t ↦ A(⌊t⌋₊)`
at `-s`, and Mathlib's `mellin_differentiableAt_of_isBigO_rpow` applies because the step function
vanishes on `(0, 1)` and is `O(t ^ r)` at infinity.

Together the two statements continue `LSeries f` analytically from its half-plane of convergence
to `Re s > r`; this is the classical continuation of a Dirichlet series with cancelling
coefficients by partial summation (see e.g. Tenenbaum, *Introduction to Analytic and
Probabilistic Number Theory*, Chapter II.1).

## Main results

* `TauCeti.LSeries.differentiableOn_integral_mul_cpow_of_isBigO`,
  `TauCeti.LSeries.integrableOn_mul_cpow_of_isBigO` and
  `TauCeti.LSeries.norm_integral_mul_cpow_le_of_bound`: holomorphy, absolute convergence and an
  explicit bound for `∫ t in Set.Ioi 1, g t * t ^ (-(s + 1))` with a general kernel `g` that is
  locally integrable on `[1, ∞)` and `O(t ^ r)` (or bounded) at infinity. The partial-sum results
  below are their instances at the step function `g t = A(⌊t⌋₊)`.
* `TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO`: under the bound `A(n) = O(n ^ r)`,
  the function `s ↦ s * ∫ t in Set.Ioi 1, A(⌊t⌋₊) * t ^ (-(s + 1))` is
  complex-differentiable on `{s | r < s.re}`.
* `TauCeti.LSeries.integrableOn_sum_mul_cpow_of_isBigO`: under the same bound the integral
  converges absolutely on `{s | r < s.re}`.
* `TauCeti.LSeries.norm_mul_integral_le_of_bound`: uniformly bounded partial sums give the
  explicit bound `C * ‖s‖ / s.re` on `Re(s) > 0`.
* `TauCeti.LSeries.exists_differentiableOn_eq_LSeries_sub_div_of_isBigO`: if instead the partial
  sums are `κ n + O(n ^ r)` and `LSeries f` converges absolutely on `Re s > 1`, then
  `LSeries f s - κ / (s - 1)` continues holomorphically from `Re s > 1` to `Re s > r`. When
  `r < 1` this half-plane contains `s = 1`, so there `LSeries f` has at most a simple pole, at
  `s = 1`, with residue `κ`.
-/

public section

open Finset Filter MeasureTheory Complex Asymptotics

open scoped Topology

namespace TauCeti.LSeries

/-! ### Integrals of a general kernel against `t ^ (-(s + 1))` -/

/-- The integral `∫ t in Set.Ioi 1, g t * t ^ (-(s + 1))` is the Mellin transform at `-s` of `g`
restricted to `[1, ∞)`. -/
private theorem integral_Ioi_one_eq_mellin_indicator (g : ℝ → ℂ) (s : ℂ) :
    ∫ t in Set.Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(s + 1)) =
      mellin ((Set.Ici 1).indicator g) (-s) := by
  have hEq : Set.EqOn (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) • (Set.Ici 1).indicator g t)
      ((Set.Ici (1 : ℝ)).indicator fun t ↦ g t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 0) := by
    intro t _
    dsimp only
    by_cases h1 : t ∈ Set.Ici (1 : ℝ)
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1, smul_eq_mul, mul_comm, neg_add']
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1, smul_zero]
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hEq,
    setIntegral_indicator measurableSet_Ici,
    Set.inter_eq_right.mpr (Set.Ici_subset_Ioi.mpr zero_lt_one), integral_Ici_eq_integral_Ioi]

private theorem locallyIntegrableOn_indicator_Ici_one {g : ℝ → ℂ}
    (hg : LocallyIntegrableOn g (Set.Ici 1)) :
    LocallyIntegrableOn ((Set.Ici 1).indicator g) (Set.Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k _ hk
  rw [integrableOn_indicator_iff measurableSet_Ici.nullMeasurableSet]
  exact (locallyIntegrableOn_iff isClosed_Ici.isLocallyClosed).mp hg _ Set.inter_subset_left
    (hk.inter_left isClosed_Ici)

private theorem isBigO_indicator_Ici_one_atTop {g : ℝ → ℂ} {r : ℝ}
    (hO : g =O[atTop] fun t ↦ t ^ r) :
    (Set.Ici 1).indicator g =O[atTop] fun t ↦ t ^ r := by
  refine hO.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with t ht
  exact (Set.indicator_of_mem (Set.mem_Ici.mpr ht) g).symm

private theorem isBigO_indicator_Ici_one_nhdsGT_zero (g : ℝ → ℂ) (b : ℝ) :
    (Set.Ici 1).indicator g =O[𝓝[>] 0] fun t : ℝ ↦ t ^ b := by
  refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
  exact (Set.indicator_of_notMem (not_le.mpr ht.2) g).symm

/-- **Holomorphy of an integral against `t ^ (-(s + 1))`.** If `g` is locally integrable on
`[1, ∞)` and `O(t ^ r)` at infinity, then `s ↦ ∫ t in Set.Ioi 1, g t * t ^ (-(s + 1))` is
complex-differentiable on the half-plane `r < Re s`. -/
theorem differentiableOn_integral_mul_cpow_of_isBigO {g : ℝ → ℂ} {r : ℝ}
    (hg : LocallyIntegrableOn g (Set.Ici 1)) (hO : g =O[atTop] fun t ↦ t ^ r) :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∫ t in Set.Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(s + 1)))
      {s | r < s.re} := by
  intro s hs
  have hmellin : DifferentiableAt ℂ (fun z : ℂ ↦ mellin ((Set.Ici 1).indicator g) (-z)) s :=
    (mellin_differentiableAt_of_isBigO_rpow (a := -r) (locallyIntegrableOn_indicator_Ici_one hg)
      (by rw [neg_neg]; exact isBigO_indicator_Ici_one_atTop hO) (by simpa using hs)
      (isBigO_indicator_Ici_one_nhdsGT_zero g _) (sub_one_lt (-s).re)).comp s
      differentiableAt_id.neg
  simp_rw [integral_Ioi_one_eq_mellin_indicator]
  exact hmellin.differentiableWithinAt

/-- If `g` is locally integrable on `[1, ∞)` and `O(t ^ r)` at infinity, then
`t ↦ g t * t ^ (-(s + 1))` is integrable on `(1, ∞)` for `r < Re s`. -/
theorem integrableOn_mul_cpow_of_isBigO {g : ℝ → ℂ} {r : ℝ}
    (hg : LocallyIntegrableOn g (Set.Ici 1)) (hO : g =O[atTop] fun t ↦ t ^ r) {s : ℂ}
    (hs : r < s.re) :
    IntegrableOn (fun t : ℝ ↦ g t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hconv : MellinConvergent ((Set.Ici 1).indicator g) (-s) :=
    mellinConvergent_of_isBigO_rpow (a := -r) (locallyIntegrableOn_indicator_Ici_one hg)
      (by rw [neg_neg]; exact isBigO_indicator_Ici_one_atTop hO) (by simpa using hs)
      (isBigO_indicator_Ici_one_nhdsGT_zero g _) (sub_one_lt (-s).re)
  refine (hconv.mono_set (Set.Ioi_subset_Ioi zero_le_one)).congr_fun (fun t ht ↦ ?_)
    measurableSet_Ioi
  dsimp only
  rw [Set.indicator_of_mem (Set.mem_Ici.mpr (Set.mem_Ioi.mp ht).le), smul_eq_mul, mul_comm,
    neg_add']

/-- If `‖g t‖ ≤ C` on `(1, ∞)`, then `‖∫ t in Set.Ioi 1, g t * t ^ (-(s + 1))‖ ≤ C / s.re` on
`Re(s) > 0`. -/
theorem norm_integral_mul_cpow_le_of_bound {g : ℝ → ℂ} {C : ℝ}
    (hg : ∀ t ∈ Set.Ioi (1 : ℝ), ‖g t‖ ≤ C) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(s + 1))‖ ≤ C / s.re := by
  calc
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), C * t ^ (-(s.re + 1)) := by
      refine norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt
        (by linarith : -(s.re + 1) < -1) zero_lt_one).const_mul C) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht)]
      simp only [neg_re, add_re, one_re]
      exact mul_le_mul_of_nonneg_right (hg t ht) (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
    _ = C / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
        Real.one_rpow]
      ring

/-! ### The partial-summation integral -/

/-- **Holomorphy of the partial-summation integral.** If the partial sums
`∑ k ∈ Icc 1 n, f k` are `O(n ^ r)`, then
`s ↦ s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1))` is complex-differentiable
on the half-plane `r < Re s`.

By Mathlib's `LSeries_eq_mul_integral` this function agrees with `LSeries f` wherever the series
converges in that half-plane, so it is an analytic continuation of `LSeries f` to `Re s > r`. -/
theorem differentiableOn_mul_integral_of_isBigO (f : ℕ → ℂ) {r : ℝ}
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)))
      {s | r < s.re} :=
  differentiableOn_id.mul <| differentiableOn_integral_mul_cpow_of_isBigO
    ((locallyIntegrableOn_sum_Icc_natFloor f 1).mono_set (Set.Ici_subset_Ici.mpr zero_le_one))
    hO.comp_natFloor_rpow

/-- If the partial sums `∑ k ∈ Icc 1 n, f k` are `O(n ^ r)`, the partial-summation integral
converges absolutely on the half-plane `r < Re s`. -/
theorem integrableOn_sum_mul_cpow_of_isBigO (f : ℕ → ℂ) {r : ℝ}
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) {s : ℂ} (hs : r < s.re) :
    IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)))
      (Set.Ioi 1) :=
  integrableOn_mul_cpow_of_isBigO
    ((locallyIntegrableOn_sum_Icc_natFloor f 1).mono_set (Set.Ici_subset_Ici.mpr zero_le_one))
    hO.comp_natFloor_rpow hs

/-- If partial sums are bounded by `C`, their partial-summation continuation has norm at most
`C * ‖s‖ / s.re` on `Re(s) > 0`. -/
theorem norm_mul_integral_le_of_bound (f : ℕ → ℂ) {C : ℝ}
    (hf : ∀ n, ‖∑ k ∈ Icc 1 n, f k‖ ≤ C) {s : ℂ} (hs : 0 < s.re) :
    ‖s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) *
      (t : ℂ) ^ (-(s + 1))‖ ≤ C * ‖s‖ / s.re := by
  rw [norm_mul, mul_comm C, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_integral_mul_cpow_le_of_bound (fun _ _ ↦ hf _) hs)
    (norm_nonneg _)

/-- **Continuation of an L-series with its pole at `s = 1` removed.** If the partial sums
`∑ k ∈ Icc 1 n, f k` are `κ n + O(n ^ r)` and `LSeries f` converges absolutely on
`Re s > 1`, then there is a function holomorphic on the half-plane `Re s > r` that agrees with
`LSeries f s - κ / (s - 1)` on `Re s > 1`. When `r < 1`, so that the half-plane contains `s = 1`,
`LSeries f` therefore continues meromorphically to `Re s > r` with at most a simple pole, at
`s = 1`, of residue `κ`.

`TauCeti.exists_differentiableOn_eq_dedekindZeta_sub` is the Dedekind-zeta instance. -/
theorem exists_differentiableOn_eq_LSeries_sub_div_of_isBigO (f : ℕ → ℂ) (κ : ℂ) {r : ℝ}
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k - κ * n) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hf : ∀ s : ℂ, 1 < s.re → LSeriesSummable f s) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | r < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = LSeries f s - κ / (s - 1) := by
  have hsum (n : ℕ) : ∑ k ∈ Icc 1 n, (f - κ • (1 : ℕ → ℂ)) k = ∑ k ∈ Icc 1 n, f k - κ * n := by
    simp [sum_sub_distrib, mul_comm]
  have hO' : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, (f - κ • (1 : ℕ → ℂ)) k) =O[atTop]
      fun n ↦ (n : ℝ) ^ r := by
    simpa only [hsum] using hO
  -- Mathlib's integral representation needs a nonnegative exponent, so weaken `r` to `max r 0`.
  have hO₀ : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, (f - κ • (1 : ℕ → ℂ)) k) =O[atTop]
      fun n ↦ (n : ℝ) ^ max r 0 := by
    refine hO'.trans <| .of_bound' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le (mod_cast hn) (le_max_left r 0)
  -- Subtracting `κ` times the coefficients of the Riemann zeta function leaves partial sums
  -- `O(n ^ r)`, so the partial-summation integral of `f - κ` continues its `L`-series; add
  -- `κ (ζ(s) - 1/(s-1))`, which is entire (Mathlib's `riemannZeta₀`).
  -- The formula below is only used on `Re s > r`; elsewhere `G` is the required value itself.
  set F : ℂ → ℂ := fun s ↦ s * (∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Icc 1 ⌊t⌋₊, (f - κ • (1 : ℕ → ℂ)) k) * (t : ℂ) ^ (-(s + 1))) + κ * riemannZeta₀ s
    with hF
  have hdiff : DifferentiableOn ℂ F {s | r < s.re} :=
    (differentiableOn_mul_integral_of_isBigO _ hO').fun_add
      (differentiable_riemannZeta₀.const_mul _).differentiableOn
  refine ⟨fun s ↦ if r < s.re then F s else LSeries f s - κ / (s - 1),
    hdiff.congr fun s (hs : r < s.re) ↦ by simp only [hs, ↓reduceIte], fun s hs ↦ ?_⟩
  by_cases hrs : r < s.re
  swap
  · simp [hrs]
  have hs1 : LSeriesSummable (κ • (1 : ℕ → ℂ)) s :=
    LSeriesSummable.smul _ (LSeriesSummable_one_iff.mpr hs)
  have hs0 : s ≠ 1 := fun h ↦ by simp [h] at hs
  simp only [hrs, ↓reduceIte, hF]
  rw [← LSeries_eq_mul_integral _ (le_max_right r 0) (max_lt hrs (by linarith))
      ((hf s hs).sub hs1) hO₀,
    LSeries_sub (hf s hs) hs1, LSeries_smul, LSeries_one_eq_riemannZeta hs,
    riemannZeta_eq_inv_sub_add hs0]
  ring

end TauCeti.LSeries
