/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Analytic continuation of an L-series from a bound on its partial sums

If the partial sums `A(n) = ∑_{k=1}^n f k` of a sequence `f : ℕ → ℂ` are `O(n ^ r)` for some
`0 ≤ r`, Mathlib's `LSeries_eq_mul_integral` (from `Mathlib/NumberTheory/LSeries/SumCoeff.lean`)
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

* `TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO`: under the bound `A(n) = O(n ^ r)`
  with `0 ≤ r`, the function `s ↦ s * ∫ t in Set.Ioi 1, A(⌊t⌋₊) * t ^ (-(s + 1))` is
  complex-differentiable on `{s | r < s.re}`.
-/

public section

open Finset Filter MeasureTheory Complex Asymptotics

open scoped Topology

namespace TauCeti.LSeries

/-- The step function `t ↦ ∑_{k=1}^{⌊t⌋₊} f k` vanishes below `1`. -/
private theorem sum_Icc_one_natFloor_eq_zero (f : ℕ → ℂ) {t : ℝ} (ht : t < 1) :
    ∑ k ∈ Icc 1 ⌊t⌋₊, f k = 0 := by
  simp [Nat.floor_eq_zero.mpr ht]

/-- The integral in `LSeries_eq_mul_integral` is a Mellin transform of the partial-sum step
function, evaluated at `-s`. -/
private theorem integral_Ioi_one_eq_mellin (f : ℕ → ℂ) (s : ℂ) :
    ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) =
      mellin (fun t : ℝ ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, f k) (-s) := by
  set A : ℝ → ℂ := fun t ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, f k
  have hEq : Set.EqOn (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) • A t)
      ((Set.Ici (1 : ℝ)).indicator fun t ↦ A t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 0) := by
    intro t _
    dsimp only
    by_cases h1 : 1 ≤ t
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr h1), smul_eq_mul, mul_comm, neg_add']
    · have hA : A t = 0 := sum_Icc_one_natFloor_eq_zero f (not_le.mp h1)
      rw [Set.indicator_of_notMem (by simpa using h1), hA, smul_zero]
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hEq,
    setIntegral_indicator measurableSet_Ici,
    Set.inter_eq_right.mpr (Set.Ici_subset_Ioi.mpr zero_lt_one), integral_Ici_eq_integral_Ioi]

/-- **Holomorphy of the partial-summation integral.** If the partial sums
`∑ k ∈ Icc 1 n, f k` are `O(n ^ r)` for some `0 ≤ r`, then
`s ↦ s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1))` is complex-differentiable
on the half-plane `r < Re s`.

By Mathlib's `LSeries_eq_mul_integral` this function agrees with `LSeries f` wherever the series
converges in that half-plane, so it is an analytic continuation of `LSeries f` to `Re s > r`. -/
theorem differentiableOn_mul_integral_of_isBigO (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)))
      {s | r < s.re} := by
  set A : ℝ → ℂ := fun t ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, f k
  have hloc : LocallyIntegrableOn A (Set.Ioi 0) := by
    simpa [A] using (locallyIntegrableOn_mul_sum_Icc f le_rfl (m := 1)
      (g := fun _ ↦ (1 : ℂ)) (locallyIntegrableOn_const 1)).mono_set Set.Ioi_subset_Ici_self
  have htop : A =O[atTop] (· ^ (-(-r))) := by
    simp_rw [neg_neg]
    exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
      isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0)
  have hbot (b : ℝ) : A =O[𝓝[>] 0] (· ^ (-b)) := by
    refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact (sum_Icc_one_natFloor_eq_zero f ht.2).symm
  intro s hs
  have hmellin : DifferentiableAt ℂ (fun z : ℂ ↦ mellin A (-z)) s :=
    (mellin_differentiableAt_of_isBigO_rpow hloc htop (by simpa using hs) (hbot ((-s).re - 1))
      (by linarith)).comp s differentiableAt_id.neg
  simp_rw [integral_Ioi_one_eq_mellin]
  exact (differentiableAt_id.mul hmellin).differentiableWithinAt

end TauCeti.LSeries
