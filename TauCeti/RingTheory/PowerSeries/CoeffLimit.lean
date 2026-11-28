/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.RingTheory.PowerSeries.Rescale
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp

/-!
# Coefficientwise limits of power series

This file records `PowerSeries.tendsto_coeff_of_mul_eq` (passing a coefficientwise limit through
`F i * B i = A i` when `constantCoeff (B i) = 1` and `constantCoeff B₀ = 1`) and
`PowerSeries.tendsto_coeff_one_add_div_pow` (`(1 + C (c / N) * X) ^ N → rescale c (exp 𝕜)`).
-/

public section

namespace PowerSeries

open Filter
open scoped Nat Topology

/-- Coefficientwise convergence passes through `F i * B i = A i` when `B i` and `B₀` have
constant coefficient `1`. -/
theorem tendsto_coeff_of_mul_eq {R ι : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    {l : Filter ι} {F A B : ι → R⟦X⟧} {L A₀ B₀ : R⟦X⟧}
    (hmul : ∀ i, F i * B i = A i) (hmul₀ : L * B₀ = A₀)
    (hB_const : ∀ i, constantCoeff (B i) = 1) (hB₀_const : constantCoeff B₀ = 1)
    (hA : ∀ k, Tendsto (fun i ↦ coeff k (A i)) l (𝓝 (coeff k A₀)))
    (hB : ∀ k, Tendsto (fun i ↦ coeff k (B i)) l (𝓝 (coeff k B₀)))
    (k : ℕ) : Tendsto (fun i ↦ coeff k (F i)) l (𝓝 (coeff k L)) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hsolve (P Q : R⟦X⟧) (hQ : constantCoeff Q = 1) :
        coeff k P = coeff k (P * Q) - ∑ i ∈ Finset.range k, coeff i P * coeff (k - i) Q := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ coeff i P * coeff j Q)
          k, Finset.sum_range_succ, Nat.sub_self, coeff_zero_eq_constantCoeff, hQ, mul_one,
        add_sub_cancel_left]
    simp_rw [fun i ↦ hsolve (F i) (B i) (hB_const i), hmul, hsolve L B₀ hB₀_const, hmul₀]
    exact (hA k).sub (tendsto_finsetSum _ fun i hi ↦
      (ih i (Finset.mem_range.mp hi)).mul (hB (k - i)))

/-- Coefficientwise convergence of `(1 + C (c / N) * X) ^ N` to `rescale c (exp 𝕜)`. -/
theorem tendsto_coeff_one_add_div_pow {𝕜 : Type*} [Field 𝕜] [Algebra ℚ 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] [ContinuousSMul ℚ≥0 𝕜] (c : 𝕜) (k : ℕ) :
    Tendsto (fun N : ℕ ↦ coeff k ((1 + C (c / N) * X) ^ N))
      atTop (𝓝 (coeff k (rescale c (exp 𝕜)))) := by
  have : CharZero 𝕜 := charZero_of_inj_zero fun n hn ↦
    Nat.cast_eq_zero.mp ((algebraMap ℚ 𝕜).injective (by simpa using hn))
  have hcoeff : ∀ᶠ N : ℕ in atTop, coeff k ((1 + C (c / N) * X) ^ N) =
      (c ^ k / (k ! : 𝕜)) * ∏ i ∈ Finset.range k, (1 - (i : 𝕜) * (N : 𝕜)⁻¹) := by
    filter_upwards [eventually_ge_atTop (max k 1)] with N hN
    have hkN : k ≤ N := (le_max_left k 1).trans hN
    have hN0 : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hk0 : (k ! : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hpow : (1 + C (c / N) * X) ^ N =
        ∑ i ∈ Finset.range (N + 1), C ((N.choose i : 𝕜) * (c / N) ^ i) * X ^ i := by
      rw [add_comm 1 _, add_pow]; refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [one_pow, mul_one, mul_pow, ← map_natCast C, ← map_pow, mul_right_comm, ← map_mul,
        mul_comm ((c / ↑N) ^ i)]
    have hdesc : (k ! : 𝕜) * (N.choose k : 𝕜) = ∏ i ∈ Finset.range k, ((N : 𝕜) - i) := by
      have h := congrArg ((↑) : ℕ → 𝕜) (Nat.descFactorial_eq_factorial_mul_choose N k)
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_mul, Nat.cast_prod] at h; exact h.symm.trans
        (Finset.prod_congr rfl fun i hi ↦ Nat.cast_sub ((Finset.mem_range.mp hi).le.trans hkN))
    have hprod : ∏ i ∈ Finset.range k, (1 - (i : 𝕜) * (N : 𝕜)⁻¹) =
        (∏ i ∈ Finset.range k, ((N : 𝕜) - i)) / (N : 𝕜) ^ k := by
      have hNk : (N : 𝕜) ^ k = ∏ _i ∈ Finset.range k, (N : 𝕜) := by simp
      rw [hNk, ← Finset.prod_div_distrib]; exact Finset.prod_congr rfl fun i _ ↦ by field_simp
    rw [hpow, map_sum]; simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range,
      Nat.lt_succ_iff.mpr hkN, ↓reduceIte, hprod, ← hdesc, div_pow]; field_simp
  have h1 : Tendsto (fun N : ℕ ↦ ∏ i ∈ Finset.range k, (1 - (i : 𝕜) * (N : 𝕜)⁻¹)) atTop (𝓝 1) := by
    simpa using tendsto_finsetProd (Finset.range k) fun i _ ↦
      (tendsto_const_nhds (x := (1 : 𝕜))).sub
        ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := 𝕜)).const_mul (i : 𝕜))
  simpa only [mul_one, coeff_rescale, coeff_exp, map_div₀, map_one, map_natCast, mul_one_div] using
    (h1.const_mul (c ^ k / (k ! : 𝕜))).congr' (EventuallyEq.symm hcoeff)

end PowerSeries
