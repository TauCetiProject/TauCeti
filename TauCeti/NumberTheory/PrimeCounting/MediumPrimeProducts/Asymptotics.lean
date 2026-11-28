/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.NumberTheory.PrimeCounting.MediumPrimeProducts.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics
import TauCeti.NumberTheory.PrimeCounting.Asymptotics

/-!
# The number of products of `m` primes in `[x / 2, x]`

Let `k(x)` be the number of primes in `[x / 2, x]`. It differs from `π(x) - π(x / 2)` by at most
one (`TauCeti.primeCounting_le_card_mediumPrimes_add_primeCounting` and
`TauCeti.card_mediumPrimes_add_primeCounting_le_primeCounting_add_one`), and the prime number
theorem at the two scales `x` and `x / 2`, in the form
`TauCeti.tendsto_primeCounting_mul_sub_mul_div`, gives `(π(x) - π(x / 2)) / (x / log x) → 1 / 2`.
Hence `k(x) ∼ x / (2 log x)`.

The set `N_m(x)` of products of `m` distinct primes of `[x / 2, x]` has `k(x).choose m` elements
(`TauCeti.card_mediumPrimeProducts`), and Mathlib's `isEquivalent_choose` gives
`n.choose m ∼ n ^ m / m!` for fixed `m`. Composing with `k(x) → ∞`, it follows that

  `#N_m(x) ∼ (x / log x) ^ m / (2 ^ m * m!)`

as `x → ∞`, for each fixed `m`.

## Main results

* `TauCeti.tendsto_card_mediumPrimes_div_div_log`, `TauCeti.isEquivalent_card_mediumPrimes`:
  `k(x) / (x / log x) → 1 / 2`, that is `k(x) ∼ x / (2 log x)`.
* `TauCeti.tendsto_card_mediumPrimes_atTop`: `k(x)` tends to infinity.
* `TauCeti.isEquivalent_card_mediumPrimeProducts`: `#N_m(x) ∼ (x / log x) ^ m / (2 ^ m * m!)`.

## References

* L. Bary-Soroker, D. Koukoulopoulos and G. Kozma, *Irreducibility of random polynomials: general
  measures*, arXiv:2007.14567v3, equation (3.4).
-/

public section

open Filter Asymptotics Finset Nat
open scoped Topology

namespace TauCeti

/-- The number of primes in `[x / 2, x]`, divided by `x / log x`, tends to `1 / 2`. -/
theorem tendsto_card_mediumPrimes_div_div_log :
    Tendsto (fun x : ℝ ↦ (#(mediumPrimes x) : ℝ) / (x / Real.log x)) atTop (𝓝 (1 / 2)) := by
  have hden : Tendsto (fun x : ℝ ↦ x / Real.log x) atTop atTop := TauCeti.Real.tendsto_div_log_atTop
  have hD : Tendsto (fun x : ℝ ↦ ((primeCounting ⌊x⌋₊ : ℝ) - primeCounting ⌊x / 2⌋₊) /
      (x / Real.log x)) atTop (𝓝 (1 / 2)) := by
    have h := tendsto_primeCounting_mul_sub_mul_div (a := 1 / 2) (b := 1) (by norm_num) zero_le_one
    have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h1] at h
    simpa only [one_mul, one_div, inv_mul_eq_div] using h
  have hD1 : Tendsto (fun x : ℝ ↦ ((primeCounting ⌊x⌋₊ : ℝ) - primeCounting ⌊x / 2⌋₊) /
      (x / Real.log x) + (x / Real.log x)⁻¹) atTop (𝓝 (1 / 2)) := by
    simpa using hD.add hden.inv_tendsto_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hD hD1 ?_ ?_
  · filter_upwards [hden.eventually_gt_atTop 0] with x hx
    have h : (primeCounting ⌊x⌋₊ : ℝ) ≤ #(mediumPrimes x) + primeCounting ⌊x / 2⌋₊ :=
      mod_cast primeCounting_le_card_mediumPrimes_add_primeCounting x
    exact div_le_div_of_nonneg_right (by linarith) hx.le
  · filter_upwards [hden.eventually_gt_atTop 0] with x hx
    have h : (#(mediumPrimes x) : ℝ) + primeCounting ⌊x / 2⌋₊ ≤ primeCounting ⌊x⌋₊ + 1 :=
      mod_cast card_mediumPrimes_add_primeCounting_le_primeCounting_add_one x
    rw [← one_div, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hx.le

/-- **The prime number theorem in `[x / 2, x]`**: the number of primes in `[x / 2, x]` is
asymptotic to `x / (2 log x)`. -/
theorem isEquivalent_card_mediumPrimes :
    (fun x : ℝ ↦ (#(mediumPrimes x) : ℝ)) ~[atTop] fun x ↦ x / (2 * Real.log x) := by
  have h2 : Tendsto (fun x : ℝ ↦ 2 * ((#(mediumPrimes x) : ℝ) / (x / Real.log x))) atTop
      (𝓝 1) := by
    simpa using tendsto_card_mediumPrimes_div_div_log.const_mul 2
  refine isEquivalent_of_tendsto_one (h2.congr fun x ↦ ?_)
  simp only [Pi.div_apply, div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- The number of primes in `[x / 2, x]` tends to infinity with `x`. -/
theorem tendsto_card_mediumPrimes_atTop :
    Tendsto (fun x : ℝ ↦ #(mediumPrimes x)) atTop atTop := by
  have hden : Tendsto (fun x : ℝ ↦ x / (2 * Real.log x)) atTop atTop := by
    have h := TauCeti.Real.tendsto_div_log_atTop.atTop_div_const (zero_lt_two' ℝ)
    refine h.congr fun x ↦ ?_
    rw [div_div, mul_comm]
  exact tendsto_natCast_atTop_iff.1 (isEquivalent_card_mediumPrimes.symm.tendsto_atTop hden)

/-- For each fixed `m`, the number of products of `m` distinct primes in `[x / 2, x]` is
asymptotic to `(x / log x) ^ m / (2 ^ m * m!)`. -/
theorem isEquivalent_card_mediumPrimeProducts (m : ℕ) :
    (fun x : ℝ ↦ (#(mediumPrimeProducts x m) : ℝ)) ~[atTop]
      fun x ↦ (x / Real.log x) ^ m / (2 ^ m * m.factorial) := by
  have hchoose := (isEquivalent_choose m).comp_tendsto tendsto_card_mediumPrimes_atTop
  have hpow := (isEquivalent_card_mediumPrimes.pow m).div
    (IsEquivalent.refl (u := fun _ : ℝ ↦ (m.factorial : ℝ)) (l := atTop))
  refine ((hchoose.trans hpow).congr_left ?_).congr_right ?_
  · exact Eventually.of_forall fun x ↦ by
      simp only [Function.comp_apply, card_mediumPrimeProducts]
  · exact Eventually.of_forall fun x ↦ by
      simp only [Pi.div_apply, Pi.pow_apply, div_eq_mul_inv, mul_pow, mul_inv, inv_pow]
      ring

end TauCeti
