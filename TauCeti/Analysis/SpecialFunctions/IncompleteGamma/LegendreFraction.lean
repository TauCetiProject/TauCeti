/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.Algebra.ContinuedFractions.ReductionOfOrder
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.KummerLaplace
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Upper
import TauCeti.Analysis.Asymptotics.Sum.Divergence
import TauCeti.Analysis.Asymptotics.Sum.Telescoping
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral

/-!
# Legendre's continued fraction for the upper incomplete Gamma function

For `z ∈ Complex.slitPlane`, Legendre's continued fraction for the normalized upper incomplete
Gamma combination `z^{-a} e^z Γ(a, z) = K(0, a - 1; z)` has head `0`, partial denominators
`b_n = 1`, and partial numerators `a₁ = z⁻¹`, `a_{2k} = (k - a) z⁻¹`, `a_{2k+1} = k z⁻¹`
(`k ≥ 1`; non-terminating when `a ∉ {1, 2, ...}`). In terms of the rotated Kummer-Laplace
integrals `Complex.kummerLaplace`, the sequence `(f_n)_{n ≥ 0}` defined by
* `f₀ = 1`,
* `f_{2k+1} = -(1 - a)_k z^{-k} K(k, a - 1 - k; z)`,
* `f_{2k+2} = (1 - a)_{k+1} z^{-(k+1)} K(k, a - 2 - k; z)`

satisfies the associated three-term recurrence `f_{n+2} = f_{n+1} + a_{n+1} f_n` on
`Complex.slitPlane` with initial values `f₀ = 1` and `f₁ = -K(0, a - 1; z)`. In Gautschi's
analysis of three-term recurrence relations, this sequence is the minimal solution used to apply
Pincherle's theorem in the non-terminating regime `a ∉ {1, 2, ...}`; its eventual nonvanishing
follows from the saddle-point asymptotics in
`TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Asymptotics`.

Minimality is proved through the reduction-of-order series
`∑ (-1)^m (a₁ ⋯ aₘ) / (f(m) f(m + 1))`. With `K_k = K(k, a - 1 - k; z)`, its odd terms are
`k! / ((1 - a)_{k+1} K_k K(k, a - 2 - k; z))` and its consecutive pairs collapse, by the contiguous
relation `K_k - K(k, a - 2 - k; z) = K_{k+1}`, to `-k! / ((1 - a)_{k+1} K_k K_{k+1})`. The
saddle-point asymptotic `K_k ~ √π e^{z/2} z^{-a/2-1/4} k^{a/2-1/4} e^{-2√(kz)}` and Euler's limit
for `Γ(1 - a)` make the pairs asymptotic to the forward differences of a multiple of
`e^{4√(kz)}`. A discrete Stolz–Cesàro argument (`TauCeti.isLittleO_sum_range_sub`) then shows
that both the odd and the even partial sums grow like `e^{4√(kz)}`. The reduction-of-order
criterion `TauCeti.tendsto_convs_contFrac_of_tendsto_norm_sum` gives convergence of the continued
fraction to `-f₁ / f₀ = K(0, a - 1; z)`, which the identity theorem identifies with
`z^{-a} e^z Γ(a, z)` on the slit plane (DLMF 8.9.2).

## Main definitions

* `Complex.upperIncompleteGammaContFracPartNum a z n` — the `n`-th partial numerator of Legendre's
  continued fraction for `z^{-a} e^z Γ(a, z)`.
* `Complex.upperIncompleteGammaContFracSolution a z n` — the Kummer-Laplace solution sequence
  `f_n` of the associated three-term recurrence on `Complex.slitPlane`, normalized by `f₀ = 1`.

## Main results

* `Complex.upperIncompleteGammaContFracPartNum_ne_zero_iff` —
  `upperIncompleteGammaContFracPartNum a z n ≠ 0` iff `z ≠ 0` and `(Even n → a ≠ (n / 2 : ℕ))`.
* `Complex.upperIncompleteGammaContFracSolution_zero`,
  `Complex.upperIncompleteGammaContFracSolution_one` — initial values `f₀ = 1` and
  `f₁ = -kummerLaplace 0 (a - 1) z`.
* `Complex.upperIncompleteGammaContFracSolution_add_two` — on `slitPlane`,
  `f (n + 2) = f (n + 1) + upperIncompleteGammaContFracPartNum a z (n + 1) * f n`.
* `Complex.eventually_upperIncompleteGammaContFracSolution_ne_zero` — for `z ∈ slitPlane` and
  `a ≠ m + 1` (`m : ℕ`), `upperIncompleteGammaContFracSolution a z n ≠ 0` eventually as `n → ∞`.
* `Complex.tendsto_norm_sum_upperIncompleteGammaContFracSolution_atTop`: for `z ∈ slitPlane` and
  `a ∉ {1, 2, …}`, the reduction-of-order partial sums of the solution tend to infinity in norm,
  so the solution is minimal.
* `Complex.kummerLaplace_zero_eq_cpow_neg_mul_exp_mul_upperIncompleteGamma`: on `slitPlane`,
  `K(0, a - 1; z) = z^{-a} e^z Γ(a, z)`.
* `Complex.tendsto_convs_upperIncompleteGamma`: DLMF 8.9.2: for `z ∈ slitPlane` and
  `a ∉ {1, 2, …}`, the continued fraction has eventually nonzero denominators and its convergents
  tend to `z^{-a} e^z Γ(a, z)`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.9](https://dlmf.nist.gov/8.9).
* W. Gautschi, *Computational aspects of three-term recurrence relations*, SIAM Rev. 9 (1967),
  24–82.
-/

public section

noncomputable section

open Filter Polynomial
open scoped Topology

namespace Complex

/-- The `n`-th partial numerator of Legendre's continued fraction for `z^{-a} e^z Γ(a, z)`:
`a₁ = z⁻¹`, `a_{2k} = (k - a) * z⁻¹` (`k ≥ 1`), and `a_{2k+1} = k * z⁻¹` (`k ≥ 1`), paired with
partial denominators `b_n = 1` and head `b₀ = 0`. -/
def upperIncompleteGammaContFracPartNum (a z : ℂ) (n : ℕ) : ℂ :=
  if n = 1 then z⁻¹
  else if Even n then (((n / 2 : ℕ) : ℂ) - a) * z⁻¹
  else ((n / 2 : ℕ) : ℂ) * z⁻¹

/-- Defining formula for `Complex.upperIncompleteGammaContFracPartNum`. -/
theorem upperIncompleteGammaContFracPartNum_def (a z : ℂ) (n : ℕ) :
    upperIncompleteGammaContFracPartNum a z n =
      if n = 1 then z⁻¹
      else if Even n then (((n / 2 : ℕ) : ℂ) - a) * z⁻¹
      else ((n / 2 : ℕ) : ℂ) * z⁻¹ := (rfl)

/-- Zeroth index evaluation `upperIncompleteGammaContFracPartNum a z 0 = -a * z⁻¹`. -/
@[simp]
theorem upperIncompleteGammaContFracPartNum_zero (a z : ℂ) :
    upperIncompleteGammaContFracPartNum a z 0 = -a * z⁻¹ := by
  simp [upperIncompleteGammaContFracPartNum]

/-- First partial numerator `a₁ = z⁻¹` of Legendre's continued fraction. -/
@[simp]
theorem upperIncompleteGammaContFracPartNum_one (a z : ℂ) :
    upperIncompleteGammaContFracPartNum a z 1 = z⁻¹ := by
  simp [upperIncompleteGammaContFracPartNum]

/-- Even partial numerator `a_{2k+2} = (k + 1 - a) * z⁻¹` of Legendre's continued fraction. -/
@[simp]
theorem upperIncompleteGammaContFracPartNum_two_mul_add_two (a z : ℂ) (k : ℕ) :
    upperIncompleteGammaContFracPartNum a z (2 * k + 2) = ((k : ℂ) + 1 - a) * z⁻¹ := by
  rw [upperIncompleteGammaContFracPartNum, ite_eq_right (by omega), ite_eq_left ⟨k + 1, by ring⟩,
    Nat.mul_add_div zero_lt_two]
  norm_num

/-- Odd partial numerator `a_{2k+3} = (k + 1) * z⁻¹` of Legendre's continued fraction. -/
@[simp]
theorem upperIncompleteGammaContFracPartNum_two_mul_add_three (a z : ℂ) (k : ℕ) :
    upperIncompleteGammaContFracPartNum a z (2 * k + 3) = ((k : ℂ) + 1) * z⁻¹ := by
  rw [upperIncompleteGammaContFracPartNum, ite_eq_right (by omega),
    ite_eq_right (by simp [parity_simps]), Nat.mul_add_div zero_lt_two]
  norm_num

/-- Exact nonvanishing characterization of `upperIncompleteGammaContFracPartNum a z n`: it is
nonzero if and only if `z ≠ 0` and, when `n` is even, `a ≠ (n / 2 : ℕ)`. -/
theorem upperIncompleteGammaContFracPartNum_ne_zero_iff {a z : ℂ} {n : ℕ} :
    upperIncompleteGammaContFracPartNum a z n ≠ 0 ↔ z ≠ 0 ∧ (Even n → a ≠ (n / 2 : ℕ)) := by
  rcases n with _ | _ | n
  · simp [and_comm]
  · simp
  · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [add_assoc (2 * k) 1 1, upperIncompleteGammaContFracPartNum_two_mul_add_two,
        Nat.mul_add_div zero_lt_two]
      simp [parity_simps, sub_eq_zero, eq_comm (a := a), and_comm]
    · have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rw [add_assoc (2 * k) 1 1, add_assoc (2 * k) 2 1,
        upperIncompleteGammaContFracPartNum_two_mul_add_three]
      simp [parity_simps, hk1]

/-- Explicit Kummer-Laplace solution sequence of the three-term recurrence
`f (n + 2) = f (n + 1) + upperIncompleteGammaContFracPartNum a z (n + 1) * f n` on
`Complex.slitPlane` associated with Legendre's continued fraction for `z^{-a} e^z Γ(a, z)`,
normalized by `f 0 = 1`:
* `f 0 = 1`,
* `f (2k + 1) = -(1 - a)_k * z⁻¹ ^ k * kummerLaplace k (a - 1 - k) z`,
* `f (2k + 2) = (1 - a)_{k+1} * z⁻¹ ^ (k + 1) * kummerLaplace k (a - 2 - k) z`. -/
def upperIncompleteGammaContFracSolution (a z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 =>
      if Even n then
        -(ascPochhammer ℂ (n / 2)).eval (1 - a) * z⁻¹ ^ (n / 2) *
          kummerLaplace (n / 2) (a - 1 - (n / 2 : ℕ)) z
      else
        (ascPochhammer ℂ (n / 2 + 1)).eval (1 - a) * z⁻¹ ^ (n / 2 + 1) *
          kummerLaplace (n / 2) (a - 2 - (n / 2 : ℕ)) z

/-- Normalization `f 0 = 1` of `upperIncompleteGammaContFracSolution`. -/
@[simp]
theorem upperIncompleteGammaContFracSolution_zero (a z : ℂ) :
    upperIncompleteGammaContFracSolution a z 0 = 1 := by rfl

/-- Successor formula for `Complex.upperIncompleteGammaContFracSolution`. -/
theorem upperIncompleteGammaContFracSolution_succ (a z : ℂ) (n : ℕ) :
    upperIncompleteGammaContFracSolution a z (n + 1) =
      if Even n then
        -(ascPochhammer ℂ (n / 2)).eval (1 - a) * z⁻¹ ^ (n / 2) *
          kummerLaplace (n / 2) (a - 1 - (n / 2 : ℕ)) z
      else
        (ascPochhammer ℂ (n / 2 + 1)).eval (1 - a) * z⁻¹ ^ (n / 2 + 1) *
          kummerLaplace (n / 2) (a - 2 - (n / 2 : ℕ)) z := (rfl)

/-- Initial value `f 1 = -kummerLaplace 0 (a - 1) z` of `upperIncompleteGammaContFracSolution`. -/
@[simp]
theorem upperIncompleteGammaContFracSolution_one (a z : ℂ) :
    upperIncompleteGammaContFracSolution a z 1 = -kummerLaplace 0 (a - 1) z := by
  simp [upperIncompleteGammaContFracSolution]

/-- Odd-index formula for `upperIncompleteGammaContFracSolution`. -/
@[simp]
theorem upperIncompleteGammaContFracSolution_two_mul_add_one (a z : ℂ) (k : ℕ) :
    upperIncompleteGammaContFracSolution a z (2 * k + 1) =
      -(ascPochhammer ℂ k).eval (1 - a) * z⁻¹ ^ k * kummerLaplace k (a - 1 - k) z := by
  rw [upperIncompleteGammaContFracSolution, ite_eq_left (even_two_mul k),
    Nat.mul_div_right k zero_lt_two]

/-- Even-index formula for `upperIncompleteGammaContFracSolution`. -/
@[simp]
theorem upperIncompleteGammaContFracSolution_two_mul_add_two (a z : ℂ) (k : ℕ) :
    upperIncompleteGammaContFracSolution a z (2 * k + 2) =
      (ascPochhammer ℂ (k + 1)).eval (1 - a) * z⁻¹ ^ (k + 1) *
        kummerLaplace k (a - 2 - k) z := by
  rw [upperIncompleteGammaContFracSolution, ite_eq_right (by simp [parity_simps]),
    Nat.mul_add_div zero_lt_two]
  simp

/-- **Three-term recurrence for Legendre's incomplete Gamma continued fraction.**
On `slitPlane`, `f := upperIncompleteGammaContFracSolution a z` satisfies
`f (n + 2) = f (n + 1) + upperIncompleteGammaContFracPartNum a z (n + 1) * f n` for every
`n : ℕ`. -/
theorem upperIncompleteGammaContFracSolution_add_two (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (n : ℕ) :
    upperIncompleteGammaContFracSolution a z (n + 2) =
      upperIncompleteGammaContFracSolution a z (n + 1) +
        upperIncompleteGammaContFracPartNum a z (n + 1) *
          upperIncompleteGammaContFracSolution a z n := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  rcases eq_or_ne n 0 with rfl | hn0
  · -- Base step `n = 0`: integration by parts at `c = 0`.
    have hibp := congr_arg (z⁻¹ * ·) (mul_kummerLaplace_zero (a - 1) hz)
    simp only [← mul_assoc, inv_mul_cancel₀ hz0, one_mul, mul_add, mul_one,
      sub_sub, one_add_one_eq_two] at hibp
    have h2 : upperIncompleteGammaContFracSolution a z 2 =
        (1 - a) * z⁻¹ * kummerLaplace 0 (a - 2) z := by
      simpa [ascPochhammer_one] using upperIncompleteGammaContFracSolution_two_mul_add_two a z 0
    rw [h2, upperIncompleteGammaContFracSolution_one, upperIncompleteGammaContFracPartNum_one,
      upperIncompleteGammaContFracSolution_zero, mul_one]
    linear_combination hibp
  · obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 1 ∨ n = 2 * k + 2 := ⟨(n - 1) / 2, by omega⟩
    · -- Odd step `n = 2k + 1`: contiguous difference in the middle parameter.
      have hidx₁ : 2 * k + 1 + 2 = 2 * (k + 1) + 1 := by omega
      have hidx₂ : 2 * k + 1 + 1 = 2 * k + 2 := by omega
      have hpar₁ : a - 1 - (k : ℂ) - 1 = a - 2 - k := by ring
      have hpar₂ : a - 1 - ((k + 1 : ℕ) : ℂ) = a - 2 - k := by push_cast; ring
      have hdiff := kummerLaplace_sub_kummerLaplace_sub_one k (a - 1 - k) hz
      rw [hpar₁] at hdiff
      rw [hidx₁, hidx₂]
      simp only [upperIncompleteGammaContFracSolution_two_mul_add_one,
        upperIncompleteGammaContFracSolution_two_mul_add_two,
        upperIncompleteGammaContFracPartNum_two_mul_add_two, hpar₂, ascPochhammer_succ_eval]
      linear_combination (ascPochhammer ℂ k).eval (1 - a) * (1 - a + (k : ℂ)) *
        z⁻¹ ^ (k + 1) * hdiff
    · -- Even step `n = 2k + 2`: integration by parts at `c = k + 1`.
      have hidx₁ : 2 * k + 2 + 2 = 2 * (k + 1) + 2 := by omega
      have hidx₂ : 2 * k + 2 + 1 = 2 * (k + 1) + 1 := by omega
      have hpart : upperIncompleteGammaContFracPartNum a z (2 * (k + 1) + 1) =
          ((k : ℂ) + 1) * z⁻¹ := by
        have hidx₃ : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
        rw [hidx₃, upperIncompleteGammaContFracPartNum_two_mul_add_three]
      have hpar₁ : a - 2 - ((k + 1 : ℕ) : ℂ) = a - 2 - k - 1 := by push_cast; ring
      have hpar₂ : a - 1 - ((k + 1 : ℕ) : ℂ) = a - 2 - k := by push_cast; ring
      have hpoch : (ascPochhammer ℂ (k + 1 + 1)).eval (1 - a) =
          (ascPochhammer ℂ (k + 1)).eval (1 - a) * (1 - a + (k : ℂ) + 1) := by
        rw [ascPochhammer_succ_eval]
        push_cast
        ring
      have hibp := congr_arg (z⁻¹ * ·) (mul_kummerLaplace_add_one k (a - 2 - k) hz)
      simp only [← mul_assoc, inv_mul_cancel₀ hz0, one_mul, mul_add] at hibp
      rw [hidx₁, hidx₂]
      simp only [upperIncompleteGammaContFracSolution_two_mul_add_two,
        upperIncompleteGammaContFracSolution_two_mul_add_one, hpart, hpar₁, hpar₂, hpoch]
      linear_combination (ascPochhammer ℂ (k + 1)).eval (1 - a) * z⁻¹ ^ (k + 1) * hibp

private theorem ascPochhammer_eval_one_sub_ne_zero {a : ℂ} (ha : ∀ m : ℕ, a ≠ m + 1) (k : ℕ) :
    (ascPochhammer ℂ k).eval (1 - a) ≠ 0 := by
  rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
  rintro ⟨m, _, hm⟩
  exact ha m (by linear_combination -hm)

/-- When `z ∈ slitPlane` and `a` is not a positive integer, the Kummer-Laplace recurrence
solution `upperIncompleteGammaContFracSolution a z n` is eventually nonzero as `n → ∞`. -/
theorem eventually_upperIncompleteGammaContFracSolution_ne_zero {a : ℂ}
    (ha : ∀ m : ℕ, a ≠ m + 1) {z : ℂ} (hz : z ∈ slitPlane) :
    ∀ᶠ n : ℕ in atTop, upperIncompleteGammaContFracSolution a z n ≠ 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hp := ascPochhammer_eval_one_sub_ne_zero ha
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (eventually_kummerLaplace_ne_zero a hz)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (eventually_kummerLaplace_ne_zero (a - 1) hz)
  refine eventually_atTop.mpr ⟨2 * max N₁ N₂ + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 1 ∨ n = 2 * k + 2 :=
    ⟨(n - 1) / 2, by omega⟩
  · rw [upperIncompleteGammaContFracSolution_two_mul_add_one]
    refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (hp k)) (pow_ne_zero k (inv_ne_zero hz0)))
      (hN₁ k ?_)
    have : max N₁ N₂ ≤ k := by omega
    exact (le_max_left N₁ N₂).trans this
  · rw [upperIncompleteGammaContFracSolution_two_mul_add_two]
    refine mul_ne_zero (mul_ne_zero (hp (k + 1)) (pow_ne_zero (k + 1) (inv_ne_zero hz0))) ?_
    have hk2 : N₂ ≤ k := (le_max_right N₁ N₂).trans (by omega)
    simpa [sub_sub, one_add_one_eq_two] using hN₂ k hk2

/-! ### Minimality of the Kummer-Laplace solution -/

section Minimality

open Asymptotics Finset
open scoped Nat Real

/-- The term `(-1)^n (a₁ ⋯ aₙ) / (f(n) f(n + 1))` of the reduction-of-order series of the
Kummer-Laplace solution `f`. -/
private def legendreTerm (a z : ℂ) (n : ℕ) : ℂ :=
  (-1) ^ n * (∏ j ∈ Icc 1 n, upperIncompleteGammaContFracPartNum a z j) /
    (upperIncompleteGammaContFracSolution a z n * upperIncompleteGammaContFracSolution a z (n + 1))

private theorem prod_Icc_partNum_two_mul_add_one (a z : ℂ) (k : ℕ) :
    ∏ j ∈ Icc 1 (2 * k + 1), upperIncompleteGammaContFracPartNum a z j =
      (ascPochhammer ℂ k).eval (1 - a) * (k ! : ℂ) * z⁻¹ ^ (2 * k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : upperIncompleteGammaContFracPartNum a z (2 * k + 1 + 1) = ((k : ℂ) + 1 - a) * z⁻¹ :=
      upperIncompleteGammaContFracPartNum_two_mul_add_two a z k
    have h3 : upperIncompleteGammaContFracPartNum a z (2 * k + 1 + 1 + 1) = ((k : ℂ) + 1) * z⁻¹ :=
      upperIncompleteGammaContFracPartNum_two_mul_add_three a z k
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, prod_Icc_succ_top (by omega),
      prod_Icc_succ_top (by omega), ih, h2, h3, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    ring

private theorem prod_Icc_partNum_two_mul_add_two (a z : ℂ) (k : ℕ) :
    ∏ j ∈ Icc 1 (2 * k + 2), upperIncompleteGammaContFracPartNum a z j =
      (ascPochhammer ℂ (k + 1)).eval (1 - a) * (k ! : ℂ) * z⁻¹ ^ (2 * k + 2) := by
  have h2 : upperIncompleteGammaContFracPartNum a z (2 * k + 1 + 1) = ((k : ℂ) + 1 - a) * z⁻¹ :=
    upperIncompleteGammaContFracPartNum_two_mul_add_two a z k
  rw [show 2 * k + 2 = 2 * k + 1 + 1 from rfl, prod_Icc_succ_top (by omega),
    prod_Icc_partNum_two_mul_add_one, h2, ascPochhammer_succ_eval]
  ring

private theorem legendreTerm_two_mul_add_one {a z : ℂ} (hz : z ≠ 0)
    (hp : ∀ k : ℕ, (ascPochhammer ℂ k).eval (1 - a) ≠ 0) {k : ℕ}
    (hK : kummerLaplace k (a - 1 - k) z ≠ 0) (hL : kummerLaplace k (a - 2 - k) z ≠ 0) :
    legendreTerm a z (2 * k + 1) = (k ! : ℂ) / (ascPochhammer ℂ (k + 1)).eval (1 - a) /
      (kummerLaplace k (a - 1 - k) z * kummerLaplace k (a - 2 - k) z) := by
  have hp0 := hp k
  rw [legendreTerm, prod_Icc_partNum_two_mul_add_one,
    upperIncompleteGammaContFracSolution_two_mul_add_one,
    show 2 * k + 1 + 1 = 2 * k + 2 from rfl, upperIncompleteGammaContFracSolution_two_mul_add_two,
    Odd.neg_one_pow ⟨k, rfl⟩, ascPochhammer_succ_eval]
  field_simp
  ring

private theorem legendreTerm_two_mul_add_two {a z : ℂ} (hz : z ≠ 0)
    (hp : ∀ k : ℕ, (ascPochhammer ℂ k).eval (1 - a) ≠ 0) {k : ℕ}
    (hL : kummerLaplace k (a - 2 - k) z ≠ 0)
    (hK₁ : kummerLaplace (k + 1) (a - 1 - (k + 1 : ℕ)) z ≠ 0) :
    legendreTerm a z (2 * k + 2) = -((k ! : ℂ) / (ascPochhammer ℂ (k + 1)).eval (1 - a) /
      (kummerLaplace k (a - 2 - k) z * kummerLaplace (k + 1) (a - 1 - (k + 1 : ℕ)) z)) := by
  have hp1 := hp (k + 1)
  rw [legendreTerm, prod_Icc_partNum_two_mul_add_two,
    upperIncompleteGammaContFracSolution_two_mul_add_two,
    show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by ring,
    upperIncompleteGammaContFracSolution_two_mul_add_one, Even.neg_one_pow ⟨k + 1, by ring⟩]
  field_simp
  ring

/-- The contiguous relation `K(k, a - 1 - k) - K(k, a - 2 - k) = K(k + 1, a - 2 - k)` linking
consecutive odd values of the Kummer-Laplace solution. -/
private theorem kummerLaplace_sub_eq_succ (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (k : ℕ) :
    kummerLaplace k (a - 1 - k) z - kummerLaplace k (a - 2 - k) z =
      kummerLaplace (k + 1) (a - 1 - (k + 1 : ℕ)) z := by
  have h1 : a - 1 - (k : ℂ) - 1 = a - 2 - k := by ring
  have h2 : a - 1 - (k : ℂ) - 1 = a - 1 - ((k + 1 : ℕ) : ℂ) := by push_cast; ring
  have h := kummerLaplace_sub_kummerLaplace_sub_one k (a - 1 - k) hz
  rw [h1] at h
  rw [h, ← h1, h2]

private theorem legendreTerm_pair {a z : ℂ} (hz : z ∈ slitPlane)
    (hp : ∀ k : ℕ, (ascPochhammer ℂ k).eval (1 - a) ≠ 0) {k : ℕ}
    (hK : kummerLaplace k (a - 1 - k) z ≠ 0) (hL : kummerLaplace k (a - 2 - k) z ≠ 0)
    (hK₁ : kummerLaplace (k + 1) (a - 1 - (k + 1 : ℕ)) z ≠ 0) :
    legendreTerm a z (2 * k + 1) + legendreTerm a z (2 * k + 2) =
      -((k ! : ℂ) / (ascPochhammer ℂ (k + 1)).eval (1 - a) /
        (kummerLaplace k (a - 1 - k) z * kummerLaplace (k + 1) (a - 1 - (k + 1 : ℕ)) z)) := by
  have hz0 := slitPlane_ne_zero hz
  have hp1 := hp (k + 1)
  have hrel := kummerLaplace_sub_eq_succ a hz k
  rw [legendreTerm_two_mul_add_one hz0 hp hK hL, legendreTerm_two_mul_add_two hz0 hp hL hK₁]
  field_simp
  linear_combination -(k ! : ℂ) * hrel

/-! #### Asymptotics of the reduction-of-order terms -/

private theorem natCast_mul_cpow_one_half (z : ℂ) (k : ℕ) :
    ((k : ℂ) * z) ^ (1 / 2 : ℂ) = (Real.sqrt k : ℂ) * z ^ (1 / 2 : ℂ) := by
  rw [natCast_mul_cpow, ofReal_sqrt_eq_cpow (Nat.cast_nonneg k), ofReal_natCast]

/-- The constant `√π e^{z/2} z^{-a/2 - 1/4}` of the saddle-point asymptotic of
`K(k, a - 1 - k; z)`. -/
private def legendreConst (a z : ℂ) : ℂ :=
  (Real.sqrt π : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4)

private theorem legendreConst_ne_zero (a : ℂ) {z : ℂ} (hz : z ≠ 0) : legendreConst a z ≠ 0 :=
  mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos))
    (exp_ne_zero _)) (cpow_ne_zero_iff.mpr (Or.inl hz))

/-- The model `e^{4 √(k z)}` for the growth of the reduction-of-order terms. -/
private def legendreModel (z : ℂ) (k : ℕ) : ℂ :=
  cexp (4 * ((Real.sqrt k : ℂ) * z ^ (1 / 2 : ℂ)))

private theorem kummerLaplace_isEquivalent_sqrt (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (fun k : ℕ => kummerLaplace k (a - 1 - k) z) ~[atTop] fun k : ℕ =>
      legendreConst a z * (k : ℂ) ^ (a / 2 - 1 / 4) *
        cexp (-2 * ((Real.sqrt k : ℂ) * z ^ (1 / 2 : ℂ))) := by
  simpa only [legendreConst, natCast_mul_cpow_one_half] using kummerLaplace_isEquivalent a hz

/-- `K(k, a - 2 - k; z)` is `√z / √k` times the model of `K(k, a - 1 - k; z)`. -/
private theorem kummerLaplace_sub_two_isEquivalent (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (fun k : ℕ => kummerLaplace k (a - 2 - k) z) ~[atTop] fun k : ℕ =>
      z ^ (1 / 2 : ℂ) * (Real.sqrt k : ℂ)⁻¹ * (legendreConst a z * (k : ℂ) ^ (a / 2 - 1 / 4) *
        cexp (-2 * ((Real.sqrt k : ℂ) * z ^ (1 / 2 : ℂ)))) := by
  have hz0 := slitPlane_ne_zero hz
  refine ((kummerLaplace_isEquivalent_sqrt (a - 1) hz).congr_left
    (Eventually.of_forall fun k => by simp only [show a - 1 - 1 - (k : ℂ) = a - 2 - k by ring]))
    |>.congr_right ?_
  filter_upwards [eventually_ne_atTop 0] with k hk
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [legendreConst, legendreConst, show -(a - 1) / 2 - 1 / 4 = (-a / 2 - 1 / 4) + 1 / 2 by ring,
    cpow_add _ _ hz0, show (a - 1) / 2 - 1 / 4 = (a / 2 - 1 / 4) + -(1 / 2) by ring,
    cpow_add _ _ hk0, cpow_neg, ofReal_sqrt_eq_cpow (Nat.cast_nonneg k), ofReal_natCast]
  ring

private theorem eventually_kummerLaplace_sub_two_ne_zero (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    ∀ᶠ k : ℕ in atTop, kummerLaplace k (a - 2 - k) z ≠ 0 := by
  filter_upwards [eventually_kummerLaplace_ne_zero (a - 1) hz] with k hk
  rwa [show a - 1 - 1 - (k : ℂ) = a - 2 - k by ring] at hk

private theorem legendreModel_succ (z : ℂ) (k : ℕ) :
    legendreModel z (k + 1) = legendreModel z k *
      cexp (4 * z ^ (1 / 2 : ℂ) * ((Real.sqrt ((k : ℝ) + 1) - Real.sqrt k : ℝ) : ℂ)) := by
  rw [legendreModel, legendreModel, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem norm_legendreModel (z : ℂ) (k : ℕ) :
    ‖legendreModel z k‖ = Real.exp (4 * (Real.sqrt k * (z ^ (1 / 2 : ℂ)).re)) := by
  rw [legendreModel, norm_exp]
  simp

private theorem tendsto_norm_legendreModel_atTop {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun k => ‖legendreModel z k‖) atTop atTop := by
  have hs : 0 < (z ^ (1 / 2 : ℂ)).re := (cpow_one_half_re_pos_iff z).mpr hz
  simp only [norm_legendreModel]
  exact Real.tendsto_exp_atTop.comp <| Tendsto.const_mul_atTop (by norm_num) <|
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const hs)

/-- The model moves outward at a bounded angle. -/
private theorem norm_legendreModel_succ_sub_le {z : ℂ} (hz : z ∈ slitPlane) (k : ℕ) :
    ‖legendreModel z (k + 1) - legendreModel z k‖ ≤
      Real.exp (4 * ‖z ^ (1 / 2 : ℂ)‖) * ‖z ^ (1 / 2 : ℂ)‖ / (z ^ (1 / 2 : ℂ)).re *
        (‖legendreModel z (k + 1)‖ - ‖legendreModel z k‖) := by
  set s := z ^ (1 / 2 : ℂ)
  have hs : 0 < s.re := (cpow_one_half_re_pos_iff z).mpr hz
  set x : ℝ := Real.sqrt ((k : ℝ) + 1) - Real.sqrt k
  have hx0 : 0 ≤ x := sub_nonneg.2 (Real.sqrt_le_sqrt (by linarith))
  have hx1 : x ≤ 1 := by
    have := Real.sqrt_add_le_add_sqrt (k : ℝ) 1
    rw [Real.sqrt_one] at this
    linarith
  set u : ℂ := 4 * s * x
  have hsplit : legendreModel z (k + 1) = legendreModel z k * cexp u := legendreModel_succ z k
  have hu_norm : ‖u‖ = 4 * ‖s‖ * x := by
    simp [u, abs_of_nonneg hx0]
  have hu_re : u.re = 4 * s.re * x := by
    simp [u]
  rw [hsplit]
  calc ‖legendreModel z k * cexp u - legendreModel z k‖
      = ‖legendreModel z k‖ * ‖cexp u - 1‖ := by rw [← norm_mul, mul_sub_one]
    _ ≤ ‖legendreModel z k‖ * (‖u‖ * Real.exp ‖u‖) := by
        gcongr
        simpa using norm_exp_sub_sum_le_norm_mul_exp u 1
    _ ≤ ‖legendreModel z k‖ * (4 * ‖s‖ * x * Real.exp (4 * ‖s‖)) := by
        rw [hu_norm]
        have : Real.exp (4 * ‖s‖ * x) ≤ Real.exp (4 * ‖s‖) :=
          Real.exp_le_exp.2 (by nlinarith [norm_nonneg s])
        gcongr
    _ = Real.exp (4 * ‖s‖) * ‖s‖ / s.re * (‖legendreModel z k‖ * (4 * s.re * x)) := by
        field_simp
    _ ≤ Real.exp (4 * ‖s‖) * ‖s‖ / s.re * (‖legendreModel z k‖ * (Real.exp u.re - 1)) := by
        gcongr
        rw [← hu_re]
        linarith [Real.add_one_le_exp u.re]
    _ = Real.exp (4 * ‖s‖) * ‖s‖ / s.re *
          (‖legendreModel z k * cexp u‖ - ‖legendreModel z k‖) := by
        rw [norm_mul, norm_exp]
        ring

/-- The forward differences of the model satisfy `Δ e^{4 √(k z)} ~ 2 √z k^{-1/2} e^{4 √(k z)}`. -/
private theorem legendreModel_succ_sub_isEquivalent {z : ℂ} (hz : z ∈ slitPlane) :
    (fun k => legendreModel z (k + 1) - legendreModel z k) ~[atTop]
      fun k => 2 * z ^ (1 / 2 : ℂ) * (Real.sqrt k : ℂ)⁻¹ * legendreModel z k := by
  set s := z ^ (1 / 2 : ℂ)
  have hs0 : s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hz))
  set x : ℕ → ℝ := fun k => Real.sqrt ((k : ℝ) + 1) - Real.sqrt k
  have hx_pos (k : ℕ) : 0 < x k := sub_pos.2 (Real.sqrt_lt_sqrt (Nat.cast_nonneg k) (by linarith))
  have hsx : Tendsto (fun k : ℕ => Real.sqrt k * x k) atTop (𝓝 (1 / 2)) :=
    Real.tendsto_sqrt_mul_sqrt_add_one_sub_sqrt.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hx : Tendsto x atTop (𝓝 0) := by
    have := hsx.mul hinv
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with k hk
    have : Real.sqrt k ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
    field_simp
  -- `u k = 4 √z (√(k + 1) - √k) → 0` through nonzero values, so `(e^{u k} - 1) / u k → 1`.
  set u : ℕ → ℂ := fun k => 4 * s * (x k : ℂ)
  have hu : Tendsto u atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
    · simpa using (hx.ofReal.const_mul (4 * s))
    · exact mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hs0)
        (ofReal_ne_zero.mpr (hx_pos k).ne')
  have hslope : Tendsto (fun k => (cexp (u k) - 1) / u k) atTop (𝓝 1) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp (Complex.hasDerivAt_exp 0)).comp hu
    simpa [Function.comp_def, slope_def_field] using h
  have hlim : Tendsto (fun k : ℕ => (Real.sqrt k : ℂ) * (cexp (u k) - 1) / (2 * s)) atTop
      (𝓝 1) := by
    have h := ((hsx.ofReal.mul_const (4 * s)).mul hslope).div_const (2 * s)
    have h1 : ((1 / 2 : ℝ) : ℂ) * (4 * s) * 1 / (2 * s) = 1 := by
      push_cast
      field_simp
      ring
    rw [h1] at h
    refine h.congr' (Eventually.of_forall fun k => ?_)
    have hxk : (x k : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hx_pos k).ne'
    simp only [u]
    push_cast
    field_simp
  refine isEquivalent_of_tendsto_one (hlim.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with k hk
  have hk0 : (Real.sqrt k : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  have hsplit : legendreModel z (k + 1) = legendreModel z k * cexp (u k) :=
    legendreModel_succ z k
  have hH : legendreModel z k ≠ 0 := exp_ne_zero _
  rw [Pi.div_apply, hsplit]
  field_simp

/-- For `k ≥ 1`, `k^{a - 1} / (C k^{a/2 - 1/4} e^{-2 √(k z)})² = e^{4 √(k z)} / (C² √k)`. -/
private theorem inv_cpow_one_sub_div_sq (a : ℂ) {z : ℂ} (hz : z ≠ 0) {k : ℕ} (hk : k ≠ 0) :
    ((k : ℂ) ^ (1 - a))⁻¹ / (legendreConst a z * (k : ℂ) ^ (a / 2 - 1 / 4) *
      cexp (-2 * ((Real.sqrt k : ℂ) * z ^ (1 / 2 : ℂ)))) ^ 2 =
        legendreModel z k / (legendreConst a z ^ 2 * (Real.sqrt k : ℂ)) := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hρ : (Real.sqrt k : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  have hw : (k : ℂ) ^ (a / 2 - 1 / 4) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hk0)
  have hC := legendreConst_ne_zero a hz
  have hq : ((k : ℂ) ^ (1 - a))⁻¹ =
      (k : ℂ) ^ (a / 2 - 1 / 4) * (k : ℂ) ^ (a / 2 - 1 / 4) / (Real.sqrt k : ℂ) := by
    rw [eq_div_iff hρ, ofReal_sqrt_eq_cpow (Nat.cast_nonneg k), ofReal_natCast, ← cpow_neg,
      ← cpow_add _ _ hk0, ← cpow_add _ _ hk0]
    congr 1
    ring
  have hH : legendreModel z k = (cexp (-2 * ((Real.sqrt k : ℂ) * z ^ (1 / 2 : ℂ))) ^ 2)⁻¹ := by
    rw [legendreModel, ← Complex.exp_natCast_mul, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [hq, hH]
  set w := (k : ℂ) ^ (a / 2 - 1 / 4)
  field_simp

/-- The odd terms satisfy `T(2k + 1) ~ μ e^{4 √(k z)}` with `μ = Γ(1 - a) / (√z C²)`. -/
private theorem legendreTerm_two_mul_add_one_isEquivalent {a : ℂ} (ha : ∀ m : ℕ, a ≠ m + 1)
    {z : ℂ} (hz : z ∈ slitPlane) :
    (fun k : ℕ => legendreTerm a z (2 * k + 1)) ~[atTop] fun k =>
      Gamma (1 - a) / (z ^ (1 / 2 : ℂ) * legendreConst a z ^ 2) * legendreModel z k := by
  have hz0 := slitPlane_ne_zero hz
  have hp := ascPochhammer_eval_one_sub_ne_zero ha
  have hs : ∀ m : ℕ, 1 - a ≠ -m := fun m hm => ha m (by linear_combination -hm)
  have hs0 : z ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hC := legendreConst_ne_zero a hz0
  have hKne := eventually_kummerLaplace_ne_zero a hz
  have hLne := eventually_kummerLaplace_sub_two_ne_zero a hz
  refine ((isEquivalent_factorial_div_ascPochhammer_eval_succ hs).div
    ((kummerLaplace_isEquivalent_sqrt a hz).mul (kummerLaplace_sub_two_isEquivalent a hz)))
    |>.congr_left ?_ |>.congr_right ?_
  · filter_upwards [hKne, hLne] with k hK hL
    simp only [Pi.div_apply, Pi.mul_apply, legendreTerm_two_mul_add_one hz0 hp hK hL]
  · filter_upwards [eventually_ne_atTop 0] with k hk
    have h := inv_cpow_one_sub_div_sq a hz0 hk
    have hρ : (Real.sqrt k : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
    simp only [Pi.div_apply, Pi.mul_apply]
    set m := legendreConst a z * (k : ℂ) ^ (a / 2 - 1 / 4) *
      cexp (-2 * ((Real.sqrt k : ℂ) * z ^ (1 / 2 : ℂ)))
    have hm : m ≠ 0 := mul_ne_zero (mul_ne_zero hC (cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr hk)))) (exp_ne_zero _)
    calc Gamma (1 - a) * ((k : ℂ) ^ (1 - a))⁻¹ / (m * (z ^ (1 / 2 : ℂ) * (Real.sqrt k : ℂ)⁻¹ * m))
        = Gamma (1 - a) * (Real.sqrt k : ℂ) / z ^ (1 / 2 : ℂ) *
            (((k : ℂ) ^ (1 - a))⁻¹ / m ^ 2) := by field_simp
      _ = _ := by rw [h]; field_simp

/-- The pair sums satisfy `T(2k + 1) + T(2k + 2) ~ Δ(λ e^{4 √(k z)})` with
`λ = -Γ(1 - a) / (2 √z C²)`. -/
private theorem legendreTerm_pair_isEquivalent {a : ℂ} (ha : ∀ m : ℕ, a ≠ m + 1)
    {z : ℂ} (hz : z ∈ slitPlane) :
    (fun k : ℕ => legendreTerm a z (2 * k + 1) + legendreTerm a z (2 * k + 2)) ~[atTop] fun k =>
      -(Gamma (1 - a) / (2 * z ^ (1 / 2 : ℂ) * legendreConst a z ^ 2)) * legendreModel z (k + 1) -
        -(Gamma (1 - a) / (2 * z ^ (1 / 2 : ℂ) * legendreConst a z ^ 2)) * legendreModel z k := by
  have hz0 := slitPlane_ne_zero hz
  have hp := ascPochhammer_eval_one_sub_ne_zero ha
  have hs : ∀ m : ℕ, 1 - a ≠ -m := fun m hm => ha m (by linear_combination -hm)
  have hs0 : z ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hC := legendreConst_ne_zero a hz0
  have hKne := eventually_kummerLaplace_ne_zero a hz
  have hLne := eventually_kummerLaplace_sub_two_ne_zero a hz
  have hK₁ne : ∀ᶠ k : ℕ in atTop, kummerLaplace (k + 1) (a - 1 - (k + 1 : ℕ)) z ≠ 0 :=
    (tendsto_add_atTop_nat 1).eventually hKne
  have hK := kummerLaplace_isEquivalent_sqrt a hz
  -- `K(k, a - 2 - k) = o(K(k, a - 1 - k))`, so `K(k + 1, a - 2 - k) ~ K(k, a - 1 - k)`.
  have hLo : (fun k : ℕ => kummerLaplace k (a - 2 - k) z) =o[atTop] fun k : ℕ =>
      legendreConst a z * (k : ℂ) ^ (a / 2 - 1 / 4) *
        cexp (-2 * ((Real.sqrt k : ℂ) * z ^ (1 / 2 : ℂ))) := by
    refine (kummerLaplace_sub_two_isEquivalent a hz).isBigO.trans_isLittleO ?_
    have ht : Tendsto (fun k : ℕ => z ^ (1 / 2 : ℂ) * (Real.sqrt k : ℂ)⁻¹) atTop (𝓝 0) := by
      simpa using ((tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).ofReal.const_mul
          (z ^ (1 / 2 : ℂ)))
    simpa using ((isLittleO_one_iff ℂ).2 ht).mul_isBigO (isBigO_refl _ atTop)
  have hK₁ := (hK.sub_isLittleO hLo).congr_left
    (Eventually.of_forall fun k => kummerLaplace_sub_eq_succ a hz k)
  have hΔ := (IsEquivalent.refl (u := fun _ : ℕ =>
    -(Gamma (1 - a) / (2 * z ^ (1 / 2 : ℂ) * legendreConst a z ^ 2)))).mul
      (legendreModel_succ_sub_isEquivalent hz)
  refine (((isEquivalent_factorial_div_ascPochhammer_eval_succ hs).div
    (hK.mul hK₁)).neg.congr_left ?_).trans
      ((hΔ.symm.congr_left ?_).congr_right (Eventually.of_forall fun k => ?_))
  · filter_upwards [hKne, hLne, hK₁ne] with k hK hL hK₁
    simp only [Pi.div_apply, Pi.mul_apply, legendreTerm_pair hz hp hK hL hK₁]
  · filter_upwards [eventually_ne_atTop 0] with k hk
    have hρ : (Real.sqrt k : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
    simp only [Pi.div_apply, Pi.mul_apply]
    rw [mul_div_assoc, ← sq, inv_cpow_one_sub_div_sq a hz0 hk]
    field_simp
  · simp only [Pi.mul_apply]
    ring

/-- The odd-indexed partial sums of the reduction-of-order series are sums of pairs. -/
private theorem sum_Ico_one_legendreTerm_two_mul_add_one (a z : ℂ) (k : ℕ) :
    ∑ m ∈ Ico 1 (2 * k + 1), legendreTerm a z m =
      ∑ j ∈ range k, (legendreTerm a z (2 * j + 1) + legendreTerm a z (2 * j + 2)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ← ih, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring,
      sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega), add_assoc]

/-- For `z ∈ slitPlane` and `a ∉ {1, 2, …}`, the reduction-of-order partial sums starting at
index `1` tend to infinity in norm. The pair sums `T(2k + 1) + T(2k + 2)` are asymptotic to the
forward differences of `λ e^{4 √(k z)}`, so the odd-indexed partial sums are
`λ e^{4 √(k z)} + o(e^{4 √(k z)})`; adding `T(2k + 1) ~ μ e^{4 √(k z)}` gives the even-indexed
ones, with `λ + μ = μ / 2 ≠ 0`. -/
private theorem tendsto_norm_sum_Ico_one_legendreTerm_atTop {a : ℂ} (ha : ∀ m : ℕ, a ≠ m + 1)
    {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun n => ‖∑ m ∈ Ico 1 n, legendreTerm a z m‖) atTop atTop := by
  have hz0 := slitPlane_ne_zero hz
  have hs0 : z ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hC := legendreConst_ne_zero a hz0
  have hΓ : Gamma (1 - a) ≠ 0 := Gamma_ne_zero fun m hm => ha m (by linear_combination -hm)
  set H := legendreModel z
  set μ := Gamma (1 - a) / (z ^ (1 / 2 : ℂ) * legendreConst a z ^ 2)
  set c := -(Gamma (1 - a) / (2 * z ^ (1 / 2 : ℂ) * legendreConst a z ^ 2))
  have hμ : μ ≠ 0 := div_ne_zero hΓ (mul_ne_zero hs0 (pow_ne_zero 2 hC))
  have hc : c ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero hΓ (mul_ne_zero (mul_ne_zero two_ne_zero hs0) (pow_ne_zero 2 hC)))
  have hcμ : c + μ ≠ 0 := by
    have : c + μ = μ / 2 := by simp only [c, μ]; field_simp; ring
    rw [this]
    exact div_ne_zero hμ two_ne_zero
  have hHtop := tendsto_norm_legendreModel_atTop hz
  have hodd_sum := sum_Ico_one_legendreTerm_two_mul_add_one a z
  have hP : (fun k => ∑ j ∈ range k, (legendreTerm a z (2 * j + 1) + legendreTerm a z (2 * j + 2))
      - c * H k) =o[atTop] H := by
    refine (TauCeti.isLittleO_sum_range_sub (G := fun k => c * H k)
      (M := Real.exp (4 * ‖z ^ (1 / 2 : ℂ)‖) * ‖z ^ (1 / 2 : ℂ)‖ / (z ^ (1 / 2 : ℂ)).re)
      (legendreTerm_pair_isEquivalent ha hz) (fun k => ?_) ?_).trans_isBigO
        (isBigO_const_mul_self c H atTop)
    · rw [← mul_sub, norm_mul, norm_mul, norm_mul, ← mul_sub, mul_left_comm]
      exact mul_le_mul_of_nonneg_left (norm_legendreModel_succ_sub_le hz k) (norm_nonneg c)
    · simpa only [norm_mul] using hHtop.const_mul_atTop (norm_pos_iff.mpr hc)
  have hT : (fun k => legendreTerm a z (2 * k + 1) - μ * H k) =o[atTop] H :=
    (legendreTerm_two_mul_add_one_isEquivalent ha hz).isLittleO.trans_isBigO
      (isBigO_const_mul_self μ H atTop)
  -- A sequence `c' H + o(H)` with `c' ≠ 0` tends to infinity in norm.
  have hdiv {u : ℕ → ℂ} {c' : ℂ} (hc' : c' ≠ 0) (hu : (fun k => u k - c' * H k) =o[atTop] H) :
      Tendsto (fun k => ‖u k‖) atTop atTop := by
    have h : u ~[atTop] fun k => c' * H k := hu.trans_isBigO (isBigO_self_const_mul hc' H atTop)
    exact ((isBigO_self_const_mul hc' H atTop).trans h.symm.isBigO).trans_tendsto_norm_atTop hHtop
  have hodd := hdiv hc hP
  have heven := hdiv (u := fun k => ∑ j ∈ range k,
      (legendreTerm a z (2 * j + 1) + legendreTerm a z (2 * j + 2)) + legendreTerm a z (2 * k + 1))
    hcμ ((hP.add hT).congr_left fun k => by ring)
  rw [tendsto_atTop]
  intro B
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 (tendsto_atTop.1 hodd B)
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.1 (tendsto_atTop.1 heven B)
  refine eventually_atTop.2 ⟨2 * (K₁ + K₂) + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 1 ∨ n = 2 * k + 2 := ⟨(n - 1) / 2, by omega⟩
  · rw [hodd_sum]
    exact hK₁ k (by omega)
  · rw [show 2 * k + 2 = 2 * k + 1 + 1 from rfl, sum_Ico_succ_top (by omega), hodd_sum]
    exact hK₂ k (by omega)

/-- **Minimality of the Kummer-Laplace solution.** For `z ∈ slitPlane` and `a ∉ {1, 2, …}`, the
reduction-of-order partial sums `∑_{m = N}^{n - 1} (-1)^m (a₁ ⋯ aₘ) / (f(m) f(m + 1))` of
`f = upperIncompleteGammaContFracSolution a z` tend to infinity in norm, for every starting
index `N`. -/
theorem tendsto_norm_sum_upperIncompleteGammaContFracSolution_atTop {a : ℂ}
    (ha : ∀ m : ℕ, a ≠ m + 1) {z : ℂ} (hz : z ∈ slitPlane) (N : ℕ) :
    Tendsto (fun n => ‖∑ m ∈ Ico N n,
      (-1) ^ m * (∏ j ∈ Icc 1 m, upperIncompleteGammaContFracPartNum a z j) /
        (upperIncompleteGammaContFracSolution a z m *
          upperIncompleteGammaContFracSolution a z (m + 1))‖) atTop atTop :=
  (TauCeti.tendsto_norm_sum_Ico_atTop_iff 1 N).1 (tendsto_norm_sum_Ico_one_legendreTerm_atTop ha hz)

end Minimality

/-! ### Convergence of DLMF 8.9.2 -/

/-- On `slitPlane`, the Kummer-Laplace integral `K(0, a - 1; z)` is the normalized upper
incomplete Gamma function `z^{-a} e^z Γ(a, z)`. -/
theorem kummerLaplace_zero_eq_cpow_neg_mul_exp_mul_upperIncompleteGamma (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    kummerLaplace 0 (a - 1) z = z ^ (-a) * cexp z * upperIncompleteGamma a z := by
  have hexp (w : ℂ) : cexp w * upperIncompleteGamma a w =
      ∫ t in Set.Ioi (0 : ℝ), cexp (-(t : ℂ)) * ((t : ℂ) + w) ^ (a - 1) := by
    rw [upperIncompleteGamma_def, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero, one_mul]
    congr 1
    ext t
    rw [mul_comm, add_comm]
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => cexp (-(t : ℂ)) * ((t : ℂ) + 1) ^ (a - 1)) (Set.Ioi 0) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      ((integrableOn_upperIncompleteGamma_integrand a one_mem_slitPlane).const_mul (cexp 1))
      (fun t _ => ?_) measurableSet_Ioi
    rw [neg_add, Complex.exp_add, Complex.exp_neg 1, add_comm (1 : ℂ)]
    field_simp
  have hI := TauCeti.differentiableOn_integral_mul_ofReal_add_cpow one_mem_slitPlane hint
  have hg : AnalyticOnNhd ℂ (fun w => w ^ (-a) *
      ∫ t in Set.Ioi (0 : ℝ), cexp (-(t : ℂ)) * ((t : ℂ) + w) ^ (a - 1)) slitPlane :=
    DifferentiableOn.analyticOnNhd (fun w hw => ((differentiableAt_id.cpow_const hw).mul
      ((hI w hw).differentiableAt (isOpen_slitPlane.mem_nhds hw))).differentiableWithinAt)
      isOpen_slitPlane
  have heq := ((differentiableOn_kummerLaplace 0 (a - 1)).analyticOnNhd
    isOpen_slitPlane).eqOn_slitPlane_of_ofReal_pos_eq hg (fun x hx => ?_) hz
  · simpa only [mul_assoc, hexp] using heq
  · rw [kummerLaplace_zero_ofReal_eq_cpow_neg_mul_exp_mul_integral a hx, ← hexp,
      upperIncompleteGamma_ofReal, mul_assoc]

/-- **DLMF 8.9.2**: for `z ∈ slitPlane` and `a ∉ {1, 2, …}`, Legendre's continued fraction
`z⁻¹ / (1 + (1 - a) z⁻¹ / (1 + z⁻¹ / (1 + (2 - a) z⁻¹ / (1 + 2 z⁻¹ / (1 + ⋯)))))` has eventually
nonzero denominators, and its convergents tend to `z^{-a} e^z Γ(a, z)`. -/
theorem tendsto_convs_upperIncompleteGamma {a : ℂ} (ha : ∀ m : ℕ, a ≠ m + 1) {z : ℂ}
    (hz : z ∈ slitPlane) :
    (∀ᶠ n in atTop,
        (TauCeti.contFrac (upperIncompleteGammaContFracPartNum a z) fun _ => 1).dens n ≠ 0) ∧
      Tendsto (TauCeti.contFrac (upperIncompleteGammaContFracPartNum a z) fun _ => 1).convs atTop
        (𝓝 (z ^ (-a) * cexp z * upperIncompleteGamma a z)) := by
  have h := TauCeti.tendsto_convs_contFrac_of_tendsto_norm_sum (b := fun _ => (1 : ℂ))
    (fun n hn => ?_) (by simp) (eventually_upperIncompleteGammaContFracSolution_ne_zero ha hz)
    (tendsto_norm_sum_upperIncompleteGammaContFracSolution_atTop ha hz 0)
  · rwa [upperIncompleteGammaContFracSolution_zero, div_one,
      upperIncompleteGammaContFracSolution_one, neg_neg,
      kummerLaplace_zero_eq_cpow_neg_mul_exp_mul_upperIncompleteGamma a hz] at h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [one_mul, Nat.add_sub_cancel]
    exact upperIncompleteGammaContFracSolution_add_two a hz m

end Complex

end
