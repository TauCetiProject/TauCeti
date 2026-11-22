/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SumIntegralComparisons

/-!
# The first Stieltjes constant

The first Stieltjes constant is
`γ₁ = lim_{N → ∞} (∑_{n ≤ N} (log n) / n - (log N)² / 2) = -0.0728158…`. It is the coefficient
in the Laurent expansion `ζ(1 + s) = 1/s + γ - γ₁ s + O(s²)` of the Riemann zeta function at `1`
(that expansion is not proved here), and it enters explicit estimates for divisor sums through
the constant term `γ² - 2γ₁` of `∑_{n ≤ t} τ(n) / n`.

We define `γ₁` as the limit, in the same way as Mathlib defines Euler's constant
`Real.eulerMascheroniConstant`, prove that the limit exists, and give the explicit remainder
`∑_{n ≤ x} (log n) / n = (log x)² / 2 + γ₁ + O*((log x) / x)` for every real `x ≥ 3`, where the
sum runs over the natural numbers `1 ≤ n ≤ x` and `O*(h)` denotes a quantity of absolute value at
most `h`. Since `t ↦ (log t) / t` decreases on `[3, ∞)`, both follow from the integral-test
comparison `AntitoneOn.abs_sum_Ioc_natFloor_sub_integral_sub_le`.

## Main results

* `TauCeti.stieltjesGammaOne`: the first Stieltjes constant `γ₁`.
* `TauCeti.tendsto_sum_log_div_sub_log_sq_div_two`: the partial sums
  `∑_{n ≤ N} (log n) / n - (log N)² / 2` tend to `γ₁`.
* `TauCeti.abs_sum_log_div_sub_log_sq_div_two_sub_stieltjesGammaOne_le`: for every real `x ≥ 3`,
  `|∑_{n ≤ x} (log n) / n - (log x)² / 2 - γ₁| ≤ (log x) / x`.
* `TauCeti.stieltjesGammaOne_le_sum_log_div_sub_log_sq_div_two`: for every natural `N ≥ 3`,
  the partial sum `∑_{n ≤ N} (log n) / n - (log N)² / 2` is at least `γ₁`.

## References

* T. J. Stieltjes, letter to C. Hermite of 1885, in *Correspondance d'Hermite et de Stieltjes*,
  vol. I, Gauthier-Villars, 1905: the constants `γₖ` as limits of this kind.
* K. Berkane, O. Bordellès, O. Ramaré, *Explicit upper bounds for the remainder term in the
  divisor problem*, Math. Comp. 81 (2012), equation (2.2): the use of `γ₁` in explicit divisor
  sums.
-/

public section

open Filter Finset Real
open scoped Topology

namespace TauCeti

/-- The first Stieltjes constant
`γ₁ = lim_{N → ∞} (∑_{n ≤ N} (log n) / n - (log N)² / 2)`, the sum running over
`Finset.Icc 1 N`. Its value is `-0.0728158…`; the limit exists by
`TauCeti.tendsto_sum_log_div_sub_log_sq_div_two`. -/
noncomputable def stieltjesGammaOne : ℝ :=
  limUnder atTop fun N : ℕ => ∑ n ∈ Icc 1 N, Real.log n / n - Real.log N ^ 2 / 2

private lemma antitoneOn_log_div_self :
    AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Ici ((3 : ℕ) : ℝ)) :=
  Real.log_div_self_antitoneOn.mono fun x hx =>
    Set.mem_Ici.2 <| exp_one_lt_three.le.trans <| by simpa using hx

private lemma log_div_self_nonneg : ∀ x ∈ Set.Ici ((3 : ℕ) : ℝ), 0 ≤ Real.log x / x :=
  fun x hx => by
    have h3 : (3 : ℝ) ≤ x := by simpa using hx
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)

/-- Above `3`, the partial sum minus `(log x)² / 2` is the integral-test difference from `3` on,
shifted by the terms `n ≤ 3`. -/
private lemma sum_log_div_sub_eq {x : ℝ} (hx : 3 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, Real.log n / n - Real.log x ^ 2 / 2 =
      (∑ n ∈ Ioc 3 ⌊x⌋₊, Real.log n / n - ∫ t in ((3 : ℕ) : ℝ)..x, Real.log t / t) +
        (∑ n ∈ Icc (1 : ℕ) 3, Real.log n / n - Real.log 3 ^ 2 / 2) := by
  have h3 : 3 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hIcc (b : ℕ) : Icc 1 b = Ioc 0 b := Icc_add_one_left_eq_Ioc 0 b
  rw [integral_log_div_self (by rw [Set.mem_uIcc]; push_cast; rintro (h | h) <;> linarith [h.1]),
    hIcc, hIcc, ← sum_Ioc_consecutive _ (Nat.zero_le 3) h3]
  push_cast
  ring

private lemma sum_log_div_sub_eq_natCast {N : ℕ} (hN : 3 ≤ N) :
    ∑ n ∈ Icc 1 N, Real.log n / n - Real.log N ^ 2 / 2 =
      (∑ n ∈ Ioc 3 N, Real.log n / n - ∫ t in ((3 : ℕ) : ℝ)..N, Real.log t / t) +
        (∑ n ∈ Icc (1 : ℕ) 3, Real.log n / n - Real.log 3 ^ 2 / 2) := by
  have h := sum_log_div_sub_eq (x := N) (by exact_mod_cast hN)
  rwa [Nat.floor_natCast] at h

private lemma exists_tendsto_and_eq :
    ∃ C, Tendsto (fun N : ℕ => ∑ n ∈ Ioc 3 N, Real.log n / n -
        ∫ t in ((3 : ℕ) : ℝ)..N, Real.log t / t) atTop (𝓝 C) ∧
      Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, Real.log n / n - Real.log N ^ 2 / 2) atTop
        (𝓝 (C + (∑ n ∈ Icc (1 : ℕ) 3, Real.log n / n - Real.log 3 ^ 2 / 2))) := by
  obtain ⟨C, hC⟩ :=
    antitoneOn_log_div_self.exists_tendsto_sum_Ioc_sub_integral log_div_self_nonneg
  refine ⟨C, hC, (hC.add_const _).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 3] with N hN
  exact (sum_log_div_sub_eq_natCast hN).symm

/-- The partial sums `∑_{n ≤ N} (log n) / n - (log N)² / 2` tend to the first Stieltjes
constant. -/
theorem tendsto_sum_log_div_sub_log_sq_div_two :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, Real.log n / n - Real.log N ^ 2 / 2) atTop
      (𝓝 stieltjesGammaOne) := by
  obtain ⟨C, -, h⟩ := exists_tendsto_and_eq
  rwa [stieltjesGammaOne, h.limUnder_eq]

/-- The first Stieltjes constant with an explicit remainder: for every real `x ≥ 3`,
`∑_{n ≤ x} (log n) / n = (log x)² / 2 + γ₁ + O*((log x) / x)`, the sum running over the natural
numbers `1 ≤ n ≤ x`. -/
theorem abs_sum_log_div_sub_log_sq_div_two_sub_stieltjesGammaOne_le {x : ℝ} (hx : 3 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, Real.log n / n - Real.log x ^ 2 / 2 - stieltjesGammaOne| ≤
      Real.log x / x := by
  obtain ⟨C, hC, h⟩ := exists_tendsto_and_eq
  rw [tendsto_nhds_unique h tendsto_sum_log_div_sub_log_sq_div_two |>.symm, sum_log_div_sub_eq hx,
    add_sub_add_right_eq_sub]
  exact antitoneOn_log_div_self.abs_sum_Ioc_natFloor_sub_integral_sub_le log_div_self_nonneg hC
    (by exact_mod_cast hx)

/-- For every natural `N ≥ 3`, the partial sum `∑_{n ≤ N} (log n) / n - (log N)² / 2` is at least
the first Stieltjes constant, which it approaches from above. -/
theorem stieltjesGammaOne_le_sum_log_div_sub_log_sq_div_two {N : ℕ} (hN : 3 ≤ N) :
    stieltjesGammaOne ≤ ∑ n ∈ Icc 1 N, Real.log n / n - Real.log N ^ 2 / 2 := by
  obtain ⟨C, hC, h⟩ := exists_tendsto_and_eq
  rw [tendsto_nhds_unique h tendsto_sum_log_div_sub_log_sq_div_two |>.symm,
    sum_log_div_sub_eq_natCast hN]
  grw [antitoneOn_log_div_self.le_sum_Ioc_sub_integral hC hN]

end TauCeti
