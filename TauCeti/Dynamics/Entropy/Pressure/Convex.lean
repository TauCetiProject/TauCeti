/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Entropy.Pressure
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import TauCeti.Analysis.Asymptotics.ExpGrowth

/-!
# Convexity of topological pressure

For a map `T : X → X` of a uniform space, the topological pressure `φ ↦ P(T, φ)` is convex:
for `0 ≤ t ≤ 1`, `P(T, t • φ + (1 - t) • ψ) ≤ t * P(T, φ) + (1 - t) * P(T, ψ)` in `EReal`,
provided `P(T, φ)` and `P(T, ψ)` are not `⊤`. The proof applies Hölder's inequality with exponents
`1 / t` and `1 / (1 - t)` to the sum over each dynamical net: the weight of the combined potential
at `x` is
`exp (birkhoffSum T φ n x) ^ t * exp (birkhoffSum T ψ n x) ^ (1 - t)`.

The finiteness hypotheses exclude the indeterminate sum `⊤ + ⊥` on the right, where the
pressure of one potential grows faster than any exponential and that of the other decays faster.

## Main results

* `TauCeti.pressureNetSum_smul_add_smul_le`: the pressure sum of `t • φ + (1 - t) • ψ` is at most
  `pressureNetSum T φ U n ^ t * pressureNetSum T ψ U n ^ (1 - t)`.
* `TauCeti.netPressureEntourage_smul_add_smul_le`: convexity of the pressure at an entourage.
* `TauCeti.topologicalPressure_smul_add_smul_le`: convexity of the topological pressure.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped ENNReal Uniformity

variable {X : Type*} {T : X → X} {φ ψ : X → ℝ} {U : SetRel X X} {t : ℝ}

/-- The Birkhoff sums of `t • φ + (1 - t) • ψ` give the weights
`exp (birkhoffSum T φ n x) ^ t * exp (birkhoffSum T ψ n x) ^ (1 - t)`. -/
private theorem ofReal_exp_birkhoffSum_smul_add_smul (T : X → X) (φ ψ : X → ℝ) (t : ℝ) (n : ℕ)
    (x : X) :
    ENNReal.ofReal (Real.exp (birkhoffSum T (t • φ + (1 - t) • ψ) n x)) =
      ENNReal.ofReal (Real.exp (birkhoffSum T φ n x)) ^ t *
        ENNReal.ofReal (Real.exp (birkhoffSum T ψ n x)) ^ (1 - t) := by
  have hsum : birkhoffSum T (t • φ + (1 - t) • ψ) n x =
      t * birkhoffSum T φ n x + (1 - t) * birkhoffSum T ψ n x := by
    simp only [birkhoffSum, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
  rw [hsum, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm t, mul_comm (1 - t),
    Real.exp_mul, Real.exp_mul, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)]

/-- **Hölder's inequality for pressure sums.** For `0 < t < 1`, the pressure sum of
`t • φ + (1 - t) • ψ` is at most `pressureNetSum T φ U n ^ t * pressureNetSum T ψ U n ^ (1 - t)`.
-/
theorem pressureNetSum_smul_add_smul_le (ht₀ : 0 < t) (ht₁ : t < 1) (T : X → X) (φ ψ : X → ℝ)
    (U : SetRel X X) (n : ℕ) :
    pressureNetSum T (t • φ + (1 - t) • ψ) U n ≤
      pressureNetSum T φ U n ^ t * pressureNetSum T ψ U n ^ (1 - t) := by
  have hpq : (1 / t).HolderConjugate (1 / (1 - t)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ ht₀, one_mul]
      exact ht₁
    · simp only [one_div, inv_inv]
      ring
  rw [pressureNetSum_le_iff]
  intro s hs
  set f : X → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (birkhoffSum T φ n x))
  set g : X → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (birkhoffSum T ψ n x))
  have hft : ∀ x, (f x ^ t) ^ (1 / t) = f x := fun x ↦ by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel ht₀.ne', ENNReal.rpow_one]
  have hgt : ∀ x, (g x ^ (1 - t)) ^ (1 / (1 - t)) = g x := fun x ↦ by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (sub_pos.mpr ht₁).ne', ENNReal.rpow_one]
  calc ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T (t • φ + (1 - t) • ψ) n x))
      = ∑ x ∈ s, f x ^ t * g x ^ (1 - t) :=
        Finset.sum_congr rfl fun x _ ↦ ofReal_exp_birkhoffSum_smul_add_smul T φ ψ t n x
    _ ≤ (∑ x ∈ s, (f x ^ t) ^ (1 / t)) ^ (1 / (1 / t)) *
          (∑ x ∈ s, (g x ^ (1 - t)) ^ (1 / (1 - t))) ^ (1 / (1 / (1 - t))) :=
        ENNReal.inner_le_Lp_mul_Lq s _ _ hpq
    _ = (∑ x ∈ s, f x) ^ t * (∑ x ∈ s, g x) ^ (1 - t) := by
        simp only [hft, hgt, one_div_one_div]
    _ ≤ pressureNetSum T φ U n ^ t * pressureNetSum T ψ U n ^ (1 - t) := by
        gcongr
        · exact hs.sum_le_pressureNetSum
        · exact hs.sum_le_pressureNetSum

/-- A nonnegative real multiple of an extended real other than `⊤` is not `⊤`. -/
private theorem coe_mul_ne_top {c : ℝ} (hc : 0 ≤ c) {a : EReal} (ha : a ≠ ⊤) :
    (c : EReal) * a ≠ ⊤ :=
  (EReal.mul_ne_top _ _).mpr ⟨.inl (EReal.coe_ne_bot c), .inl (EReal.coe_nonneg.mpr hc),
    .inl (EReal.coe_ne_top c), .inr ha⟩

/-- **Convexity at an entourage.** For `0 < t < 1`, if the pressures of `φ` and `ψ` at the
entourage `U` are not `⊤`, then the pressure of `t • φ + (1 - t) • ψ` at `U` is at most
`t * netPressureEntourage T φ U + (1 - t) * netPressureEntourage T ψ U`. -/
theorem netPressureEntourage_smul_add_smul_le (ht₀ : 0 < t) (ht₁ : t < 1)
    (hφ : netPressureEntourage T φ U ≠ ⊤) (hψ : netPressureEntourage T ψ U ≠ ⊤) :
    netPressureEntourage T (t • φ + (1 - t) • ψ) U ≤
      t * netPressureEntourage T φ U + ((1 - t : ℝ) : EReal) * netPressureEntourage T ψ U := by
  have h1t : (0 : ℝ) ≤ 1 - t := (sub_pos.mpr ht₁).le
  rw [netPressureEntourage_def] at hφ hψ ⊢
  rw [netPressureEntourage_def, netPressureEntourage_def, ← expGrowthSup_rpow ht₀.le,
    ← expGrowthSup_rpow h1t]
  refine (expGrowthSup_monotone fun n ↦
    pressureNetSum_smul_add_smul_le ht₀ ht₁ T φ ψ U n).trans (expGrowthSup_mul_le ?_ ?_)
  · right
    rw [expGrowthSup_rpow h1t]
    exact coe_mul_ne_top h1t hψ
  · left
    rw [expGrowthSup_rpow ht₀.le]
    exact coe_mul_ne_top ht₀.le hφ

/-- **Convexity of topological pressure.** For `0 ≤ t ≤ 1`, if `P(T, φ)` and `P(T, ψ)` are not
`⊤`, then `P(T, t • φ + (1 - t) • ψ) ≤ t * P(T, φ) + (1 - t) * P(T, ψ)`. -/
theorem topologicalPressure_smul_add_smul_le [UniformSpace X] (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hφ : topologicalPressure T φ ≠ ⊤) (hψ : topologicalPressure T ψ ≠ ⊤) :
    topologicalPressure T (t • φ + (1 - t) • ψ) ≤
      t * topologicalPressure T φ + ((1 - t : ℝ) : EReal) * topologicalPressure T ψ := by
  rcases ht₀.eq_or_lt with rfl | ht₀
  · simp
  rcases ht₁.eq_or_lt with rfl | ht₁
  · simp
  rw [topologicalPressure_le_iff]
  intro U hU
  have hφU : netPressureEntourage T φ U ≠ ⊤ :=
    ne_top_of_le_ne_top hφ (netPressureEntourage_le_topologicalPressure hU)
  have hψU : netPressureEntourage T ψ U ≠ ⊤ :=
    ne_top_of_le_ne_top hψ (netPressureEntourage_le_topologicalPressure hU)
  refine (netPressureEntourage_smul_add_smul_le ht₀ ht₁ hφU hψU).trans ?_
  gcongr <;> exact netPressureEntourage_le_topologicalPressure hU

end TauCeti
