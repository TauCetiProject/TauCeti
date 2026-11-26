/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Entropy.Pressure
import Mathlib.Analysis.MeanInequalities
import TauCeti.Analysis.Asymptotics.ExpGrowth
import TauCeti.Data.EReal.Operations
import TauCeti.Dynamics.BirkhoffSum.Basic

/-!
# Convexity of topological pressure

For a map `T : X → X` of a uniform space, the topological pressure `φ ↦ P(T, φ)` is convex:
for `0 ≤ t ≤ 1`, `P(T, t • φ + (1 - t) • ψ) ≤ t * P(T, φ) + (1 - t) * P(T, ψ)` in `EReal`,
unless one of `P(T, φ)` and `P(T, ψ)` is `⊤` and the other `⊥`. The proof applies Hölder's
inequality with exponents `1 / t` and `1 / (1 - t)` to the sum over each dynamical net: the weight
of the combined potential at `x` is
`exp (birkhoffSum T φ n x) ^ t * exp (birkhoffSum T ψ n x) ^ (1 - t)`.

The hypotheses exclude only the indeterminate sum `⊤ + ⊥` on the right, where the pressure of
one potential grows faster than any exponential and that of the other decays faster. When one
pressure is `⊤` and the other is not `⊥`, the right-hand side is `⊤`.

## Main results

* `TauCeti.pressureNetSum_smul_add_smul_le`: the pressure sum of `t • φ + (1 - t) • ψ` is at most
  `pressureNetSum T φ U n ^ t * pressureNetSum T ψ U n ^ (1 - t)`.
* `TauCeti.netPressureEntourage_smul_add_smul_le`: convexity of the pressure at an entourage.
* `TauCeti.topologicalPressure_smul_add_smul_le`: convexity of the topological pressure.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, Theorem 9.7: convexity of the pressure, proved by Hölder's inequality on the sums over
  separated sets.
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
    rw [birkhoffSum_add_apply, birkhoffSum_smul_apply, birkhoffSum_smul_apply, smul_eq_mul,
      smul_eq_mul]
  rw [hsum, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity),
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  ring_nf

/-- **Hölder's inequality for pressure sums.** For `0 < t < 1`, the pressure sum of
`t • φ + (1 - t) • ψ` is at most `pressureNetSum T φ U n ^ t * pressureNetSum T ψ U n ^ (1 - t)`.
-/
theorem pressureNetSum_smul_add_smul_le (ht₀ : 0 < t) (ht₁ : t < 1) (T : X → X) (φ ψ : X → ℝ)
    (U : SetRel X X) (n : ℕ) :
    pressureNetSum T (t • φ + (1 - t) • ψ) U n ≤
      pressureNetSum T φ U n ^ t * pressureNetSum T ψ U n ^ (1 - t) := by
  have hpq := Real.holderConjugate_one_div ht₀ (sub_pos.mpr ht₁) (add_sub_cancel t 1)
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

/-- **Convexity at an entourage.** For `0 < t < 1`, unless one of the pressures of `φ` and `ψ`
at the entourage `U` is `⊤` and the other `⊥`, the pressure of `t • φ + (1 - t) • ψ` at `U` is at
most `t * netPressureEntourage T φ U + (1 - t) * netPressureEntourage T ψ U`. -/
theorem netPressureEntourage_smul_add_smul_le (ht₀ : 0 < t) (ht₁ : t < 1)
    (h : netPressureEntourage T φ U ≠ ⊤ ∨ netPressureEntourage T ψ U ≠ ⊥)
    (h' : netPressureEntourage T φ U ≠ ⊥ ∨ netPressureEntourage T ψ U ≠ ⊤) :
    netPressureEntourage T (t • φ + (1 - t) • ψ) U ≤
      t * netPressureEntourage T φ U + ((1 - t : ℝ) : EReal) * netPressureEntourage T ψ U := by
  have h1t : (0 : ℝ) < 1 - t := sub_pos.mpr ht₁
  by_cases hT : netPressureEntourage T φ U = ⊤ ∨ netPressureEntourage T ψ U = ⊤
  · rw [EReal.coe_mul_add_coe_mul_eq_top_of_ne_or_ne ht₀ h1t h h' hT]
    exact le_top
  obtain ⟨hφ, hψ⟩ := not_or.mp hT
  replace h1t := h1t.le
  rw [netPressureEntourage_def] at hφ hψ ⊢
  rw [netPressureEntourage_def, netPressureEntourage_def, ← expGrowthSup_rpow ht₀.le,
    ← expGrowthSup_rpow h1t]
  refine (expGrowthSup_monotone fun n ↦
    pressureNetSum_smul_add_smul_le ht₀ ht₁ T φ ψ U n).trans (expGrowthSup_mul_le ?_ ?_)
  · right
    rw [expGrowthSup_rpow h1t]
    simp [EReal.mul_ne_top, h1t, hψ, -EReal.coe_sub]
  · left
    rw [expGrowthSup_rpow ht₀.le]
    simp [EReal.mul_ne_top, ht₀.le, hφ]

/-- **Convexity of topological pressure.** For `0 ≤ t ≤ 1`, unless one of `P(T, φ)` and
`P(T, ψ)` is `⊤` and the other `⊥`, `P(T, t • φ + (1 - t) • ψ) ≤ t * P(T, φ) + (1 - t) * P(T, ψ)`.
-/
theorem topologicalPressure_smul_add_smul_le [UniformSpace X] (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (h : topologicalPressure T φ ≠ ⊤ ∨ topologicalPressure T ψ ≠ ⊥)
    (h' : topologicalPressure T φ ≠ ⊥ ∨ topologicalPressure T ψ ≠ ⊤) :
    topologicalPressure T (t • φ + (1 - t) • ψ) ≤
      t * topologicalPressure T φ + ((1 - t : ℝ) : EReal) * topologicalPressure T ψ := by
  rcases ht₀.eq_or_lt with rfl | ht₀
  · simp
  rcases ht₁.eq_or_lt with rfl | ht₁
  · simp
  by_cases hT : topologicalPressure T φ = ⊤ ∨ topologicalPressure T ψ = ⊤
  · rw [EReal.coe_mul_add_coe_mul_eq_top_of_ne_or_ne ht₀ (sub_pos.mpr ht₁) h h' hT]
    exact le_top
  obtain ⟨hφ, hψ⟩ := not_or.mp hT
  rw [topologicalPressure_le_iff]
  intro U hU
  have hφU : netPressureEntourage T φ U ≠ ⊤ :=
    ne_top_of_le_ne_top hφ (netPressureEntourage_le_topologicalPressure hU)
  have hψU : netPressureEntourage T ψ U ≠ ⊤ :=
    ne_top_of_le_ne_top hψ (netPressureEntourage_le_topologicalPressure hU)
  refine (netPressureEntourage_smul_add_smul_le ht₀ ht₁ (.inl hφU) (.inr hψU)).trans ?_
  gcongr <;> exact netPressureEntourage_le_topologicalPressure hU

end TauCeti
