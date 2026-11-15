/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Integral measures are `1`-Lipschitz

A `ℤ_p`-valued measure `μ` on a topological space sends a test function whose values all have norm
at most `p⁻ᵏ` to an element of norm at most `p⁻ᵏ`
(`AbstractMeasure.norm_apply_le_of_forall_norm_le`): such a test function is `pᵏ` times a test
function, so its integral is divisible by `pᵏ`. On a compact space this gives
`‖μ f‖ ≤ ‖f‖` for the supremum norm (`AbstractMeasure.norm_apply_le`). This is the uniform bound
that makes the integral measures behave like a dual unit ball.

## Main results

* `AbstractMeasure.norm_apply_le_of_forall_norm_le`: a pointwise bound `‖f x‖ ≤ p⁻ᵏ` on a test
  function bounds its integral by `p⁻ᵏ`.
* `AbstractMeasure.norm_apply_le`: on a compact space, every `ℤ_p`-valued measure is `1`-Lipschitz
  for the supremum norm.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, §3.
-/

public section

open scoped AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

namespace AbstractMeasure

variable {X : Type*} [TopologicalSpace X]

/-- A test function whose values all have norm at most `p⁻ᵏ` is `pᵏ` times a `ℤ_p`-valued test
function, so its integral has norm at most `p⁻ᵏ`. -/
theorem norm_apply_le_of_forall_norm_le (μ : D(X, ℤ_[p])) {f : C(X, ℤ_[p])} {k : ℕ}
    (hf : ∀ x, ‖f x‖ ≤ (p : ℝ) ^ (-k : ℤ)) : ‖μ f‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
  have hp : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
  -- Divide `f` by `p ^ k` inside `ℚ_p`; the quotient still takes values in `ℤ_p`.
  have hmem : ∀ x, ‖(f x : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1 := fun x ↦ by
    rw [norm_div, norm_pow, Padic.norm_p, ← PadicInt.norm_def, div_le_one (by positivity),
      inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hf x
  let g : C(X, ℤ_[p]) := ⟨fun x ↦ Padic.lift _ (hmem x),
    ((continuous_subtype_val.comp f.continuous).div_const _).subtype_mk hmem⟩
  have hg : ∀ x, (g x : ℚ_[p]) = f x / (p : ℚ_[p]) ^ k := fun _ ↦ rfl
  have hfg : f = (p : ℤ_[p]) ^ k • g := by
    ext x
    have : (p : ℚ_[p]) ^ k ≠ 0 := pow_ne_zero _ (mod_cast (Fact.out : p.Prime).ne_zero)
    simp [hg, mul_div_cancel₀ _ this]
  rw [hfg, map_smul, smul_eq_mul, norm_mul, PadicInt.norm_p_pow]
  exact mul_le_of_le_one_right (zpow_nonneg hp.le _) (PadicInt.norm_le_one _)

/-- **Integral measures are `1`-Lipschitz.** On a compact space, every `ℤ_p`-valued measure
satisfies `‖μ f‖ ≤ ‖f‖` for the supremum norm on test functions. -/
theorem norm_apply_le [CompactSpace X] (μ : D(X, ℤ_[p])) (f : C(X, ℤ_[p])) : ‖μ f‖ ≤ ‖f‖ := by
  by_contra! h
  have hμf : μ f ≠ 0 := by
    rintro h0
    rw [h0, norm_zero] at h
    exact (norm_nonneg f).not_gt h
  rw [PadicInt.norm_eq_zpow_neg_valuation hμf] at h
  -- Every value of `f` has norm below `‖μ f‖ = p ^ (-v)`, hence at most `p ^ (-(v + 1))`.
  have hle : ∀ x, ‖f x‖ ≤ (p : ℝ) ^ (-((μ f).valuation + 1 : ℕ) : ℤ) := fun x ↦ by
    rw [Nat.cast_succ, neg_add, ← sub_eq_add_neg]
    exact (PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one _ _).mp
      ((f.norm_coe_le_norm x).trans_lt h)
  have hμ := norm_apply_le_of_forall_norm_le μ hle
  rw [PadicInt.norm_eq_zpow_neg_valuation hμf] at hμ
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  exact (zpow_lt_zpow_right₀ hp (by omega)).not_ge hμ

end AbstractMeasure
