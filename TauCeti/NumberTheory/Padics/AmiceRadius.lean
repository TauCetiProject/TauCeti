/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.Padics.Basic
import Mathlib.Analysis.Normed.Ring.Ultra
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The Amice radii and the sharp `p`-adic factorial bound

This module defines the Amice radii
`TauCeti.amiceRadius p h = p ^ (-1 / ((p - 1) pʰ))`
and establishes their basic inequalities together with the sharp level-zero factorial lower bound
`r₀ ^ (n - 1) ≤ ‖(n! : L)‖` (`TauCeti.amiceRadius_zero_pow_sub_one_le_norm_factorial`) in every
seminormed `ℚ_[p]`-algebra with `‖(1 : L)‖ = 1`.

These results live below `TauCeti.NumberTheory.Padics.Factorial` so both factorial estimates and
the `p`-adic exponential API can share them without an import cycle with
`TauCeti.NumberTheory.Padics.Distribution.Amice.Norm`.

## Main definitions

* `TauCeti.amiceRadius p h`: the radius `p ^ (-1 / ((p - 1) pʰ))`.

## Main results

* `TauCeti.amiceRadius_zero`: `amiceRadius p 0 = p ^ (-((p : ℝ) - 1)⁻¹)`.
* `TauCeti.amiceRadius_pos`, `TauCeti.amiceRadius_lt_one`, `TauCeti.amiceRadius_pow`.
* `TauCeti.amiceRadius_zero_pow_sub_one`, `TauCeti.inv_lt_amiceRadius_zero_iff`,
  `TauCeti.zpow_neg_lt_amiceRadius_zero`.
* `TauCeti.amiceRadius_succ_pow`, `TauCeti.strictMono_amiceRadius`, `TauCeti.tendsto_amiceRadius`.
* `TauCeti.amiceRadius_zero_pow_sub_one_le_norm_factorial` and
  `TauCeti.amiceRadius_zero_pow_sub_one_le_norm_natCast`: the sharp level-zero lower bounds
  `r₀ ^ (n - 1) ≤ ‖(n! : L)‖` and `r₀ ^ (n - 1) ≤ ‖(n : L)‖` for `n ≠ 0`.
-/

public section

open Filter Topology Nat

namespace TauCeti

variable (p : ℕ) [hp : Fact p.Prime]

/-- The radius `r_h = p ^ (-1 / ((p - 1) pʰ))` attached to the analytic level `h`: the `pʰ`-th
root of the radius of convergence `p ^ (-1 / (p - 1))` of the `p`-adic exponential. The Gauss
norm of an Amice transform at this radius is comparable with its dual stage norm at level `h`. -/
noncomputable def amiceRadius (h : ℕ) : ℝ :=
  (p : ℝ) ^ (-(1 / (((p : ℝ) - 1) * (p : ℝ) ^ h)))

omit hp in
/-- The closed form of the radius `r_h`. -/
theorem amiceRadius_def (h : ℕ) :
    amiceRadius p h = (p : ℝ) ^ (-(1 / (((p : ℝ) - 1) * (p : ℝ) ^ h))) :=
  (rfl)

omit hp in
/-- The level-zero radius `r₀ = p ^ (-1 / (p - 1))`, the radius of convergence of the `p`-adic
exponential. -/
theorem amiceRadius_zero : amiceRadius p 0 = (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
  simp [amiceRadius_def]

variable {p}

private theorem one_lt_natCast : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

private theorem natCast_pos : (0 : ℝ) < p := zero_lt_one.trans (one_lt_natCast (p := p))

private theorem sub_one_pos : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr (one_lt_natCast (p := p))

/-- The radii `r_h` are positive. -/
theorem amiceRadius_pos (h : ℕ) : 0 < amiceRadius p h :=
  Real.rpow_pos_of_pos natCast_pos _

/-- The radii `r_h` are smaller than `1`. -/
theorem amiceRadius_lt_one (h : ℕ) : amiceRadius p h < 1 := by
  refine Real.rpow_lt_one_of_one_lt_of_neg one_lt_natCast (neg_neg_of_pos ?_)
  have := sub_one_pos (p := p)
  have := natCast_pos (p := p)
  positivity

omit hp in
/-- The `n`-th power of `r_h` is `p ^ (-n / ((p - 1) pʰ))`. -/
theorem amiceRadius_pow (h n : ℕ) :
    amiceRadius p h ^ n = (p : ℝ) ^ (-((n : ℝ) / (((p : ℝ) - 1) * (p : ℝ) ^ h))) := by
  rw [amiceRadius_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- `r_0 ^ (p - 1) = p⁻¹`: the radius `r_0 = p ^ (-1 / (p - 1))` is the radius of convergence of
the `p`-adic exponential. -/
theorem amiceRadius_zero_pow_sub_one : amiceRadius p 0 ^ (p - 1) = (p : ℝ)⁻¹ := by
  rw [amiceRadius_pow, Nat.cast_sub hp.out.one_le, Nat.cast_one, pow_zero, mul_one,
    div_self (sub_one_pos (p := p)).ne', Real.rpow_neg_one]

/-- The prime `p` lies strictly inside the disc of convergence of the `p`-adic exponential,
`‖p‖ = p⁻¹ < r_0 = p ^ (-1 / (p - 1))`, exactly when `p` is odd. At `p = 2` the two are equal. -/
theorem inv_lt_amiceRadius_zero_iff : (p : ℝ)⁻¹ < amiceRadius p 0 ↔ p ≠ 2 := by
  have h2 := hp.out.two_le
  have h := pow_lt_pow_iff_right_of_lt_one₀ (amiceRadius_pos (p := p) 0) (amiceRadius_lt_one 0)
    (m := p - 1) (n := 1)
  rw [pow_one, amiceRadius_zero_pow_sub_one] at h
  rw [h]
  omega

/-- For a depth `i` with `1 < (p - 1) i`, the closed disc of radius `p ^ (-i)` lies inside the
open disc of radius `r_0 = p ^ (-1 / (p - 1))`: `p ^ (-i) < r_0`. -/
theorem zpow_neg_lt_amiceRadius_zero {i : ℕ} (hi : 1 < (p - 1) * i) :
    (p : ℝ) ^ (-(i : ℤ)) < amiceRadius p 0 := by
  have hi' : (1 : ℝ) < ((p : ℝ) - 1) * i := by
    have h := (Nat.cast_lt (α := ℝ)).mpr hi
    push_cast [Nat.cast_sub hp.out.one_le] at h
    exact h
  rw [← Real.rpow_intCast, amiceRadius_def]
  refine Real.rpow_lt_rpow_of_exponent_lt one_lt_natCast ?_
  push_cast
  rw [neg_lt_neg_iff, pow_zero, mul_one, div_lt_iff₀ sub_one_pos]
  linarith

/-- `r_{h+1} ^ p = r_h`: each radius is the `p`-th root of the previous one. -/
theorem amiceRadius_succ_pow (h : ℕ) : amiceRadius p (h + 1) ^ p = amiceRadius p h := by
  have := natCast_pos (p := p)
  have := sub_one_pos (p := p)
  rw [amiceRadius_pow, amiceRadius_def, pow_succ]
  congr 1
  field_simp

/-- The radii `r_h` increase strictly with the level `h`. -/
theorem strictMono_amiceRadius : StrictMono (amiceRadius p) := by
  refine strictMono_nat_of_lt_succ fun h ↦ Real.rpow_lt_rpow_of_exponent_lt one_lt_natCast ?_
  have := sub_one_pos (p := p)
  have := natCast_pos (p := p)
  rw [neg_lt_neg_iff, pow_succ]
  gcongr
  exact lt_mul_of_one_lt_right (by positivity) one_lt_natCast

omit hp in
/-- The radii `r_h` tend to `1`. -/
theorem tendsto_amiceRadius : Tendsto (amiceRadius p) atTop (𝓝 1) := by
  rcases lt_or_ge 1 p with hp1 | hp1
  · have h1 : (1 : ℝ) < p := by exact_mod_cast hp1
    refine (tendsto_const_rpow_div_pow_atTop (zero_lt_one.trans h1).ne' h1
      (-(1 / ((p : ℝ) - 1)))).congr fun h ↦ ?_
    simp only [amiceRadius_def, neg_div, div_mul_eq_div_div]
  · -- The degenerate values `p = 0` and `p = 1`: the radii are eventually constant `1`.
    interval_cases p
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with h hh
      simp [amiceRadius, zero_pow (Nat.pos_iff_ne_zero.mp hh)]
    · exact tendsto_const_nhds.congr fun h ↦ by simp [amiceRadius]

/-- **The sharp factorial bound.** In every normed algebra over `ℚ_[p]`,
`r_0 ^ (n - 1) ≤ ‖n!‖` for `n ≠ 0`, where `r_0 = p ^ (-1 / (p - 1))`. Equality holds when `n` is a
power of `p`. This sharpens the case `h = 0` of `TauCeti.amiceRadius_pow_le_norm_factorial`. -/
theorem amiceRadius_zero_pow_sub_one_le_norm_factorial {L : Type*} [SeminormedRing L]
    [NormOneClass L] [NormedAlgebra ℚ_[p] L] {n : ℕ} (hn : n ≠ 0) :
    amiceRadius p 0 ^ (n - 1) ≤ ‖(n ! : L)‖ := by
  rw [norm_natCast_eq_norm_padic (p := p), amiceRadius_pow,
    Padic.norm_natCast_eq_zpow (factorial_ne_zero n), ← Real.rpow_intCast, Int.cast_neg,
    Int.cast_natCast]
  refine Real.rpow_le_rpow_of_exponent_le one_lt_natCast.le ?_
  -- Legendre's formula: `(p - 1) v_p(n!) = n - s_p(n) < n`.
  have hleg : (((p - 1) * padicValNat p n ! : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    have h := sub_one_mul_multiplicity_factorial_lt_of_ne_zero p hn
    rw [← Nat.padicValNat_def] at h
    exact_mod_cast Nat.le_sub_one_of_lt h
  push_cast [Nat.cast_sub hp.out.one_le] at hleg
  rw [pow_zero, mul_one, neg_le_neg_iff, le_div_iff₀ sub_one_pos]
  linarith

/-- In every normed algebra over `ℚ_[p]`, `r_0 ^ (n - 1) ≤ ‖n‖` for `n ≠ 0`, where
`r_0 = p ^ (-1 / (p - 1))`: the factor `n` of `n!` has norm at least `‖n!‖`. This bounds the
coefficients `(-1) ^ (n + 1) / n` of the logarithm series. -/
theorem amiceRadius_zero_pow_sub_one_le_norm_natCast {L : Type*} [SeminormedRing L]
    [NormOneClass L] [NormedAlgebra ℚ_[p] L] {n : ℕ} (hn : n ≠ 0) :
    amiceRadius p 0 ^ (n - 1) ≤ ‖(n : L)‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine (amiceRadius_zero_pow_sub_one_le_norm_factorial (L := ℚ_[p]) hn).trans ?_
  rw [norm_natCast_eq_norm_padic (p := p) (K := L), factorial_succ, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)

end TauCeti
