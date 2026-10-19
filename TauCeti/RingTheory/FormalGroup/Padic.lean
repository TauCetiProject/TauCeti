/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.BaseChange
public import TauCeti.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Convergence of integral formal group logarithms

If `F` is a formal group law over `ℤ_[p]`, its normalized invariant differential has integral
coefficients. The logarithm of its scalar extension to `ℚ_[p]` therefore has coefficients `bₙ`
with `n bₙ` integral and `‖bₙ‖ ≤ n`. Consequently the logarithm converges absolutely at every
`p`-adic parameter of norm less than one, including when `p = 2`.

This applies in particular to `W.formalGroup` for an integral Weierstrass equation `W`. It is a
convergence statement for the logarithm series, not a claim that the exponential converges on
the same disc or that logarithmic evaluation is injective on that disc.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5–6.
-/

public section

namespace FormalGroup

variable {p : ℕ} [Fact p.Prime] (F : FormalGroup ℤ_[p])

/-- Multiplying the positive-degree logarithm coefficient by its degree gives a `p`-adic
integer, namely the corresponding coefficient of the integral invariant differential. -/
theorem norm_natCast_mul_coeff_log_le_one (n : ℕ) :
    ‖(n + 1 : ℚ_[p]) *
      PowerSeries.coeff (n + 1) (F.map (algebraMap ℤ_[p] ℚ_[p])).log‖ ≤ 1 := by
  rw [F.natCast_mul_coeff_log_map]
  exact PadicInt.norm_le_one _

/-- The norm of the degree-`n` coefficient of an integral formal group's logarithm is at most
`n`. The constant coefficient is zero. -/
theorem norm_coeff_log_le (n : ℕ) :
    ‖PowerSeries.coeff n (F.map (algebraMap ℤ_[p] ℚ_[p])).log‖ ≤ n := by
  cases n with
  | zero => simp
  | succ n =>
    have h := F.norm_natCast_mul_coeff_log_le_one n
    rw [norm_mul] at h
    have hn : 0 < ‖(n + 1 : ℚ_[p])‖ := norm_pos_iff.mpr (by exact_mod_cast Nat.succ_ne_zero n)
    have hb : ‖PowerSeries.coeff (n + 1) (F.map (algebraMap ℤ_[p] ℚ_[p])).log‖ ≤
        ‖(n + 1 : ℚ_[p])‖⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hn).mpr
      simpa only [mul_comm] using h
    have hi : (n + 1 : ℝ)⁻¹ ≤ ‖(n + 1 : ℚ_[p])‖ := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Padic.inv_natCast_le_norm_natCast (p := p) (n + 1)
    have hi' : ‖(n + 1 : ℚ_[p])‖⁻¹ ≤ (n + 1 : ℝ) := by
      simpa only [inv_inv] using inv_anti₀ (by positivity : 0 < (n + 1 : ℝ)⁻¹) hi
    simpa only [Nat.cast_add, Nat.cast_one] using hb.trans hi'

/-- The logarithm of a formal group over the `p`-adic integers converges absolutely throughout
the open unit disc of `ℚ_[p]`. -/
theorem summable_norm_coeff_log_mul_pow {t : ℚ_[p]} (ht : ‖t‖ < 1) :
    Summable (fun n : ℕ ↦
      ‖PowerSeries.coeff n (F.map (algebraMap ℤ_[p] ℚ_[p])).log * t ^ n‖) := by
  have hs : Summable (fun n : ℕ ↦ (n : ℝ) * ‖t‖ ^ n) := by
    simpa [norm_mul] using
      summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := ‖t‖) 1
        (by simpa only [Real.norm_eq_abs, abs_norm] using ht)
  apply hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (F.norm_coeff_log_le n) (by positivity)

/-- The logarithm series of an integral formal group is summable at every parameter of norm
less than one. Its value can therefore be taken by `tsum` without a nonconvergence junk value. -/
theorem summable_coeff_log_mul_pow {t : ℚ_[p]} (ht : ‖t‖ < 1) :
    Summable (fun n : ℕ ↦
      PowerSeries.coeff n (F.map (algebraMap ℤ_[p] ℚ_[p])).log * t ^ n) :=
  (F.summable_norm_coeff_log_mul_pow ht).of_norm

end FormalGroup
