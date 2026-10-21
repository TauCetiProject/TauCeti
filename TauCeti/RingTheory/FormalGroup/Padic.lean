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
coefficients. The logarithm of its scalar extension to a normed `ℚ_[p]`-algebra field `K`
therefore has coefficients `bₙ` with `n bₙ` integral and `‖bₙ‖ ≤ n`. The logarithm's terms have
summable norms at every parameter of norm less than one, including when `p = 2`. When `K` is
complete, the logarithm series itself is summable there.

This applies in particular to `W.formalGroup` for an integral Weierstrass equation `W`. It is a
convergence statement for the logarithm series, not a claim that the exponential converges on
the same disc or that logarithmic evaluation is injective on that disc.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5–6.
-/

public section

namespace FormalGroup

variable {p : ℕ} [Fact p.Prime] (F : FormalGroup ℤ_[p])
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [Algebra ℚ K]
  [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]

/-- Multiplying the positive-degree logarithm coefficient by its degree gives a `p`-adic
integer's image in `K`, namely the corresponding coefficient of the integral invariant
differential. -/
theorem norm_natCast_mul_coeff_log_le_one (n : ℕ) :
    ‖(n + 1 : K) *
      PowerSeries.coeff (n + 1) (F.map (algebraMap ℤ_[p] K)).log‖ ≤ 1 := by
  rw [F.natCast_mul_coeff_log_map, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K,
    norm_algebraMap', PadicInt.algebraMap_apply, PadicInt.norm_coe]
  exact PadicInt.norm_le_one _

/-- The norm of the degree-`n` coefficient of an integral formal group's logarithm is at most
`n`. The constant coefficient is zero. -/
theorem norm_coeff_log_le (n : ℕ) :
    ‖PowerSeries.coeff n (F.map (algebraMap ℤ_[p] K)).log‖ ≤ n := by
  cases n with
  | zero => simp
  | succ n =>
    have h := F.norm_natCast_mul_coeff_log_le_one (K := K) n
    rw [norm_mul] at h
    have hnorm : ‖(n + 1 : K)‖ = ‖(n + 1 : ℚ_[p])‖ := by
      simpa only [map_add, map_natCast, map_one] using
        norm_algebraMap' K (n + 1 : ℚ_[p])
    have hn : 0 < ‖(n + 1 : K)‖ := by
      rw [hnorm]
      exact norm_pos_iff.mpr (by exact_mod_cast Nat.succ_ne_zero n)
    have hb : ‖PowerSeries.coeff (n + 1) (F.map (algebraMap ℤ_[p] K)).log‖ ≤
        ‖(n + 1 : K)‖⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hn).mpr
      simpa only [mul_comm] using h
    have hi : (n + 1 : ℝ)⁻¹ ≤ ‖(n + 1 : K)‖ := by
      simpa only [hnorm, Nat.cast_add, Nat.cast_one] using
        Padic.inv_natCast_le_norm_natCast (p := p) (n + 1)
    have hi' : ‖(n + 1 : K)‖⁻¹ ≤ (n + 1 : ℝ) := by
      simpa only [inv_inv] using inv_anti₀ (by positivity : 0 < (n + 1 : ℝ)⁻¹) hi
    simpa only [Nat.cast_add, Nat.cast_one] using hb.trans hi'

/-- The logarithm of a formal group over the `p`-adic integers converges absolutely throughout
the open unit disc of any normed `ℚ_[p]`-algebra field. -/
theorem summable_norm_coeff_log_mul_pow {t : K} (ht : ‖t‖ < 1) :
    Summable (fun n : ℕ ↦
      ‖PowerSeries.coeff n (F.map (algebraMap ℤ_[p] K)).log * t ^ n‖) := by
  have hs : Summable (fun n : ℕ ↦ (n : ℝ) * ‖t‖ ^ n) := by
    simpa [norm_mul] using
      summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := ‖t‖) 1
        (by simpa only [Real.norm_eq_abs, abs_norm] using ht)
  apply hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (F.norm_coeff_log_le (K := K) n) (by positivity)

/-- The logarithm series of an integral formal group is summable at every parameter of norm
less than one in a complete normed `ℚ_[p]`-algebra field. Its value can therefore be taken by
`tsum` without a nonconvergence junk value. -/
theorem summable_coeff_log_mul_pow [CompleteSpace K] {t : K} (ht : ‖t‖ < 1) :
    Summable (fun n : ℕ ↦
      PowerSeries.coeff n (F.map (algebraMap ℤ_[p] K)).log * t ^ n) :=
  (F.summable_norm_coeff_log_mul_pow ht).of_norm

end FormalGroup
