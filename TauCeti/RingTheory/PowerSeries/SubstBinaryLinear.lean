/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Coefficients of univariate power series substituted along binary linear forms

For univariate formal power series `g, h : R⟦X⟧` over a commutative ring `R`, this file
computes the bivariate coefficients at `X₀ ^ m * X₁ ^ n` of `g(X₀ + X₁)` and `g(X₀) * h(X₁)`:

* `TauCeti.coeff_subst_X_add_X`: the coefficient of `X₀ ^ m * X₁ ^ n` in `g.subst (X 0 + X 1)` is
  `(m + n).choose m * PowerSeries.coeff (m + n) g`.
* `TauCeti.factorial_mul_coeff_subst_X_add_X`: multiplying by `m ! * n !` yields
  `(m + n)! * PowerSeries.coeff (m + n) g`.
* `TauCeti.coeff_subst_X_mul_subst_X`: the coefficient of `X₀ ^ m * X₁ ^ n` in
  `g.subst (X 0) * h.subst (X 1)` is `PowerSeries.coeff m g * PowerSeries.coeff n h`.

## References

* Provenance: adapted from `New.factorial_mul_coeff_subst_add` and `New.coeff_subst_mul_subst` in
  `grh/src/New/Derivatives/Sharpness/OneCurve.lean` of `grh-lean`
  (https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

namespace TauCeti

open Finset MvPowerSeries

variable {R : Type*} [CommRing R]

/-- The coefficient of `X 0 ^ m * X 1 ^ n` in `g.subst (X 0 + X 1)` is
`(m + n).choose m * PowerSeries.coeff (m + n) g`. -/
theorem coeff_subst_X_add_X (g : PowerSeries R) (m n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n)
      (g.subst (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1)) =
      ((m + n).choose m : R) * PowerSeries.coeff (m + n) g := by
  have h_subst : PowerSeries.HasSubst (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1 :
      MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h_mon (a b : ℕ) : MvPowerSeries.X (0 : Fin 2) ^ a * MvPowerSeries.X 1 ^ b =
      MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b) (1 : R) := by
    simp only [MvPowerSeries.X, monomial_pow, one_pow, Finsupp.smul_single, smul_eq_mul, mul_one,
      monomial_mul_monomial]
  have h_coeff (k : ℕ) :
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n)
        ((MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ k) =
        if k = m + n then ((m + n).choose m : R) else 0 := by
    rw [add_pow, map_sum]
    split_ifs with hk
    · subst hk
      rw [Finset.sum_eq_single m]
      · simp only [Nat.add_sub_cancel_left, h_mon, ← map_natCast MvPowerSeries.C, coeff_mul_C,
          coeff_monomial, ↓reduceIte, one_mul]
      · intro j _ hjm
        have h_ne : Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n ≠
            Finsupp.single (0 : Fin 2) j + Finsupp.single 1 (m + n - j) := fun h ↦
          hjm (by simpa using DFunLike.congr_fun h.symm 0)
        simp only [h_mon, ← map_natCast MvPowerSeries.C, coeff_mul_C, coeff_monomial, h_ne,
          ↓reduceIte, zero_mul]
      · intro hm
        exact absurd (Finset.mem_range.mpr (by omega)) hm
    · refine Finset.sum_eq_zero fun j hj ↦ ?_
      have h_ne : Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n ≠
          Finsupp.single (0 : Fin 2) j + Finsupp.single 1 (k - j) := fun h ↦ by
        have h0 : j = m := by simpa using DFunLike.congr_fun h.symm 0
        have h1 : k - j = n := by simpa using DFunLike.congr_fun h.symm 1
        have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact hk (by omega)
      simp only [h_mon, ← map_natCast MvPowerSeries.C, coeff_mul_C, coeff_monomial, h_ne,
        ↓reduceIte, zero_mul]
  rw [PowerSeries.coeff_subst h_subst, finsum_eq_single _ (m + n)]
  · simp [h_coeff, mul_comm]
  · intro k hk
    simp [h_coeff, hk]

/-- Differentiating `g(X 0 + X 1)` `m` times in `X 0` and `n` times in `X 1` at `0` gives
`g⁽ᵐ⁺ⁿ⁾(0)`: `m ! * n ! * coeff (m, n) (g(X 0 + X 1)) = (m + n)! * coeff (m + n) g`. -/
theorem factorial_mul_coeff_subst_X_add_X (g : PowerSeries R) (m n : ℕ) :
    (m.factorial : R) * (n.factorial : R) *
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n)
        (g.subst (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1)) =
      ((m + n).factorial : R) * PowerSeries.coeff (m + n) g := by
  rw [coeff_subst_X_add_X, ← mul_assoc]
  have h_nat : m.factorial * n.factorial * (m + n).choose m = (m + n).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
    rw [Nat.add_sub_cancel_left] at h
    linarith
  exact_mod_cast congrArg (fun k : ℕ ↦ (k : R) * PowerSeries.coeff (m + n) g) h_nat

/-- The coefficient of `X 0 ^ m * X 1 ^ n` in `g.subst (X 0) * h.subst (X 1)` is
`PowerSeries.coeff m g * PowerSeries.coeff n h`. -/
theorem coeff_subst_X_mul_subst_X (g h : PowerSeries R) (m n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n)
      (g.subst (MvPowerSeries.X (0 : Fin 2)) * h.subst (MvPowerSeries.X (1 : Fin 2))) =
      PowerSeries.coeff m g * PowerSeries.coeff n h := by
  have h0 : PowerSeries.HasSubst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h1 : PowerSeries.HasSubst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h_pow (i : Fin 2) (k : ℕ) : (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ k =
      MvPowerSeries.monomial (Finsupp.single i k) (1 : R) := by
    simp only [MvPowerSeries.X, monomial_pow, one_pow, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [MvPowerSeries.coeff_mul,
    Finset.sum_eq_single_of_mem (Finsupp.single (0 : Fin 2) m, Finsupp.single 1 n) (by simp)]
  · rw [PowerSeries.coeff_subst h0, PowerSeries.coeff_subst h1,
      finsum_eq_single _ m (fun k hk ↦ by
        simp only [h_pow, coeff_monomial,
          show Finsupp.single (0 : Fin 2) m ≠ Finsupp.single 0 k from
            fun h ↦ hk (by simpa using DFunLike.congr_fun h.symm 0),
          ↓reduceIte, smul_zero]),
      finsum_eq_single _ n (fun k hk ↦ by
        simp only [h_pow, coeff_monomial,
          show Finsupp.single (1 : Fin 2) n ≠ Finsupp.single 1 k from
            fun h ↦ hk (by simpa using DFunLike.congr_fun h.symm 1),
          ↓reduceIte, smul_zero])]
    simp [h_pow]
  · rintro ⟨a, b⟩ h_mem h_ne
    have h_add : a 0 + b 0 = m ∧ a 1 + b 1 = n := by simpa [Finsupp.ext_iff] using h_mem
    have h_not : ¬(a 0 = m ∧ a 1 = 0 ∧ b 0 = 0 ∧ b 1 = n) := by
      simpa [Finsupp.ext_iff, Fin.forall_fin_two] using h_ne
    obtain ha | hb : a 1 ≠ 0 ∨ b 0 ≠ 0 := by omega
    · rw [PowerSeries.coeff_subst h0, finsum_eq_zero_of_forall_eq_zero, zero_mul]
      intro k
      have h_ne' : a ≠ Finsupp.single (0 : Fin 2) k := fun hk ↦
        ha (by simpa using DFunLike.congr_fun hk 1)
      simp only [h_pow, coeff_monomial, h_ne', ↓reduceIte, smul_zero]
    · rw [PowerSeries.coeff_subst h1, finsum_eq_zero_of_forall_eq_zero, mul_zero]
      intro k
      have h_ne' : b ≠ Finsupp.single (1 : Fin 2) k := fun hk ↦
        hb (by simpa using DFunLike.congr_fun hk 0)
      simp only [h_pow, coeff_monomial, h_ne', ↓reduceIte, smul_zero]

end TauCeti
