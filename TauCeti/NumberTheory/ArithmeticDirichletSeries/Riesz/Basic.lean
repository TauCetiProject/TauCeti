/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic

/-!
# First Riesz sums

For a sequence of complex coefficients `a : ℕ → ℂ` and a real cutoff `y`, the first Riesz sum is

`TauCeti.rieszSum a y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * (y / n - 1)`.

As a function of `y`, `TauCeti.rieszSum a` vanishes on `(-∞, 1]`, is continuous on `ℝ`, and is
affine on every unit interval `[m, m + 1]`. Dividing `TauCeti.rieszSum (fun n ↦ n * a n) y` by `y`
recovers the classical first Riesz mean `∑_{1 ≤ n ≤ y} a(n) (1 - n / y)`. See
`TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Ideal` for the ideal-coefficient form,
`TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Mellin` for the forward Mellin transform, and
`TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Inversion` for Perron–Riesz inversion.

When `LSeriesSummable a σ` for `σ ≥ 1` and `0 ≤ y`,
`‖rieszSum a y‖ ≤ y ^ σ * ∑' n, ‖LSeries.term a σ n‖`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Chapter 5.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §3.12 and §9.
* L. Alpöge's formalization of the generalized Riemann hypothesis (`Deduction.ramp`).
-/

public section

open Complex

namespace TauCeti

/-- The **first Riesz sum** of `a : ℕ → ℂ` at cutoff `y : ℝ`:
`∑_{1 ≤ n ≤ y} a(n) (y / n - 1)`, vanishing for `y < 1`. -/
noncomputable def rieszSum (a : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * ((y : ℂ) / n - 1)

/-- Defining equation of `TauCeti.rieszSum`. -/
theorem rieszSum_def (a : ℕ → ℂ) (y : ℝ) :
    rieszSum a y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * ((y : ℂ) / n - 1) :=
  (rfl)

/-- The first Riesz sum of the zero sequence vanishes identically. -/
@[simp]
theorem rieszSum_zero (y : ℝ) : rieszSum 0 y = 0 := by
  simp [rieszSum_def]

/-- Additivity of the first Riesz sum in the coefficient sequence. -/
theorem rieszSum_add (a b : ℕ → ℂ) (y : ℝ) :
    rieszSum (a + b) y = rieszSum a y + rieszSum b y := by
  simp only [rieszSum_def, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Scalar homogeneity of the first Riesz sum in the coefficient sequence. -/
theorem rieszSum_smul (c : ℂ) (a : ℕ → ℂ) (y : ℝ) :
    rieszSum (c • a) y = c * rieszSum a y := by
  simp only [rieszSum_def, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- The first Riesz sum vanishes identically on `(-∞, 1]`. -/
@[simp]
theorem rieszSum_eq_zero_of_le_one (a : ℕ → ℂ) {y : ℝ} (hy : y ≤ 1) : rieszSum a y = 0 := by
  rw [rieszSum_def]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn_le : (n : ℝ) ≤ y := (Nat.le_floor_iff' (by omega)).mp (Finset.mem_Icc.mp hn).2
  have hy1 : y = 1 := le_antisymm hy ((by exact_mod_cast hn1 : (1 : ℝ) ≤ n).trans hn_le)
  have hn_eq : n = 1 := le_antisymm (by exact_mod_cast (hn_le.trans hy)) hn1
  subst hy1 hn_eq
  simp

/-- The first Riesz sum of a sequence supported at `1` equals `c * (y - 1)` for `1 ≤ y` and `0`
otherwise. -/
@[simp]
theorem rieszSum_single_one (c : ℂ) (y : ℝ) :
    rieszSum (Pi.single 1 c) y = if 1 ≤ y then c * ((y : ℂ) - 1) else 0 := by
  split_ifs with hy
  · rw [rieszSum_def, Finset.sum_eq_single 1]
    · simp
    · intro n _ hn1
      simp [Pi.single_eq_of_ne hn1]
    · intro hnot
      exact False.elim
        (hnot (Finset.mem_Icc.mpr ⟨le_rfl, (Nat.le_floor_iff' (by omega)).mpr (by simpa using hy)⟩))
  · exact rieszSum_eq_zero_of_le_one _ (not_le.mp hy).le

/-- The infinite sum of ramp terms `if 1 ≤ n ∧ n ≤ y then a n * (y / n - 1) else 0` over
`n : ℕ` equals `TauCeti.rieszSum a y`. -/
theorem tsum_ite_mul_div_sub_one_eq_rieszSum (a : ℕ → ℂ) (y : ℝ) :
    ∑' n : ℕ, (if 1 ≤ n ∧ (n : ℝ) ≤ y then a n * ((y : ℂ) / n - 1) else 0) = rieszSum a y := by
  rw [rieszSum_def, tsum_eq_sum (s := Finset.Icc 1 ⌊y⌋₊)]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' (by omega)).mp (Finset.mem_Icc.mp hn).2
    simp [hn1, hny]
  · intro n hn
    simp only [Finset.mem_Icc, not_and, not_le] at hn
    split_ifs with h
    · have hyn : y < n := (Nat.floor_lt' (by omega)).mp (hn h.1)
      exact False.elim (hyn.not_ge h.2)
    · rfl

private theorem rieszSum_eq_sum_of_le (a : ℕ → ℂ) {y : ℝ} {N : ℕ} (hyN : y ≤ N) :
    rieszSum a y = ∑ n ∈ Finset.Icc 1 N, a n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by
  have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.Icc 1 N :=
    Finset.Icc_subset_Icc_right (Nat.floor_le_of_le hyN)
  rw [rieszSum_def, ← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' (by omega)).mp (Finset.mem_Icc.mp hn).2
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
    have hnn : 0 ≤ y / n - 1 := sub_nonneg.mpr ((one_le_div hnpos).mpr hny)
    rw [max_eq_left hnn]
    simp [Complex.ofReal_div, Complex.ofReal_sub]
  · intro n hn hnot
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
    have hfl : ⌊y⌋₊ < n := by
      simp only [Finset.mem_Icc, not_and, not_le] at hnot
      exact hnot hn1
    have hyn : y < n := (Nat.floor_lt' (by omega)).mp hfl
    have hneg : y / n - 1 ≤ 0 := sub_nonpos.mpr ((div_le_one hnpos).mpr hyn.le)
    rw [max_eq_right hneg, Complex.ofReal_zero, mul_zero]

/-- On each closed unit interval `[m, m + 1]` (`m : ℕ`), `TauCeti.rieszSum a` is affine. -/
theorem rieszSum_eq_sum_mul_sub_sum_of_mem_Icc (a : ℕ → ℂ) {m : ℕ} {y : ℝ}
    (hy : y ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1)) :
    rieszSum a y = (∑ n ∈ Finset.Icc 1 m, a n / n) * y - ∑ n ∈ Finset.Icc 1 m, a n := by
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hy0 : 0 ≤ y := hm0.trans hy.1
  have hsum : ∀ k, (∑ n ∈ Finset.Icc 1 k, a n * ((y : ℂ) / n - 1)) =
      (∑ n ∈ Finset.Icc 1 k, a n / n) * y - ∑ n ∈ Finset.Icc 1 k, a n := by
    intro k
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    ring
  rcases eq_or_lt_of_le hy.2 with htop | hlt
  · have hfl : ⌊y⌋₊ = m + 1 := by
      rw [htop, ← Nat.cast_one, ← Nat.cast_add, Nat.floor_natCast]
    rw [rieszSum_def, hfl, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hzero : a (m + 1) * ((y : ℂ) / (m + 1 : ℕ) - 1) = 0 := by
      have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      have hcast : (y : ℂ) = ((m + 1 : ℕ) : ℂ) := by rw [htop]; push_cast; ring
      rw [hcast, div_self hm1, sub_self, mul_zero]
    rw [hzero, add_zero]
    exact hsum m
  · have hfl : ⌊y⌋₊ = m := (Nat.floor_eq_iff hy0).mpr ⟨hy.1, hlt⟩
    rw [rieszSum_def, hfl]
    exact hsum m

/-- The first Riesz sum `y ↦ TauCeti.rieszSum a y` is continuous on `ℝ`. -/
theorem continuous_rieszSum (a : ℕ → ℂ) : Continuous (rieszSum a) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  set N : ℕ := ⌊|y₀|⌋₊ + 1
  have hy₀ : y₀ < (N : ℝ) := by
    have h1 : y₀ ≤ |y₀| := le_abs_self y₀
    have h2 : |y₀| < (⌊|y₀|⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one |y₀|
    have hN : (N : ℝ) = (⌊|y₀|⌋₊ : ℝ) + 1 := by simp [N]
    linarith
  have hcont : Continuous fun y : ℝ ↦
      ∑ n ∈ Finset.Icc 1 N, a n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by
    fun_prop
  refine hcont.continuousAt.congr ?_
  filter_upwards [isOpen_Iio.mem_nhds hy₀] with y hy
  exact (rieszSum_eq_sum_of_le a hy.le).symm

/-- **First Riesz mean normalization**: for every `y : ℝ`,
`∑_{1 ≤ n ≤ y} a(n) (1 - n / y) = y⁻¹ * rieszSum (fun n ↦ n * a n) y`. -/
theorem sum_mul_one_sub_div_eq_inv_mul_rieszSum (a : ℕ → ℂ) (y : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * (1 - (n : ℂ) / y) =
      (y : ℂ)⁻¹ * rieszSum (fun n ↦ (n : ℂ) * a n) y := by
  rcases le_or_gt y 0 with hy | hy
  · simp [rieszSum_def, Nat.floor_of_nonpos hy]
  · rw [rieszSum_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [(Finset.mem_Icc.mp hn).1])
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    field_simp

/-- The norm of `(y : ℂ) / n - 1` equals `y / n - 1` whenever `1 ≤ y / n`. -/
theorem norm_ofReal_div_sub_one {y : ℝ} {n : ℕ} (h : 1 ≤ y / n) :
    ‖((y : ℂ) / n - 1)‖ = y / n - 1 := by
  have hcast : ((y : ℂ) / n - 1) = (((y / n - 1 : ℝ) : ℂ)) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h)]

/-- **Growth bound for Riesz sums**: if `1 ≤ σ`, `0 ≤ y`, and `LSeriesSummable a (σ : ℂ)`, then
`‖rieszSum a y‖ ≤ y ^ σ * ∑' n, ‖LSeries.term a (σ : ℂ) n‖`. -/
theorem norm_rieszSum_le {a : ℕ → ℂ} {σ y : ℝ} (hσ : 1 ≤ σ) (hy : 0 ≤ y)
    (h : LSeriesSummable a (σ : ℂ)) :
    ‖rieszSum a y‖ ≤ y ^ σ * ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ := by
  calc ‖rieszSum a y‖
      ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖a n * ((y : ℂ) / n - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, y ^ σ * ‖LSeries.term a (σ : ℂ) n‖ := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' (by omega)).mp (Finset.mem_Icc.mp hn).2
        have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
        have hyn1 : 1 ≤ y / n := (one_le_div hnpos).mpr hny
        have hramp : y / n - 1 ≤ (y / n) ^ σ := by
          have hp : y / n ≤ (y / n) ^ σ := by
            simpa using Real.rpow_le_rpow_of_exponent_le hyn1 hσ
          linarith
        rw [norm_mul, norm_ofReal_div_sub_one hyn1, LSeries.term_of_ne_zero (by omega), norm_div,
          ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.ofReal_re]
        calc ‖a n‖ * (y / n - 1) ≤ ‖a n‖ * (y / n) ^ σ :=
              mul_le_mul_of_nonneg_left hramp (norm_nonneg _)
          _ = y ^ σ * (‖a n‖ / (n : ℝ) ^ σ) := by
              rw [Real.div_rpow hy hnpos.le]; ring
    _ = y ^ σ * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖LSeries.term a (σ : ℂ) n‖ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ y ^ σ * ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hy σ)
        exact h.norm.sum_le_tsum _ fun _ _ ↦ norm_nonneg _

end TauCeti
