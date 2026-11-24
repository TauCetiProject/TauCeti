/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NormCoeff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# First Riesz sums and their Mellin transforms

For a sequence of complex coefficients `a : ℕ → ℂ` and a real cutoff `y`, the first Riesz sum is

`TauCeti.rieszSum a y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * (y / n - 1)`.

As a function of `y`, `TauCeti.rieszSum a` vanishes on `(-∞, 1]`, is continuous on `ℝ`, and is
affine on every unit interval `[m, m + 1]`. Dividing `TauCeti.rieszSum (fun n ↦ n * a n) y` by `y`
recovers the classical first Riesz mean `∑_{1 ≤ n ≤ y} a(n) (1 - n / y)`. For an ideal arithmetic
function `b`, the ideal Riesz sum `∑_{N(I) ≤ y} b(I) (y / N(I) - 1)` coincides with
`TauCeti.rieszSum (TauCeti.normCoeff K b) y`.

When `LSeriesSummable a σ` for `σ ≥ 1`, `‖rieszSum a y‖ ≤ y ^ σ * ∑' n, ‖LSeries.term a σ n‖`.
When `LSeriesSummable a s` at `s : ℂ` with `1 < s.re`, the Mellin transform
`y ↦ rieszSum a y * y ^ (-s - 1)` is integrable on `(1, ∞)` with integral
`LSeries a s / (s * (s - 1))`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Chapter 5.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §3.12 and §9.
* L. Alpöge's formalization of the generalized Riemann hypothesis for the Riesz-sum definition and
  ramp-term Mellin transform (`Deduction.ramp`, `Formalism.HC.An.sumLamChi`, `Formalism.Sz`, and
  `Deduction.mellin_ramp`).
-/

public section

open Complex MeasureTheory
open scoped nonZeroDivisors NumberField

namespace TauCeti

/-- The **first Riesz sum** of `a : ℕ → ℂ` at cutoff `y : ℝ`:
`∑_{1 ≤ n ≤ y} a(n) (y / n - 1)`, vanishing for `y < 1`. -/
@[expose] noncomputable def rieszSum (a : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * ((y : ℂ) / n - 1)

/-- Defining equation of `TauCeti.rieszSum`. -/
theorem rieszSum_def (a : ℕ → ℂ) (y : ℝ) :
    rieszSum a y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * ((y : ℂ) / n - 1) :=
  rfl

private theorem le_of_mem_Icc_floor {n : ℕ} {y : ℝ} (hn : n ∈ Finset.Icc 1 ⌊y⌋₊) :
    1 ≤ n ∧ (n : ℝ) ≤ y := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hfl : 1 ≤ ⌊y⌋₊ := hn1.trans (Finset.mem_Icc.mp hn).2
  have hy1 : (1 : ℝ) ≤ y := by
    by_contra hy
    rw [Nat.floor_eq_zero.mpr (not_le.mp hy)] at hfl
    omega
  exact ⟨hn1, (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (by linarith))⟩

/-- The Riesz sum vanishes identically on `(-∞, 1]`. -/
theorem rieszSum_eq_zero_of_le_one (a : ℕ → ℂ) {y : ℝ} (hy : y ≤ 1) : rieszSum a y = 0 := by
  rw [rieszSum]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  obtain ⟨hn1, hn_le⟩ := le_of_mem_Icc_floor hn
  have hy1 : y = 1 := le_antisymm hy ((by exact_mod_cast hn1 : (1 : ℝ) ≤ n).trans hn_le)
  have hn_eq : n = 1 := by
    have : (n : ℝ) ≤ 1 := hn_le.trans hy
    exact le_antisymm (by exact_mod_cast this) hn1
  subst hy1 hn_eq
  simp

private theorem rieszSum_eq_sum_of_le (a : ℕ → ℂ) {y : ℝ} {N : ℕ} (hyN : y ≤ N) :
    rieszSum a y = ∑ n ∈ Finset.Icc 1 N, a n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by
  have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.Icc 1 N := by
    refine Finset.Icc_subset_Icc_right ?_
    rcases le_or_gt 0 y with _hy0 | hy0
    · exact Nat.floor_le_of_le hyN
    · rw [Nat.floor_of_nonpos hy0.le]; exact Nat.zero_le N
  rw [rieszSum, ← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    obtain ⟨hn1, hny⟩ := le_of_mem_Icc_floor hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
    have hnn : 0 ≤ y / n - 1 := sub_nonneg.mpr ((one_le_div hnpos).mpr hny)
    rw [max_eq_left hnn]
    push_cast
    rfl
  · intro n hn hnot
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
    have hfl : ⌊y⌋₊ < n := by
      simp only [Finset.mem_Icc, not_and, not_le] at hnot
      exact hnot hn1
    have hyn : y < n := by
      rcases lt_or_ge y 0 with hy0 | hy0
      · exact hy0.trans hnpos
      · exact (Nat.floor_lt hy0).mp hfl
    have hneg : y / n - 1 ≤ 0 := sub_nonpos.mpr ((div_le_one hnpos).mpr hyn.le)
    rw [max_eq_right hneg, Complex.ofReal_zero, mul_zero]

/-- On each closed unit interval `[m, m + 1]` (`m : ℕ`), `TauCeti.rieszSum a` is affine. -/
theorem rieszSum_eq_sum_of_mem_Icc (a : ℕ → ℂ) {m : ℕ} {y : ℝ}
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
    rw [rieszSum, hfl, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hzero : a (m + 1) * ((y : ℂ) / (m + 1 : ℕ) - 1) = 0 := by
      have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      have hcast : (y : ℂ) = ((m + 1 : ℕ) : ℂ) := by rw [htop]; push_cast; ring
      rw [hcast, div_self hm1, sub_self, mul_zero]
    rw [hzero, add_zero]
    exact hsum m
  · have hfl : ⌊y⌋₊ = m := (Nat.floor_eq_iff hy0).mpr ⟨hy.1, hlt⟩
    rw [rieszSum, hfl]
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
theorem sum_one_sub_div_eq_inv_mul_rieszSum (a : ℕ → ℂ) (y : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * (1 - (n : ℂ) / y) =
      (y : ℂ)⁻¹ * rieszSum (fun n ↦ (n : ℂ) * a n) y := by
  rcases le_or_gt y 0 with hy | hy
  · rw [Nat.floor_of_nonpos hy, Finset.Icc_eq_empty_of_lt Nat.zero_lt_one,
      Finset.sum_empty, rieszSum, Nat.floor_of_nonpos hy,
      Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty, mul_zero]
  · rw [rieszSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [(Finset.mem_Icc.mp hn).1])
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    field_simp

/-- **Growth bound for Riesz sums**: if `1 ≤ σ`, `0 ≤ y`, and `LSeriesSummable a (σ : ℂ)`, then
`‖rieszSum a y‖ ≤ y ^ σ * ∑' n, ‖LSeries.term a (σ : ℂ) n‖`. -/
theorem norm_rieszSum_le {a : ℕ → ℂ} {σ y : ℝ} (hσ : 1 ≤ σ) (hy : 0 ≤ y)
    (h : LSeriesSummable a (σ : ℂ)) :
    ‖rieszSum a y‖ ≤ y ^ σ * ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ := by
  calc ‖rieszSum a y‖
      ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖a n * ((y : ℂ) / n - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, y ^ σ * ‖LSeries.term a (σ : ℂ) n‖ := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        obtain ⟨hn1, hny⟩ := le_of_mem_Icc_floor hn
        have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
        have hyn1 : 1 ≤ y / n := (one_le_div hnpos).mpr hny
        have hramp : y / n - 1 ≤ (y / n) ^ σ := by
          have hp : y / n ≤ (y / n) ^ σ := by
            simpa using Real.rpow_le_rpow_of_exponent_le hyn1 hσ
          linarith
        have hnorm : ‖((y : ℂ) / n - 1)‖ = y / n - 1 := by
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_one,
            ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr hyn1)]
        rw [norm_mul, hnorm, LSeries.term_of_ne_zero (by omega), norm_div,
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

/-- **Ideal coefficients**: summing `b I * (y / N(I) - 1)` over nonzero integral ideals of `𝓞 K`
with `N(I) ≤ y` equals `TauCeti.rieszSum (TauCeti.normCoeff K b) y`. -/
theorem sum_idealsLE_absNorm_eq_rieszSum_normCoeff (K : Type*) [Field K] [NumberField K]
    (b : IdealArithmeticFunction K) (y : ℝ) :
    ∑ I ∈ idealsLE K y, b I * ((y : ℂ) / Ideal.absNorm (I : Ideal (𝓞 K)) - 1) =
      rieszSum (normCoeff K b) y := by
  rw [← idealSummatory_apply K, idealSummatory_eq_sum_Icc_normCoeff, rieszSum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simpa using normCoeff_fun_mul_comp_absNorm K b (fun m : ℕ ↦ (y : ℂ) / m - 1) n

private noncomputable def rampTerm (a : ℕ → ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  if 1 ≤ n then (Set.Ici (n : ℝ)).indicator (fun t : ℝ ↦ a n * ((t : ℂ) / n - 1)) y else 0

private theorem tsum_rampTerm_eq_rieszSum (a : ℕ → ℂ) (y : ℝ) :
    ∑' n : ℕ, rampTerm a n y = rieszSum a y := by
  rw [rieszSum, tsum_eq_sum (s := Finset.Icc 1 ⌊y⌋₊)]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    obtain ⟨hn1, hny⟩ := le_of_mem_Icc_floor hn
    simp [rampTerm, hn1, Set.indicator_of_mem (Set.mem_Ici.mpr hny)]
  · intro n hn
    simp only [Finset.mem_Icc, not_and, not_le] at hn
    simp only [rampTerm]
    split_ifs with hn1
    · refine Set.indicator_of_notMem (Set.notMem_Ici.mpr ?_) _
      have hfl : ⌊y⌋₊ < n := hn hn1
      rcases lt_or_ge y 0 with hy0 | hy0
      · exact hy0.trans (Nat.cast_pos.mpr hn1)
      · exact (Nat.floor_lt hy0).mp hfl
    · rfl

private theorem norm_rampTerm_le (a : ℕ → ℂ) (n : ℕ) (y : ℝ) :
    ‖rampTerm a n y‖ ≤ if 1 ≤ n ∧ (n : ℝ) ≤ y then (‖a n‖ / n) * y else 0 := by
  simp only [rampTerm]
  by_cases hn1 : 1 ≤ n
  · by_cases hny : (n : ℝ) ≤ y
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      have hyn1 : 1 ≤ y / n := (one_le_div hnpos).mpr hny
      have hnorm : ‖((y : ℂ) / n - 1)‖ = y / n - 1 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_one,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hyn1)]
      simp only [hn1, hny, and_self, ↓reduceIte, Set.indicator_of_mem (Set.mem_Ici.mpr hny),
        norm_mul, hnorm]
      calc ‖a n‖ * (y / n - 1) ≤ ‖a n‖ * (y / n) :=
            mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ = (‖a n‖ / n) * y := by ring
    · simp only [hn1, hny, and_false, ↓reduceIte,
        Set.indicator_of_notMem (Set.notMem_Ici.mpr (lt_of_not_ge hny)), norm_zero, le_rfl]
  · simp [hn1]

/-- Mellin transform of a single ramp term `y ↦ (y / n - 1) * y ^ (-s - 1)` on `(n, ∞)`:
equals `n ^ (-s) / (s * (s - 1))` when `1 ≤ n` and `1 < s.re`. -/
theorem integrableOn_ramp_mul_cpow {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ ((y : ℂ) / n - 1) * (y : ℂ) ^ (-s - 1)) (Set.Ioi (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h1 : IntegrableOn (fun y : ℝ ↦ (n : ℂ)⁻¹ * (y : ℂ) ^ (-s)) (Set.Ioi (n : ℝ)) :=
    (integrableOn_Ioi_cpow_of_lt (by simpa using hs) hnpos).const_mul _
  have h2 : IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1))) (Set.Ioi (n : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) hnpos
  refine (h1.sub h2).congr_fun (fun y hy ↦ ?_) measurableSet_Ioi
  have hypos : (0 : ℝ) < y := hnpos.trans hy
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hypos.ne'
  calc (n : ℂ)⁻¹ * (y : ℂ) ^ (-s) - (y : ℂ) ^ (-(s + 1))
      = (n : ℂ)⁻¹ * ((y : ℂ) ^ (1 : ℂ) * (y : ℂ) ^ (-s - 1)) - (y : ℂ) ^ (-s - 1) := by
        rw [← Complex.cpow_add _ _ hyc, show (1 : ℂ) + (-s - 1) = -s by ring,
          show -(s + 1) = -s - 1 by ring]
    _ = ((y : ℂ) / n - 1) * (y : ℂ) ^ (-s - 1) := by
        rw [Complex.cpow_one]; ring

/-- Value of the Mellin transform of a single ramp term on `(n, ∞)`. -/
theorem integral_ramp_mul_cpow {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    ∫ y in Set.Ioi (n : ℝ), ((y : ℂ) / n - 1) * (y : ℂ) ^ (-s - 1) =
      (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs; linarith
  have hs1 : s - 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h
    simp at this; linarith
  have h1 : IntegrableOn (fun y : ℝ ↦ (n : ℂ)⁻¹ * (y : ℂ) ^ (-s)) (Set.Ioi (n : ℝ)) :=
    (integrableOn_Ioi_cpow_of_lt (by simpa using hs) hnpos).const_mul _
  have h2 : IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1))) (Set.Ioi (n : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) hnpos
  have hcongr : ∫ y in Set.Ioi (n : ℝ), ((y : ℂ) / n - 1) * (y : ℂ) ^ (-s - 1) =
      ∫ y in Set.Ioi (n : ℝ), ((n : ℂ)⁻¹ * (y : ℂ) ^ (-s) - (y : ℂ) ^ (-(s + 1))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hnpos.trans hy).ne'
    calc ((y : ℂ) / n - 1) * (y : ℂ) ^ (-s - 1)
        = (n : ℂ)⁻¹ * ((y : ℂ) ^ (1 : ℂ) * (y : ℂ) ^ (-s - 1)) - (y : ℂ) ^ (-(s + 1)) := by
          rw [Complex.cpow_one, show -(s + 1) = -s - 1 by ring]; ring
      _ = (n : ℂ)⁻¹ * (y : ℂ) ^ (-s) - (y : ℂ) ^ (-(s + 1)) := by
          rw [← Complex.cpow_add _ _ hyc, show (1 : ℂ) + (-s - 1) = -s by ring]
  rw [hcongr, integral_sub h1 h2, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simpa using hs) hnpos,
    integral_Ioi_cpow_of_lt (by simp; linarith) hnpos, Complex.ofReal_natCast]
  have hcp1 : (n : ℂ)⁻¹ * (n : ℂ) ^ (-s + 1) = (n : ℂ) ^ (-s) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hnc]
    congr 1; ring
  have hcp2 : (n : ℂ) ^ (-(s + 1) + 1) = (n : ℂ) ^ (-s) := by
    congr 1; ring
  rw [hcp2, mul_div_assoc', mul_neg, hcp1, show -s + 1 = -(s - 1) by ring,
    show -(s + 1) + 1 = -s by ring, neg_div_neg_eq, neg_div_neg_eq]
  field_simp
  ring

private theorem rampTerm_mul_cpow_ae_eq (a : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    (fun y : ℝ ↦ rampTerm a n y * (y : ℂ) ^ (-s - 1)) =ᵐ[volume.restrict (Set.Ioi 1)]
      (Set.Ioi (n : ℝ)).indicator (fun y : ℝ ↦
        if 1 ≤ n then a n * (((y : ℂ) / n - 1) * (y : ℂ) ^ (-s - 1)) else 0) := by
  have hne : ∀ᵐ y : ℝ ∂volume.restrict (Set.Ioi 1), y ≠ (n : ℝ) :=
    ae_restrict_of_ae (ae_iff.mpr (by simp))
  filter_upwards [hne] with y hyn
  by_cases hn1 : 1 ≤ n
  · rcases lt_or_gt_of_ne hyn with hy_lt | hy_gt
    · simp [rampTerm, hn1, Set.indicator_of_notMem (Set.notMem_Ici.mpr hy_lt),
        Set.indicator_of_notMem (Set.notMem_Ioi.mpr hy_lt.le)]
    · simp only [rampTerm, hn1, ↓reduceIte, Set.indicator_of_mem (Set.mem_Ici.mpr hy_gt.le),
        Set.indicator_of_mem (Set.mem_Ioi.mpr hy_gt), mul_assoc]
  · simp [rampTerm, hn1]

private theorem integral_norm_rpow_eq (a : ℕ → ℂ) (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ∫ y in Set.Ioi (n : ℝ), (‖a n‖ / n) * y ^ (-s.re) = ‖LSeries.term a s n‖ / (s.re - 1) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  have hlt : -s.re < -1 := by linarith
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt hnpos,
    LSeries.term_of_ne_zero hn0, norm_div, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  have h1 : (n : ℝ) ^ (-s.re + 1) = n * (n : ℝ) ^ (-s.re) := by
    rw [add_comm, Real.rpow_add hnpos, Real.rpow_one]
  have hsne : s.re - 1 ≠ 0 := by linarith
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  rw [h1, Real.rpow_neg hnpos.le, show -s.re + 1 = -(s.re - 1) by ring]
  field_simp

private theorem norm_rampTerm_mul_cpow_ae_le (a : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    (fun y : ℝ ↦ ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ) ≤ᵐ[volume.restrict (Set.Ioi 1)]
      (Set.Ioi (n : ℝ)).indicator (fun y : ℝ ↦ ENNReal.ofReal ((‖a n‖ / n) * y ^ (-s.re))) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact .of_forall fun y ↦ by simp [rampTerm]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  have hne : ∀ᵐ y : ℝ ∂volume.restrict (Set.Ioi 1), y ≠ (n : ℝ) :=
    ae_restrict_of_ae (ae_iff.mpr (by simp))
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with y _hy1 hyn
  by_cases hy_gt : (n : ℝ) < y
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hy_gt), eNorm_mul]
    have hypos : (0 : ℝ) < y := hnpos.trans hy_gt
    have hcpow : ‖(y : ℂ) ^ (-s - 1)‖ₑ = ENNReal.ofReal (y ^ (-s.re - 1)) := by
      rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hypos]
      simp
    have hramp : ‖rampTerm a n y‖ₑ ≤ ENNReal.ofReal ((‖a n‖ / n) * y) := by
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((norm_rampTerm_le a n y).trans ?_)
      simp [hn1, hy_gt.le]
    calc ‖rampTerm a n y‖ₑ * ‖(y : ℂ) ^ (-s - 1)‖ₑ
        ≤ ENNReal.ofReal ((‖a n‖ / n) * y) * ENNReal.ofReal (y ^ (-s.re - 1)) :=
          mul_le_mul' hramp hcpow.le
      _ = ENNReal.ofReal ((‖a n‖ / n) * y * y ^ (-s.re - 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((‖a n‖ / n) * y ^ (-s.re)) := by
          congr 1
          rw [mul_assoc, show y * y ^ (-s.re - 1) = y ^ (1 : ℝ) * y ^ (-s.re - 1) by
            rw [Real.rpow_one], ← Real.rpow_add hypos]
          congr 2
          ring
  · have hle : y < n := lt_of_le_of_ne (not_lt.mp hy_gt) hyn
    simp [rampTerm, hn1, Set.indicator_of_notMem (Set.notMem_Ici.mpr hle)]

private theorem lintegral_norm_rampTerm_mul_cpow_le (a : ℕ → ℂ) (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ∫⁻ y in Set.Ioi (1 : ℝ), ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ ≤
      ENNReal.ofReal (‖LSeries.term a s n‖ / (s.re - 1)) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [rampTerm]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  have hint : IntegrableOn (fun y : ℝ ↦ (‖a n‖ / n) * y ^ (-s.re)) (Set.Ioi (n : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hnpos).const_mul _
  have hsub : Set.Ioi (n : ℝ) ⊆ Set.Ioi (1 : ℝ) :=
    Set.Ioi_subset_Ioi (by exact_mod_cast hn1)
  have hnonneg :
      ∀ᵐ y : ℝ ∂volume.restrict (Set.Ioi (n : ℝ)), 0 ≤ (‖a n‖ / n) * y ^ (-s.re) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦
      mul_nonneg (by positivity) (Real.rpow_nonneg (hnpos.trans hy).le _)
  calc ∫⁻ y in Set.Ioi (1 : ℝ), ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ
      ≤ ∫⁻ y in Set.Ioi (1 : ℝ), (Set.Ioi (n : ℝ)).indicator
          (fun y : ℝ ↦ ENNReal.ofReal ((‖a n‖ / n) * y ^ (-s.re))) y :=
        lintegral_mono_ae (norm_rampTerm_mul_cpow_ae_le a n s)
    _ = ∫⁻ y in Set.Ioi (n : ℝ), ENNReal.ofReal ((‖a n‖ / n) * y ^ (-s.re)) := by
        rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          Set.inter_eq_left.mpr hsub]
    _ = ENNReal.ofReal (∫ y in Set.Ioi (n : ℝ), (‖a n‖ / n) * y ^ (-s.re)) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = ENNReal.ofReal (‖LSeries.term a s n‖ / (s.re - 1)) := by
        rw [integral_norm_rpow_eq a n hs]

private theorem integrableOn_rampTerm_mul_cpow (a : ℕ → ℂ) (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ rampTerm a n y * (y : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
  refine ⟨?_, ?_⟩
  · have hcpow : Measurable (fun y : ℝ ↦ (y : ℂ) ^ (-s - 1)) :=
      Complex.continuous_ofReal.measurable.pow_const _
    have hramp : Measurable (rampTerm a n) := by
      unfold rampTerm
      by_cases hn1 : 1 ≤ n
      · simp only [hn1, ↓reduceIte]
        exact (by fun_prop : Measurable fun t : ℝ ↦ a n * ((t : ℂ) / n - 1)).indicator
          measurableSet_Ici
      · simp only [hn1, ↓reduceIte]
        exact measurable_const
    exact (hramp.mul hcpow).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_eNorm]
    exact (lintegral_norm_rampTerm_mul_cpow_le a n hs).trans_lt ENNReal.ofReal_lt_top

private theorem tsum_lintegral_norm_rampTerm_ne_top {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (h : LSeriesSummable a s) :
    ∑' n : ℕ, ∫⁻ y in Set.Ioi (1 : ℝ), ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (tsum_le_tsum fun n ↦
    lintegral_norm_rampTerm_mul_cpow_le a n hs) ?_)
  have hsum : Summable fun n : ℕ ↦ ‖LSeries.term a s n‖ / (s.re - 1) := h.norm.div_const _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ div_nonneg (norm_nonneg _) (by linarith)) hsum]
  exact ENNReal.ofReal_lt_top

/-- **Mellin integrability of Riesz sums**: if `1 < s.re` and `LSeriesSummable a s`,
then `y ↦ rieszSum a y * y ^ (-s - 1)` is integrable on `(1, ∞)`. -/
theorem integrableOn_rieszSum_mul_cpow {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (h : LSeriesSummable a s) :
    IntegrableOn (fun y : ℝ ↦ rieszSum a y * (y : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
  have hae : AEStronglyMeasurable (fun y : ℝ ↦ rieszSum a y * (y : ℂ) ^ (-s - 1))
      (volume.restrict (Set.Ioi 1)) := by
    have hcont : ContinuousOn (fun y : ℝ ↦ rieszSum a y * (y : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
      refine (continuous_rieszSum a).continuousOn.mul ?_
      refine ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn) fun y hy ↦ Or.inl ?_
      have : (0 : ℝ) < y := zero_lt_one.trans hy
      simpa using this
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  refine ⟨hae, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  have hle : ∀ y : ℝ, ‖rieszSum a y * (y : ℂ) ^ (-s - 1)‖ₑ ≤
      ∑' n : ℕ, ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ := by
    intro y
    have hsum : rieszSum a y * (y : ℂ) ^ (-s - 1) =
        ∑' n : ℕ, rampTerm a n y * (y : ℂ) ^ (-s - 1) := by
      rw [← tsum_rampTerm_eq_rieszSum, tsum_mul_right]
    rw [hsum]
    exact eNorm_tsum_le_tsum_eNorm
  calc ∫⁻ y in Set.Ioi (1 : ℝ), ‖rieszSum a y * (y : ℂ) ^ (-s - 1)‖ₑ
      ≤ ∫⁻ y in Set.Ioi (1 : ℝ), ∑' n : ℕ, ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ :=
        lintegral_mono hle
    _ = ∑' n : ℕ, ∫⁻ y in Set.Ioi (1 : ℝ), ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ :=
        lintegral_tsum fun n ↦ (integrableOn_rampTerm_mul_cpow a n hs).1.eNorm
    _ < ⊤ := (tsum_lintegral_norm_rampTerm_ne_top hs h).lt_top

/-- **Mellin transform of Riesz sums**: if `1 < s.re` and `LSeriesSummable a s`,
then `∫ y in Set.Ioi 1, rieszSum a y * y ^ (-s - 1) = LSeries a s / (s * (s - 1))`. -/
theorem integral_rieszSum_mul_cpow {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (h : LSeriesSummable a s) :
    ∫ y in Set.Ioi (1 : ℝ), rieszSum a y * (y : ℂ) ^ (-s - 1) =
      LSeries a s / (s * (s - 1)) := by
  have heq : (fun y : ℝ ↦ rieszSum a y * (y : ℂ) ^ (-s - 1)) =
      fun y : ℝ ↦ ∑' n : ℕ, rampTerm a n y * (y : ℂ) ^ (-s - 1) := by
    ext y
    rw [← tsum_rampTerm_eq_rieszSum, tsum_mul_right]
  rw [heq, MeasureTheory.integral_tsum (fun n ↦ (integrableOn_rampTerm_mul_cpow a n hs).1)
    (tsum_lintegral_norm_rampTerm_ne_top hs h)]
  have hterm : ∀ n : ℕ, ∫ y in Set.Ioi (1 : ℝ), rampTerm a n y * (y : ℂ) ^ (-s - 1) =
      LSeries.term a s n / (s * (s - 1)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [rampTerm]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hsub : Set.Ioi (n : ℝ) ⊆ Set.Ioi (1 : ℝ) :=
        Set.Ioi_subset_Ioi (by exact_mod_cast hn1)
      rw [integral_congr_ae (rampTerm_mul_cpow_ae_eq a n s), integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi, Set.inter_eq_left.mpr hsub]
      simp only [hn1, ↓reduceIte, integral_const_mul, integral_ramp_mul_cpow hn1 hs,
        LSeries.term_of_ne_zero hn0, Complex.cpow_neg]
      ring
  simp_rw [hterm]
  rw [tsum_div_const, LSeries]

end TauCeti
