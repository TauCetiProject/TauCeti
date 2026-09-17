/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.LSeries.Continuation

/-!
# Continuation from cancellation of ideal weights

An inclusive partial-sum bound for a unitary ideal weight supplies the analytic strip
`Re s > 1 - 1 / [K : ℚ]`. The continuation is constructed by Abel summation, rather than
by treating conditional convergence as absolute convergence. Agreement with the ideal
Dirichlet series is asserted only on its absolute-convergence half-plane.

The construction uses Mathlib's Mellin transform and its integral representation of
`LSeries` from partial sums (Xavier Roblot, `Mathlib.NumberTheory.LSeries.SumCoeff`).

## References

* H. Davenport, *Multiplicative Number Theory*, chapters on partial summation.
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory
open scoped NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- A unitary ideal weight has cancellation when its inclusive ideal sums are
`O(X^(1-1/[K:ℚ]))`. The norm is taken after summing, not term by term. -/
def HasCancellation (χ : UnitaryIdealWeight K) : Prop :=
  idealSummatory K χ.toIdealArithmeticFunction =O[atTop]
    fun x : ℝ ↦ x ^ (1 - 1 / (Module.finrank ℚ K : ℝ))

/-- Cancellation gives the polynomial partial-sum bound for the regrouped coefficients. -/
theorem HasCancellation.isBigO_sum_normCoeff {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, normCoeff K χ.toIdealArithmeticFunction k)
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  unfold HasCancellation at hχ
  simpa only [Function.comp_def, idealSummatory_eq_sum_Icc_normCoeff, Nat.floor_natCast] using
    hχ.comp_tendsto tendsto_natCast_atTop_atTop


/-- Conjugation preserves cancellation; it does not change the norm of any partial sum. -/
theorem HasCancellation.conj {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ) :
    HasCancellation χ.conj := by
  unfold HasCancellation at hχ ⊢
  refine hχ.norm_left.congr_left ?_ |>.of_norm_left
  intro x
  rw [idealSummatory_apply, idealSummatory_apply]
  simp only [UnitaryIdealWeight.toIdealArithmeticFunction_apply, UnitaryIdealWeight.val_conj,
    MultiplicativeIdealWeight.conj_apply]
  conv_rhs => rw [← map_sum ((starRingEnd ℂ) : ℂ →+* ℂ), starRingEnd_apply]
  rw [norm_star]

@[simp]
theorem hasCancellation_conj_iff (χ : UnitaryIdealWeight K) :
    HasCancellation χ.conj ↔ HasCancellation χ := by
  constructor
  · intro h
    have hconj : χ.conj.conj = χ := by
      apply Subtype.ext
      simp
    simpa only [hconj] using h.conj
  · exact HasCancellation.conj

/-- The Abel–Mellin continuation of a unitary ideal weight. Its analytic meaning requires
`HasCancellation`; outside the convergence region the integral is totalized. -/
noncomputable def continuedLFunctionOfWeight (χ : UnitaryIdealWeight K) : ℂ → ℂ :=
  LSeries.continuedLSeries (normCoeff K χ.toIdealArithmeticFunction)

/-- The defining inclusive Abel integral for the continued ideal-weight series. -/
theorem continuedLFunctionOfWeight_eq_mul_integral (χ : UnitaryIdealWeight K) (s : ℂ) :
    continuedLFunctionOfWeight χ s = s * ∫ t in Set.Ioi (1 : ℝ),
      idealSummatory K χ.toIdealArithmeticFunction t * (t : ℂ) ^ (-(s + 1)) := by
  rw [continuedLFunctionOfWeight, LSeries.continuedLSeries_eq_mul_integral]
  simp_rw [idealSummatory_eq_sum_Icc_normCoeff]

/-- Cancellation continues the ideal-weight series analytically to
`Re s > 1 - 1 / [K : ℚ]`. -/
theorem HasCancellation.analyticOnNhd_continuedLFunctionOfWeight
    {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ) :
    AnalyticOnNhd ℂ (continuedLFunctionOfWeight χ)
      {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := by
  exact LSeries.analyticOnNhd_continuedLSeries
    hχ.isBigO_sum_normCoeff

/-- On the absolute-convergence half-plane the continuation agrees with the
norm-regrouped Dirichlet series. -/
theorem continuedLFunctionOfWeight_eq_LSeries
    (χ : UnitaryIdealWeight K) {s : ℂ} (hs : 1 < s.re) :
    continuedLFunctionOfWeight χ s =
      _root_.LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  have hpoint (n : ℕ) :
      ‖∑ k ∈ Finset.Icc 1 n, normCoeff K χ.toIdealArithmeticFunction k‖ ≤
        ∑ k ∈ Finset.Icc 1 n, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖ := by
    calc
      ‖∑ k ∈ Finset.Icc 1 n, normCoeff K χ.toIdealArithmeticFunction k‖
          ≤ ∑ k ∈ Finset.Icc 1 n, ‖normCoeff K χ.toIdealArithmeticFunction k‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 n, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖ := by
            exact Finset.sum_le_sum fun k hk ↦ by
              calc
                ‖normCoeff K χ.toIdealArithmeticFunction k‖
                    ≤ ∑ I ∈ normFiber K k, ‖χ.toIdealArithmeticFunction I‖ := by
                      rw [normCoeff_eq_sum_normFiber]
                      exact norm_sum_le _ _
                _ ≤ ∑ I ∈ normFiber K k, (1 : ℝ) := by
                      exact Finset.sum_le_sum fun I hI ↦ by
                        simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_apply] using
                          χ.norm_le_one I
                _ = (normFiber K k).card := by simp
                _ = ‖normCoeff K (1 : IdealArithmeticFunction K) k‖ :=
                  (norm_normCoeff_one K k).symm
  have hO :
      (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
        normCoeff K χ.toIdealArithmeticFunction k) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) :=
    (Asymptotics.isBigO_of_le _ fun n ↦ by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun k hk ↦ norm_nonneg _)] using
        hpoint n).trans (isBigO_sum_norm_normCoeff_one K)
  exact LSeries.continuedLSeries_eq_LSeries
    hO (by simpa only [max_eq_left zero_le_one] using hs)
    (LSeriesSummable_normCoeff K (summable_idealTerm_of_unitary_of_one_lt_re χ hs))



/-- **Rejection test.** The trivial weight does not satisfy `HasCancellation`: its inclusive
ideal sums grow at least linearly with a uniform slope, while cancellation would force them
below `C₀ · x^(1-1/[K:ℚ])` for a fixed `C₀`. -/
theorem not_hasCancellation_one : ¬ HasCancellation (1 : UnitaryIdealWeight K) := by
  intro h
  obtain ⟨b⟩ := idealCount_linearBounds K
  unfold HasCancellation at h
  obtain ⟨C₀, hC₀⟩ := Asymptotics.IsBigO.isBigOWith h
  rw [UnitaryIdealWeight.toIdealArithmeticFunction_one] at hC₀
  rw [Asymptotics.isBigOWith_iff] at hC₀
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hC₀
  obtain ⟨Nnat, hNnat⟩ := exists_nat_gt N
  have hfr : (0:ℝ) < Module.finrank ℚ K :=
    by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hy : (0 : ℝ) < 1 / (Module.finrank ℚ K : ℝ) := div_pos zero_lt_one hfr
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      b.lower ≤ C₀ * (n:ℝ) ^ (-(1 / (Module.finrank ℚ K : ℝ))) := by
    filter_upwards [Filter.eventually_ge_atTop (max Nnat 1)] with n hn
    have hn1 : (1:ℕ) ≤ n := le_trans (le_max_right Nnat 1) hn
    have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have hn0 : (0:ℕ) < n := lt_of_lt_of_le zero_lt_one hn1
    have hnN : (N:ℝ) ≤ (n:ℝ) := hNnat.le.trans (by exact_mod_cast le_trans (le_max_left Nnat 1) hn)
    have hlower := b.le_card (n:ℝ) hn1'
    have hpt := hN (n:ℝ) hnN
    have hnorm1 : ‖((n:ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) : ℝ)‖
        = (n:ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) :=
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
    have hnorm2 : ‖idealSummatory K (1 : IdealArithmeticFunction K) (n:ℝ)‖
        = ((Nat.card {I : (Ideal (𝓞 K))⁰ //
            (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n:ℝ)}) : ℝ) :=
      norm_idealSummatory_one_eq_card K n
    rw [hnorm2, hnorm1] at hpt
    have hn0' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
    have hstep : b.lower * (n:ℝ) * (n:ℝ)⁻¹
        ≤ C₀ * (n:ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) * (n:ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_trans hlower hpt) (inv_nonneg.mpr hn0'.le)
    have hexp : (1 - 1 / (Module.finrank ℚ K : ℝ)) - 1 = -(1 / (Module.finrank ℚ K : ℝ)) := by ring
    have hrpow : (n:ℝ) ^ (-(1 / (Module.finrank ℚ K : ℝ)))
        = (n:ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) * (n:ℝ)⁻¹ := by
      conv_lhs => rw [← hexp]
      rw [Real.rpow_sub hn0' (1 - 1 / (Module.finrank ℚ K : ℝ)) 1, Real.rpow_one, div_eq_mul_inv]
    calc b.lower = b.lower * (n:ℝ) * (n:ℝ)⁻¹ := by field_simp
      _ ≤ C₀ * (n:ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) * (n:ℝ)⁻¹ :=
          hstep
      _ = C₀ * ((n:ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) * (n:ℝ)⁻¹) := by ring
      _ = C₀ * (n:ℝ) ^ (-(1 / (Module.finrank ℚ K : ℝ))) := by rw [hrpow]
  have hlim : Tendsto
      (fun n : ℕ ↦ C₀ * (n:ℝ) ^ (-(1 / (Module.finrank ℚ K : ℝ)))) Filter.atTop (nhds 0) := by
    have hcomp : Tendsto (fun n : ℕ ↦ (n:ℝ) ^ (-(1 / (Module.finrank ℚ K : ℝ))))
        Filter.atTop (nhds 0) := (tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop
    simpa using hcomp.const_mul C₀
  exact absurd (le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound)
    (not_le.mpr b.lower_pos)

end TauCeti
