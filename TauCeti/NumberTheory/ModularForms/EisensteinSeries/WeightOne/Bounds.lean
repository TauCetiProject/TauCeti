/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Subspace
public import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
public import Mathlib.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Coefficient bounds for weight-one Eisenstein series

The positive Fourier coefficients of `E₁^{ψ,φ,t}` are the twisted divisor sums
`σ₀^{ψ,φ}(n/t)` when `t ∣ n`, and zero otherwise. Their norms are at most the number of
divisors of `n`, uniformly in the characters and the raising parameter. Consequently, for
every `ε > 0`, these coefficients are `O(n^ε)`. The same estimate holds on the span of all
the weight-one Eisenstein series at a fixed level, and its coefficient L-series converges
absolutely on `Re s > 1`.

These statements concern the Eisenstein span, not arbitrary weight-one modular forms.
No decomposition of a general modular form into Eisenstein and cuspidal parts is assumed.
The constant Fourier coefficient does not affect either the asymptotic bound or the
abscissa of absolute convergence.

## Main results

* `TauCeti.EisensteinSeries.CharIndex.norm_qExpansion_weightOneForm_coeff_le_card_divisors`:
  the uniform divisor-count bound at positive indices.
* `TauCeti.EisensteinSeries.isBigO_qExpansion_coeff_of_mem_span_weightOneForm`:
  coefficients in the Eisenstein span are `O(n^ε)` for every `ε > 0`.
* `TauCeti.EisensteinSeries.abscissaOfAbsConv_qExpansion_coeff_le_of_mem_span_weightOneForm`:
  the coefficient L-series of a form in that span has abscissa at most one.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §4.8 and Proposition 5.9.1.
-/

public noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Filter Asymptotics
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

namespace CharIndex

variable {N : ℕ} [NeZero N] (a : CharIndex N 1)

/-- The norm of a positive Fourier coefficient of a weight-one Eisenstein series is at most
the number of divisors of its index, uniformly in the characters and the raising parameter. -/
theorem norm_qExpansion_weightOneForm_coeff_le_card_divisors {n : ℕ} (hn : n ≠ 0) :
    ‖(qExpansion 1 a.weightOneForm).coeff n‖ ≤ (n.divisors.card : ℝ) := by
  rw [a.qExpansion_weightOneForm_coeff hn]
  split_ifs with ht
  · calc
      _ ≤ ∑ d ∈ (n / a.t).divisors, (d : ℝ) ^ 0 := norm_twistedDivisorSum_le _ _ _ _
      _ = ((n / a.t).divisors.card : ℝ) := by simp
      _ ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn (Nat.div_dvd_of_dvd ht))
  · simp

/-- The Fourier coefficients of a weight-one Eisenstein series are `O(n^ε)` for every
positive `ε`. -/
theorem isBigO_qExpansion_weightOneForm_coeff {ε : ℝ} (hε : 0 < ε) :
    (fun n ↦ (qExpansion 1 a.weightOneForm).coeff n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ ε) := by
  obtain ⟨C, _, hC⟩ := exists_pos_card_divisors_le_rpow hε
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ε)] using
    (a.norm_qExpansion_weightOneForm_coeff_le_card_divisors hn).trans (hC n)

end CharIndex

variable {N : ℕ} [NeZero N]

/-- Every linear combination of weight-one Eisenstein series at level `N` has Fourier
coefficients `O(n^ε)` for every positive `ε`. -/
theorem isBigO_qExpansion_coeff_of_mem_span_weightOneForm {ε : ℝ} (hε : 0 < ε)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 1}
    (hf : f ∈ Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N)))) :
    (fun n ↦ (qExpansion 1 f).coeff n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ ε) := by
  let Q := ModularForm.qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma1_map N) 1
  suffices (fun n ↦ (Q f).coeff n) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ ε) by
    simpa only [Q, ModularForm.qExpansionLinearMap_apply] using this
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨a, rfl⟩ := hg
      simpa only [Q, ModularForm.qExpansionLinearMap_apply] using
        a.isBigO_qExpansion_weightOneForm_coeff hε
  | zero => simpa using (isBigO_zero (fun n : ℕ ↦ (n : ℝ) ^ ε) atTop)
  | add g h _ _ hg hh => simpa using hg.add hh
  | smul c g _ hg => simpa using hg.const_mul_left c

/-- The coefficient L-series of any form in the weight-one Eisenstein span converges
absolutely on `Re s > 1`. -/
theorem abscissaOfAbsConv_qExpansion_coeff_le_of_mem_span_weightOneForm
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 1}
    (hf : f ∈ Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N)))) :
    LSeries.abscissaOfAbsConv (fun n ↦ (qExpansion 1 f).coeff n) ≤ (1 : EReal) := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  refine LSeriesSummable_of_isBigO_rpow (x := 1 + (y - 1) / 2)
    (by simp only [Complex.ofReal_re]; linarith) ?_
  simpa only [add_sub_cancel_left] using
    isBigO_qExpansion_coeff_of_mem_span_weightOneForm (by linarith : 0 < (y - 1) / 2) hf

end TauCeti.EisensteinSeries
