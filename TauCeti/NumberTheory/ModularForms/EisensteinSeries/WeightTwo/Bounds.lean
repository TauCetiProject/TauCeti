/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Subspace
public import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Coefficient bounds for weight-two Eisenstein series

The corrected series `E₂(z) - t E₂(tz)` has Fourier coefficients
`-24 (σ₁(n) - t σ₁(n/t))`, with the second summand present only when `t ∣ n`, and the normalized
raised series `E₂^{ψ,φ,t}` with characters has positive coefficients `σ₁^{ψ,φ}(n/t)` at the
multiples of `t`, bounded by `σ₁(n)`. For every `ε > 0` these coefficients are therefore
`O(n^(1+ε))`, and so are those of every form in the span in `M₂(Γ₁(N))` of the weight-two
Eisenstein series of all indices `(ψ, φ, t)` (`TauCeti.EisensteinSeries.CharIndex.weightTwoForm`).
Since these series span a complement of the cusp forms, this is the Eisenstein half of the bound
`aₙ = O(n^(1+ε))` for every form of weight two on `Γ₁(N)`, and hence of the abscissa bound `2`
for its L-series, the weight-two case of Diamond–Shurman, Proposition 5.9.1
(`TauCeti.ModularFormClass.abscissaOfAbsConv_qExpansion_coeff_le_of_Gamma1_le`).

The ε-family avoids asserting the false bound `σ₁(n) = O(n)`.

## Main results

* `TauCeti.EisensteinSeries.isBigO_qExpansion_coeff_correctedE2` and
  `TauCeti.EisensteinSeries.CharIndex.isBigO_qExpansion_weightTwoForm_coeff`: the coefficients
  of a corrected series, and of the weight-two series of an index, are `O(n^(1+ε))`.
* `TauCeti.EisensteinSeries.isBigO_qExpansion_coeff_of_mem_span_weightTwoForm`: the same bound
  for every linear combination of the weight-two series with character.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Chapter 4, §4.6 and
  Proposition 5.9.1.
-/

public noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Filter Asymptotics
open scoped MatrixGroups ArithmeticFunction.sigma

namespace TauCeti.EisensteinSeries

/-- For any exponent `s > 1`, the corrected weight-two Eisenstein coefficient is bounded
by `24 (1+t) n^s ∑' d, d^(-s)` at every positive index. -/
theorem norm_qExpansion_coeff_correctedE2_le (t : ℕ) [NeZero t] {s : ℝ} (hs : 1 < s)
    {n : ℕ} (hn : n ≠ 0) :
    ‖(qExpansion 1 (correctedE2 t)).coeff n‖ ≤
      24 * (1 + (t : ℝ)) * ((n : ℝ) ^ s * ∑' d : ℕ, ((d : ℝ) ^ s)⁻¹) := by
  let C : ℝ := ∑' d : ℕ, ((d : ℝ) ^ s)⁻¹
  have hC : 0 ≤ C := tsum_nonneg fun d ↦ by positivity
  have hsig (m : ℕ) : ‖(σ 1 m : ℂ)‖ ≤ (m : ℝ) ^ s * C := by
    simpa only [Complex.norm_natCast] using
      sigma_le_rpow_mul_tsum 1 (by simpa only [Nat.cast_one] using hs.le) hs m
  have hdiv : ‖(σ 1 (n / t) : ℂ)‖ ≤ (n : ℝ) ^ s * C := by
    refine (hsig _).trans ?_
    gcongr
    exact_mod_cast Nat.div_le_self n t
  rw [qExpansion_coeff_correctedE2, ite_eq_right hn, norm_mul]
  have hcorrection :
      ‖(if t ∣ n then (t : ℂ) * (σ 1 (n / t) : ℂ) else 0)‖ ≤
        (t : ℝ) * ((n : ℝ) ^ s * C) := by
    split_ifs
    · rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg t)
    · simpa only [norm_zero] using mul_nonneg (Nat.cast_nonneg t)
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s) hC)
  calc
    _ ≤ 24 * (‖(σ 1 n : ℂ)‖ +
        ‖(if t ∣ n then (t : ℂ) * (σ 1 (n / t) : ℂ) else 0)‖) := by
      simpa using mul_le_mul_of_nonneg_left
        (norm_sub_le (σ 1 n : ℂ)
          (if t ∣ n then (t : ℂ) * (σ 1 (n / t) : ℂ) else 0))
        (by norm_num : (0 : ℝ) ≤ 24)
    _ ≤ 24 * ((n : ℝ) ^ s * C + (t : ℝ) * ((n : ℝ) ^ s * C)) := by
      gcongr
      exact hsig n
    _ = _ := by dsimp only [C]; ring

/-- The corrected weight-two Eisenstein coefficients are `O(n^(1+ε))` for every `ε > 0`.
The estimate at infinity is unaffected by the constant term. -/
theorem isBigO_qExpansion_coeff_correctedE2 (t : ℕ) [NeZero t] {ε : ℝ} (hε : 0 < ε) :
    (fun n ↦ (qExpansion 1 (correctedE2 t)).coeff n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 + ε)) := by
  refine isBigO_iff.mpr
    ⟨24 * (1 + (t : ℝ)) * ∑' d : ℕ, ((d : ℝ) ^ (1 + ε))⁻¹, ?_⟩
  filter_upwards [eventually_ne_atTop 0] with n hn
  refine (norm_qExpansion_coeff_correctedE2_le t (by linarith : 1 < 1 + ε) hn).trans_eq ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  ring

/-! ### The weight-two series with character -/

namespace CharIndex

variable {N : ℕ} [NeZero N] (a : CharIndex N 2)

/-- For any exponent `s > 1`, the positive Fourier coefficients of the weight-two Eisenstein
series of an index `(ψ, φ, t)` are bounded by `24 (1 + t) n^s ∑' d, d^(-s)`. The constant is that
of the corrected series `E₂(z) - t E₂(t z)`; away from the trivial pair the coefficient is a
twisted divisor sum, bounded by `σ₁(n)`. -/
theorem norm_qExpansion_weightTwoForm_coeff_le {s : ℝ} (hs : 1 < s) {n : ℕ} (hn : n ≠ 0) :
    ‖(qExpansion 1 a.weightTwoForm).coeff n‖ ≤
      24 * (1 + (a.t : ℝ)) * ((n : ℝ) ^ s * ∑' d : ℕ, ((d : ℝ) ^ s)⁻¹) := by
  have : NeZero a.t := NeZero.of_dvd a.t_dvd
  by_cases h : a.psi = 1 ∧ a.phi = 1
  · rw [a.weightTwoForm_of_eq_one h]
    simpa only [ModularForm.coe_restrict] using norm_qExpansion_coeff_correctedE2_le a.t hs hn
  rw [a.qExpansion_weightTwoForm_coeff_of_ne_one (not_and_or.mp h) hn]
  set C : ℝ := ∑' d : ℕ, ((d : ℝ) ^ s)⁻¹
  have hnC : 0 ≤ (n : ℝ) ^ s * C :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s) (tsum_nonneg fun d ↦ by positivity)
  have hle : ‖if a.t ∣ n then DirichletCharacter.twistedDivisorSum 1 a.psi a.phi (n / a.t)
      else 0‖ ≤ (n : ℝ) ^ s * C := by
    split_ifs
    · calc
        _ ≤ ∑ d ∈ (n / a.t).divisors, (d : ℝ) ^ 1 := norm_twistedDivisorSum_le _ _ _ _
        _ ≤ ((n / a.t : ℕ) : ℝ) ^ s * C := by
          simpa only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow] using
            sigma_le_rpow_mul_tsum 1 (by simpa using hs.le) hs (n / a.t)
        _ ≤ (n : ℝ) ^ s * C := by
          gcongr
          exact_mod_cast Nat.div_le_self n a.t
    · simpa only [norm_zero] using hnC
  refine hle.trans (le_mul_of_one_le_left hnC ?_)
  have : (0 : ℝ) ≤ a.t := Nat.cast_nonneg _
  linarith

/-- The coefficients of the weight-two Eisenstein series of an index are `O(n^(1+ε))` for every
`ε > 0`. The estimate at infinity is unaffected by the constant term. -/
theorem isBigO_qExpansion_weightTwoForm_coeff {ε : ℝ} (hε : 0 < ε) :
    (fun n ↦ (qExpansion 1 a.weightTwoForm).coeff n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 + ε)) := by
  refine isBigO_iff.mpr
    ⟨24 * (1 + (a.t : ℝ)) * ∑' d : ℕ, ((d : ℝ) ^ (1 + ε))⁻¹, ?_⟩
  filter_upwards [eventually_ne_atTop 0] with n hn
  refine (a.norm_qExpansion_weightTwoForm_coeff_le (by linarith : 1 < 1 + ε) hn).trans_eq ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  ring

end CharIndex

variable {N : ℕ} [NeZero N]

/-- Every linear combination of the weight-two Eisenstein series of the indices `(ψ, φ, t)` of
level `N` has coefficients `O(n^(1+ε))` for every `ε > 0`. -/
theorem isBigO_qExpansion_coeff_of_mem_span_weightTwoForm {ε : ℝ} (hε : 0 < ε)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2}
    (hf : f ∈ Submodule.span ℂ (Set.range (CharIndex.weightTwoForm (N := N)))) :
    (fun n ↦ (qExpansion 1 f).coeff n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 + ε)) := by
  let Q := ModularForm.qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma1_map N) 2
  suffices (fun n ↦ (Q f).coeff n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 + ε)) by
    simpa only [Q, ModularForm.qExpansionLinearMap_apply] using this
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨a, rfl⟩ := hg
      simpa only [Q, ModularForm.qExpansionLinearMap_apply] using
        a.isBigO_qExpansion_weightTwoForm_coeff hε
  | zero => simpa using (isBigO_zero (fun n : ℕ ↦ (n : ℝ) ^ (1 + ε)) atTop)
  | add g h _ _ hg hh => simpa using hg.add hh
  | smul c g _ hg => simpa using hg.const_mul_left c

end TauCeti.EisensteinSeries
