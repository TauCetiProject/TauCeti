/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.Calculus.DSlope.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Iterated divided differences of analytic functions

Generic properties of iterated divided differences `(Function.swap dslope a)^[n] f` for analytic
functions `f : 𝕜 → E`:

* `AnalyticAt.iterate_dslope`: iterated divided differences preserve analyticity.
* `HasFPowerSeriesAt.iterate_dslope_apply_eq_coeff`: at the base point `z₀`, the `n`-th iterated
  divided difference equals the `n`-th Taylor coefficient `p.coeff n`.
* `AnalyticAt.factorial_smul_iterate_dslope_apply`: into a complete space `E`,
  `n! • (swap dslope z₀)^[n] f z₀ = iteratedDeriv n f z₀` without characteristic assumptions.
* Over a characteristic-zero nontrivially normed field `𝕜` into a complete space `F`,
  `AnalyticAt.iterate_dslope_apply_eq_inv_factorial_smul_iteratedDeriv`,
  `AnalyticAt.sub_sum_inv_factorial_smul_iteratedDeriv_eq_pow_smul_iterate_dslope`, and
  `AnalyticAt.iterate_dslope_eq_inv_factorial_smul_add_sub_smul_succ` relate the iterated divided
  differences to `iteratedDeriv` and supply Taylor's formula with analytic remainder quotient.
-/

public section

open Function

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {a : 𝕜}

/-- Iterated divided differences at `a` preserve analyticity at every point where `f` is
analytic. -/
theorem AnalyticAt.iterate_dslope {z : 𝕜} (hf : AnalyticAt 𝕜 f z) (n : ℕ) :
    AnalyticAt 𝕜 ((swap dslope a)^[n] f) z := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [iterate_succ_apply']; exact ih.dslope a

/-- The `n`-th iterated divided difference at `z₀` of a function with power series `p` at `z₀`
takes the value `p.coeff n` at `z₀`: these values are the Taylor coefficients. -/
theorem HasFPowerSeriesAt.iterate_dslope_apply_eq_coeff {p : FormalMultilinearSeries 𝕜 𝕜 E}
    {z₀ : 𝕜} (hp : HasFPowerSeriesAt f p z₀) (n : ℕ) : (swap dslope z₀)^[n] f z₀ = p.coeff n := by
  rw [← (hp.has_fpower_series_iterate_dslope_fslope n).coeff_zero 1,
    ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope, zero_add]

/-- If `f : 𝕜 → E` is analytic at `z₀` into a complete space `E`, then `n!` times the `n`-th
iterated divided difference at `z₀` equals `iteratedDeriv n f z₀`, without any characteristic
assumption on `𝕜`. -/
theorem AnalyticAt.factorial_smul_iterate_dslope_apply [CompleteSpace E] {z₀ : 𝕜}
    (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) :
    n.factorial • (swap dslope z₀)^[n] f z₀ = iteratedDeriv n f z₀ := by
  obtain ⟨p, r, hr⟩ := hf
  have hfact := hr.factorial_smul 1 n
  rw [← iteratedDeriv_eq_iteratedFDeriv] at hfact
  rw [hr.hasFPowerSeriesAt.iterate_dslope_apply_eq_coeff n, FormalMultilinearSeries.coeff]
  exact hfact

section CharZero

variable {F : Type*} [CharZero 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Over a characteristic-zero nontrivially normed field `𝕜`, if `f : 𝕜 → F` is analytic at `z₀`
into a complete space `F`, then the `n`-th iterated divided difference at `z₀` evaluates at `z₀`
to `(n.factorial : 𝕜)⁻¹ • iteratedDeriv n f z₀`. -/
theorem AnalyticAt.iterate_dslope_apply_eq_inv_factorial_smul_iteratedDeriv
    {f : 𝕜 → F} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) :
    (swap dslope z₀)^[n] f z₀ = (n.factorial : 𝕜)⁻¹ • iteratedDeriv n f z₀ := by
  have hne : (n.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [← hf.factorial_smul_iterate_dslope_apply n, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    inv_mul_cancel₀ hne, one_smul]

/-- **Taylor's formula with analytic divided-difference remainder**: over a characteristic-zero
nontrivially normed field `𝕜`, for `f : 𝕜 → F` analytic at `z₀` into a complete space `F`,
`f z - ∑ j ∈ Finset.range n, (z - z₀) ^ j • ((j.factorial : 𝕜)⁻¹ • iteratedDeriv j f z₀) =
  (z - z₀) ^ n • (Function.swap dslope z₀)^[n] f z`. -/
theorem AnalyticAt.sub_sum_inv_factorial_smul_iteratedDeriv_eq_pow_smul_iterate_dslope
    {f : 𝕜 → F} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) (z : 𝕜) :
    f z - ∑ j ∈ Finset.range n, (z - z₀) ^ j • ((j.factorial : 𝕜)⁻¹ • iteratedDeriv j f z₀) =
      (z - z₀) ^ n • (swap dslope z₀)^[n] f z := by
  have h := TauCeti.sum_add_pow_sub_smul_iterate_dslope f z₀ z n
  have hsum : ∑ j ∈ Finset.range n, (z - z₀) ^ j • (swap dslope z₀)^[j] f z₀ =
      ∑ j ∈ Finset.range n, (z - z₀) ^ j • ((j.factorial : 𝕜)⁻¹ • iteratedDeriv j f z₀) :=
    Finset.sum_congr rfl fun j _ ↦ by
      rw [hf.iterate_dslope_apply_eq_inv_factorial_smul_iteratedDeriv j]
  rw [hsum] at h
  exact sub_eq_of_eq_add' h.symm

/-- Successor recurrence for iterated divided-difference remainders of an analytic function
`f : 𝕜 → F` at `z₀` over a characteristic-zero nontrivially normed field `𝕜` into a complete
space `F`. -/
theorem AnalyticAt.iterate_dslope_eq_inv_factorial_smul_add_sub_smul_succ
    {f : 𝕜 → F} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) (z : 𝕜) :
    (swap dslope z₀)^[n] f z =
      (n.factorial : 𝕜)⁻¹ • iteratedDeriv n f z₀ +
        (z - z₀) • (swap dslope z₀)^[n + 1] f z := by
  have h := eq_add_of_sub_eq' (sub_smul_dslope ((swap dslope z₀)^[n] f) z₀ z).symm
  rw [hf.iterate_dslope_apply_eq_inv_factorial_smul_iteratedDeriv n] at h
  simpa only [iterate_succ_apply'] using h

end CharZero
