/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Series
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Nonvanishing
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Nonvanishing of cyclotomic character series on the line `Re s = 1`

For a cyclotomic extension `F = K(μ_m)` of a number field `K` and a nontrivial character `χ` of
`Gal(F/K)`, the continued `L`-series `cyclotomicCharacterSeriesC K F χ` does not vanish anywhere
on the line `Re s = 1`. The series of the trivial character, which has a pole at `s = 1`, is
treated for every finite Galois extension in
`TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Nonvanishing`.

## Main results

* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_ne_zero_of_re_eq_one`: for `F = K(μ_m)`
  and `χ ≠ 1`, the continued series of `χ` is nonzero on `Re s = 1`.
* `NumberField.Chebotarev.continuousOn_logDeriv_cyclotomicCharacterSeriesC`: for nontrivial
  characters, the logarithmic derivative is continuous on `Re s ≥ 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The case analysis on `χ²` follows Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`
  (Michael Stoll and David Loeffler), where `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`
  proves the analogous statement for Dirichlet `L`-functions.
-/

public section

open Complex Filter IsDedekindDomain NumberField TauCeti
open scoped Topology

namespace NumberField.Chebotarev

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

/-- **Nonvanishing on `Re s = 1`.** For `F = K(μ_m)` and a nontrivial character `χ` of
`Gal(F/K)`, the continued `L`-series of `χ` does not vanish at any `s` with `Re s = 1`. -/
theorem cyclotomicCharacterSeriesC_ne_zero_of_re_eq_one (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s.re = 1) : cyclotomicCharacterSeriesC K F χ s ≠ 0 := by
  -- At `s = 1` this is the nonvanishing at the edge of the half-plane of convergence.
  obtain rfl | hs1 := eq_or_ne s 1
  · exact cyclotomicCharacterSeriesC_ne_zero_at_one K F m χ hχ
  -- The line `Re s = 1` lies in the half-plane `Re s > 1 - 1 / [K : ℚ]` of the continuations.
  have hdiff (ψ : (F ≃ₐ[K] F) →* ℂˣ) (hψ : ψ ≠ 1) {z : ℂ} (hz : z.re = 1) :
      DifferentiableAt ℂ (cyclotomicCharacterSeriesC K F ψ) z :=
    (differentiableOn_cyclotomicCharacterSeriesC K F m ψ hψ).differentiableAt <|
      (isOpen_lt continuous_const continuous_re).mem_nhds <| by
        rw [Set.mem_ofPred_eq, hz]
        simpa only [Set.mem_ofPred_eq, hz] using
          setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hz.ge
  have hL (ψ : (F ≃ₐ[K] F) →* ℂˣ) : Set.EqOn (cyclotomicCharacterSeriesC K F ψ)
      (LSeries (normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction)) {z | 1 < z.re} :=
    fun z hz ↦ cyclotomicCharacterSeriesC_eq_LSeries K F ψ hz
  -- Away from `s = 1`, run the `3-4-1` argument; the series of `χ²` is continuous at `2s - 1`
  -- either as the trivial series (for `χ² = 1`) or as a continued nontrivial series.
  by_cases hχ2 : χ ^ 2 = 1
  · exact ne_zero_of_eqOn_LSeries_galoisCharacterWeight_of_sq_eq_one χ hχ2 hs hs1
      (hdiff χ hχ hs) (hL χ)
  · exact ne_zero_of_eqOn_LSeries_galoisCharacterWeight χ hs (hdiff χ hχ hs) (hL χ)
      (hdiff (χ ^ 2) hχ2 (by norm_num [hs])).continuousAt (hL (χ ^ 2))

variable (K F) in
/-- **Continuity of the logarithmic derivative on `Re s ≥ 1`.** For `F = K(μ_m)` and a nontrivial
character `χ` of `Gal(F/K)`, the logarithmic derivative of the continued series of `χ` is
continuous on the closed half-plane `Re s ≥ 1`: the series is holomorphic on a neighbourhood of it
and does not vanish on it. -/
theorem continuousOn_logDeriv_cyclotomicCharacterSeriesC (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) :
    ContinuousOn (logDeriv (cyclotomicCharacterSeriesC K F χ)) {s | 1 ≤ s.re} := by
  have hd := differentiableOn_cyclotomicCharacterSeriesC K F m χ hχ
  refine ((hd.deriv (isOpen_lt continuous_const continuous_re)).continuousOn.mono
    (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K)).div
    (hd.continuousOn.mono (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K))
      fun s (hs : 1 ≤ s.re) ↦ ?_
  rcases hs.lt_or_eq with hs | hs
  · rw [cyclotomicCharacterSeriesC_eq_LSeries K F χ hs]
    exact χ.LSeries_galoisCharacterWeight_ne_zero hs
  · exact cyclotomicCharacterSeriesC_ne_zero_of_re_eq_one m χ hχ hs.symm

end NumberField.Chebotarev
