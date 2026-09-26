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
* `NumberField.Chebotarev.exists_continuousOn_eq_neg_logDeriv_galoisCharacterWeight_one_sub`:
  the regularized logarithmic derivative of the trivial character extends continuously there.

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

variable (K F) in
/-- **The regularized boundary function of the trivial character.** Let `F / K` be a finite
Galois extension and `L_1` the `L`-series of the trivial character of `Gal(F/K)`, that is the
Dedekind zeta function of `K` with the Euler factors at the primes ramified in `F` deleted. Then
`-L_1'(s) / L_1(s) - 1 / (s - 1)` extends from `Re s > 1` to a function continuous on
`Re s ≥ 1`. -/
theorem exists_continuousOn_eq_neg_logDeriv_galoisCharacterWeight_one_sub : ∃ G : ℂ → ℂ,
    ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      G s = -logDeriv (LSeries (normCoeff K
        (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction)) s -
          1 / (s - 1) := by
  obtain ⟨G, hG, hGL⟩ := exists_differentiableOn_eq_cyclotomicCharacterSeriesC_one_sub K F
  set U := {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  set ρ := (dedekindZeta_residue K : ℂ) *
    ∏ 𝔭 ∈ ramifiedPrimes K F, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-1 : ℂ))
  set L₁ := LSeries (normCoeff K
    (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction)
  -- The residue `ρ` of `L₁` at `s = 1` is nonzero: every deleted Euler factor is nonzero at `1`.
  have hρ : ρ ≠ 0 :=
    dedekindZeta_residue_mul_prod_one_sub_absNorm_cpow_neg_one_ne_zero
      (ramifiedPrimes K F)
  -- `H(s) = (s - 1) L₁(s)` continues holomorphically to `U`, with value `ρ` at `s = 1`.
  set H : ℂ → ℂ := fun s ↦ (s - 1) * G s + ρ
  have hH : DifferentiableOn ℂ H U := ((differentiableOn_id.sub_const 1).mul hG).add_const ρ
  have hsub {s : ℂ} (hs : 1 < s.re) : s - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ by simp [h] at hs
  have hHL {s : ℂ} (hs : 1 < s.re) : H s = (s - 1) * L₁ s := by
    simp only [H, hGL s hs, cyclotomicCharacterSeriesC_eq_LSeries K F 1 hs, L₁]
    field_simp [hsub hs]
    ring
  -- `H` does not vanish on `Re s ≥ 1`.
  have hH0 {s : ℂ} (hs : 1 ≤ s.re) : H s ≠ 0 := by
    rcases hs.lt_or_eq with hs | hs
    · rw [hHL hs]
      exact mul_ne_zero (hsub hs) (MonoidHom.LSeries_galoisCharacterWeight_ne_zero 1 hs)
    rcases eq_or_ne s 1 with rfl | hs1
    · simpa [H] using hρ
    -- Elsewhere on the line, `H(s) / (s - 1)` is a continuation of `L₁` differentiable at `s`.
    have hne := ne_zero_of_eqOn_LSeries_galoisCharacterWeight_one (K := K) (F := F)
      (f := fun z ↦ H z / (z - 1)) hs.symm hs1
      ((hH.differentiableAt (hU.mem_nhds
        (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.le))).div
        (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
      fun z (hz : 1 < z.re) ↦ by
        simp only [hHL hz, mul_div_cancel_left₀ _ (hsub hz), L₁]
    exact fun h ↦ hne (by simp [h])
  refine ⟨fun s ↦ -logDeriv H s, ?_, fun s hs ↦ ?_⟩
  · simp only [logDeriv_apply]
    exact (((hH.deriv hU).continuousOn.mono
      (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K)).div
      (hH.continuousOn.mono (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K))
      fun _ hs ↦ hH0 hs).neg
  -- On `Re s > 1`, `L₁ = H / (s - 1)` near `s`, so `L₁'/L₁ = H'/H - 1 / (s - 1)`.
  have hHs : DifferentiableAt ℂ H s :=
    hH.differentiableAt (hU.mem_nhds
      (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.le))
  have hL : logDeriv L₁ s = logDeriv (H / fun z ↦ z - 1) s :=
    (logDeriv_congr_nhds <| eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds hs) fun z (hz : 1 < z.re) ↦ by
        simp only [Pi.div_apply, hHL hz, mul_div_cancel_left₀ _ (hsub hz)]).eq_of_nhds
  dsimp only
  rw [hL, logDeriv_div (g := fun z ↦ z - 1) s (hH0 hs.le) (hsub hs) hHs
    (differentiableAt_id.sub_const 1), logDeriv_apply (· - 1), deriv_sub_const, deriv_id'']
  ring

end NumberField.Chebotarev
