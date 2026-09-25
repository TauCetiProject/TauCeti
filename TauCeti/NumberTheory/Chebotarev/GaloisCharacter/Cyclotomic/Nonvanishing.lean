/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Series
import TauCeti.Analysis.Asymptotics.InvSubOne
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.ThreeFourOne
import TauCeti.NumberTheory.LSeries.Nonvanishing

/-!
# Nonvanishing of Galois character series on the line `Re s = 1`

Let `F / K` be a finite Galois extension of number fields. This file proves that the continued
`L`-series of the characters of `Gal(F/K)` have no zeros on the line `Re s = 1`, apart from the
pole of the trivial character at `s = 1`:

* the series of the trivial character, which is the Dedekind zeta function of `K` with the Euler
  factors at the primes ramified in `F` deleted, does not vanish at any `s ≠ 1` with `Re s = 1`;
  this holds for every function differentiable at `s` that agrees with the series on `Re s > 1`;
* for `F = K(μ_m)` and a nontrivial character `χ`, the continued series
  `cyclotomicCharacterSeriesC K F χ` does not vanish anywhere on `Re s = 1`.

Together with the continuation across `Re s = 1`, this is what makes the logarithmic derivatives
of these series, with the pole of the trivial one subtracted, continuous on `Re s ≥ 1`: the
boundary behaviour required to apply a Tauberian theorem to the Frobenius von Mangoldt series.

The proof is the classical `3-4-1` argument: the Euler-product bound
`norm_galoisCharacterLSeries_threeFourOne_ge_one` combined with the analytic criterion
`TauCeti.LSeries.ne_zero_of_threeFourOne`. The series of `χ²` must stay bounded near `1 + 2it`.
When `χ² ≠ 1` this is its continuation; when `χ² = 1` it is the continued trivial series, which is
bounded there once `t ≠ 0`; and at `s = 1` itself a nontrivial `χ` is handled by
`cyclotomicCharacterSeriesC_ne_zero_at_one`.

## Main results

* `NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight_one`: a continuation of
  the trivial-character series is nonzero on `Re s = 1` away from `s = 1`.
* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_ne_zero_of_re_eq_one`: for `F = K(μ_m)`
  and `χ ≠ 1`, the continued series of `χ` is nonzero on `Re s = 1`.

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

-- The line `Re s = 1` lies in the half-plane `Re s > 1 - 1 / [K : ℚ]` of the continuations.
private theorem mem_nhds_halfPlane_of_re_eq_one {s : ℂ} (hs : s.re = 1) :
    {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} ∈ 𝓝 s :=
  (isOpen_lt continuous_const continuous_re).mem_nhds <| by
    rw [Set.mem_ofPred_eq, hs]
    exact sub_lt_self 1 (one_div_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos))

variable (K F) in
-- The series of the trivial character continues to a function differentiable at every point of
-- `Re s = 1` other than the pole `s = 1`.
private theorem exists_differentiableAt_eqOn_LSeries_galoisCharacterWeight_one :
    ∃ T : ℂ → ℂ, (∀ s : ℂ, s.re = 1 → s ≠ 1 → DifferentiableAt ℂ T s) ∧
      Set.EqOn T (LSeries (normCoeff K
        (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction))
        {s | 1 < s.re} := by
  obtain ⟨G, hG, hGL⟩ := exists_differentiableOn_eq_cyclotomicCharacterSeriesC_one_sub K F
  set ρ := dedekindZeta_residue K *
    ∏ 𝔭 ∈ ramifiedPrimes K F, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-1 : ℂ))
  refine ⟨fun s ↦ G s + ρ / (s - 1), fun s hs hs1 ↦ ?_, fun s (hs : 1 < s.re) ↦ ?_⟩
  · exact (hG.differentiableAt (mem_nhds_halfPlane_of_re_eq_one hs)).add
      ((differentiableAt_const ρ).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
  · dsimp only
    rw [hGL s hs, cyclotomicCharacterSeriesC_eq_LSeries K F 1 hs, sub_add_cancel]

-- The reflection `2s - 1` of `1` through a point `s` of the line `Re s = 1` stays on that line,
-- and differs from `1` unless `s` does.
private theorem re_two_mul_sub_one {s : ℂ} (hs : s.re = 1) : (2 * s - 1).re = 1 := by
  norm_num [hs]

private theorem two_mul_sub_one_ne_one {s : ℂ} (hs1 : s ≠ 1) : 2 * s - 1 ≠ 1 :=
  fun h ↦ hs1 (by linear_combination h / 2)

-- **The `3-4-1` argument for a Galois character.** Let `s = 1 + it`. If `f` is differentiable at
-- `s` and `f₂` is continuous at `1 + 2it = 2s - 1`, and they agree on `Re s > 1` with the series of
-- `χ` and of `χ²` respectively, then `f s ≠ 0`.
private theorem ne_zero_of_eqOn_LSeries_galoisCharacterWeight (χ : (F ≃ₐ[K] F) →* ℂˣ) {s : ℂ}
    (hs : s.re = 1) {f f₂ : ℂ → ℂ} (hf : DifferentiableAt ℂ f s)
    (hfL : Set.EqOn f (LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction))
      {z | 1 < z.re})
    (hf₂ : ContinuousAt f₂ (2 * s - 1))
    (hf₂L : Set.EqOn f₂
      (LSeries (normCoeff K (χ ^ 2).galoisCharacterWeight.toIdealArithmeticFunction))
      {z | 1 < z.re}) :
    f s ≠ 0 := by
  -- Write `s = 1 + it`, so that `2s - 1 = 1 + 2it`.
  have hs' : s = 1 + I * s.im := by
    conv_lhs => rw [← re_add_im s, hs, ofReal_one, mul_comm]
  have hs₂ : 2 * s - 1 = 1 + 2 * I * s.im := by
    conv_lhs => rw [hs']
    ring
  rw [hs'] at hf ⊢
  rw [hs₂] at hf₂
  refine LSeries.ne_zero_of_threeFourOne ?_ ?_ hf hf₂
    (f₀ := LSeries (normCoeff K
      (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction))
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    rw [hfL (by simpa using hσ), hf₂L (by simpa using hσ)]
    exact norm_galoisCharacterLSeries_threeFourOne_ge_one χ hσ s.im
  · -- The trivial series has a simple pole at `s = 1`.
    rw [MonoidHom.galoisCharacterWeight_one]
    exact isBigO_inv_sub_one_of_tendsto_sub_one_mul <| by
      simpa using tendsto_sub_one_mul_LSeries_ofBadPrimes (K := K) (ramifiedPrimes K F)

/-- **The trivial-character series has no zeros on `Re s = 1` except at the pole.** Let `F / K`
be a finite Galois extension. If `f` agrees on `Re s > 1` with the `L`-series of the trivial
character of `Gal(F/K)`, which is the Dedekind zeta function of `K` with the Euler factors at the
ramified primes deleted, and `f` is complex differentiable at a point `s ≠ 1` with `Re s = 1`, then
`f s ≠ 0`. -/
theorem ne_zero_of_eqOn_LSeries_galoisCharacterWeight_one {f : ℂ → ℂ} {s : ℂ} (hs : s.re = 1)
    (hs1 : s ≠ 1) (hf : DifferentiableAt ℂ f s)
    (hfL : Set.EqOn f (LSeries (normCoeff K
      (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction)) {z | 1 < z.re}) :
    f s ≠ 0 := by
  obtain ⟨T, hT, hTL⟩ := exists_differentiableAt_eqOn_LSeries_galoisCharacterWeight_one K F
  refine ne_zero_of_eqOn_LSeries_galoisCharacterWeight 1 hs hf hfL
    (hT _ (re_two_mul_sub_one hs) (two_mul_sub_one_ne_one hs1)).continuousAt ?_
  rwa [show (1 : (F ≃ₐ[K] F) →* ℂˣ) ^ 2 = 1 by ext; simp]

/-- **Nonvanishing on `Re s = 1`.** For `F = K(μ_m)` and a nontrivial character `χ` of
`Gal(F/K)`, the continued `L`-series of `χ` does not vanish at any `s` with `Re s = 1`. -/
theorem cyclotomicCharacterSeriesC_ne_zero_of_re_eq_one (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s.re = 1) : cyclotomicCharacterSeriesC K F χ s ≠ 0 := by
  obtain rfl | hs1 := eq_or_ne s 1
  · exact cyclotomicCharacterSeriesC_ne_zero_at_one K F m χ hχ
  have hdiff (ψ : (F ≃ₐ[K] F) →* ℂˣ) (hψ : ψ ≠ 1) {z : ℂ} (hz : z.re = 1) :
      DifferentiableAt ℂ (cyclotomicCharacterSeriesC K F ψ) z :=
    (differentiableOn_cyclotomicCharacterSeriesC K F m ψ hψ).differentiableAt
      (mem_nhds_halfPlane_of_re_eq_one hz)
  have hL (ψ : (F ≃ₐ[K] F) →* ℂˣ) : Set.EqOn (cyclotomicCharacterSeriesC K F ψ)
      (LSeries (normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction)) {z | 1 < z.re} :=
    fun z hz ↦ cyclotomicCharacterSeriesC_eq_LSeries K F ψ hz
  by_cases hχ2 : χ ^ 2 = 1
  · -- For quadratic `χ` the series of `χ²` is the trivial one, which is differentiable at
    -- `2s - 1 ≠ 1`.
    obtain ⟨T, hT, hTL⟩ := exists_differentiableAt_eqOn_LSeries_galoisCharacterWeight_one K F
    exact ne_zero_of_eqOn_LSeries_galoisCharacterWeight χ hs (hdiff χ hχ hs) (hL χ)
      (hT _ (re_two_mul_sub_one hs) (two_mul_sub_one_ne_one hs1)).continuousAt (by rwa [hχ2])
  · exact ne_zero_of_eqOn_LSeries_galoisCharacterWeight χ hs (hdiff χ hχ hs) (hL χ)
      (hdiff (χ ^ 2) hχ2 (re_two_mul_sub_one hs)).continuousAt (hL (χ ^ 2))

end NumberField.Chebotarev
