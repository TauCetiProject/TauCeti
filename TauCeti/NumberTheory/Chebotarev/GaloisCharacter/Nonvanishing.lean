/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.ThreeFourOne
import TauCeti.Analysis.Asymptotics.InvSubOne
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Weight
import TauCeti.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Nonvanishing of Galois character series on the line `Re s = 1`

Let `F / K` be a finite Galois extension of number fields and `χ` a character of `Gal(F/K)`. On
`Re s > 1` the `L`-series of `galoisCharacterWeight χ` does not vanish, by its Euler product. This
file gives criteria for a function agreeing on `Re s > 1` with the `L`-series of
`galoisCharacterWeight χ` to be nonzero at a point `s` of the line `Re s = 1`. In particular the
series of the trivial character, which is the Dedekind zeta function of `K` with the Euler factors
at the primes ramified in `F` deleted, does not vanish at any `s ≠ 1` with `Re s = 1`.

Together with the continuation across `Re s = 1`, this is what makes the logarithmic derivatives
of these series, with the pole of the trivial one subtracted, continuous on `Re s ≥ 1`: the
boundary behaviour required to apply a Tauberian theorem to the Frobenius von Mangoldt series.

## Main results

* `MonoidHom.LSeries_galoisCharacterWeight_ne_zero`: the series of `χ` is nonzero on `Re s > 1`.
* `NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight`: a continuation of the
  series of `χ`, differentiable at `s = 1 + it`, is nonzero at `s` provided some continuation of
  the series of `χ²` is continuous at `1 + 2it`.
* `NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight_of_sq_eq_one`: for
  `χ² = 1`, a continuation of the series of `χ` is nonzero on `Re s = 1` away from `s = 1`.
* `NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight_one`: a continuation of
  the trivial-character series is nonzero on `Re s = 1` away from `s = 1`.
* `NumberField.Chebotarev.exists_continuousOn_eq_neg_logDeriv_galoisCharacterWeight_one_sub`:
  the regularized logarithmic derivative of the trivial character extends continuously to
  `Re s ≥ 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The case analysis on `χ²` follows Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`
  (Michael Stoll and David Loeffler), where `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`
  proves the analogous statement for Dirichlet `L`-functions.
-/

public section

open Complex Filter IsDedekindDomain NumberField TauCeti
open scoped Topology

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

/-- **Nonvanishing on `Re s > 1`.** For a finite Galois extension `F / K` and a character `χ` of
`Gal(F/K)`, the `L`-series of `galoisCharacterWeight χ` is nonzero at every `s` with `1 < Re s`,
where its Euler product converges absolutely. -/
theorem MonoidHom.LSeries_galoisCharacterWeight_ne_zero (χ : (F ≃ₐ[K] F) →* ℂˣ) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction) s ≠ 0 :=
  χ.galoisCharacterWeight.LSeries_ne_zero_of_summable_idealTerm
    (χ.summable_idealTerm_galoisCharacterWeight hs)

namespace NumberField.Chebotarev

variable (K F) in
-- The series of the trivial character continues to a function differentiable at every point of
-- `Re s = 1` other than the pole `s = 1`.
private theorem exists_differentiableAt_eqOn_LSeries_galoisCharacterWeight_one :
    ∃ T : ℂ → ℂ, (∀ s : ℂ, s.re = 1 → s ≠ 1 → DifferentiableAt ℂ T s) ∧
      Set.EqOn T (LSeries (normCoeff K
        (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction))
        {s | 1 < s.re} := by
  obtain ⟨G, hG, hGL⟩ := exists_differentiableOn_eq_LSeries_ofBadPrimes_sub K (ramifiedPrimes K F)
  set ρ := dedekindZeta_residue K *
    ∏ 𝔭 ∈ ramifiedPrimes K F, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-1 : ℂ))
  refine ⟨fun s ↦ G s + ρ / (s - 1), fun s hs hs1 ↦ ?_, fun s (hs : 1 < s.re) ↦ ?_⟩
  · -- The line `Re s = 1` lies in the half-plane `Re s > 1 - 1 / [K : ℚ]` of the continuation.
    have hmem : {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const continuous_re).mem_nhds <| by
        rw [Set.mem_ofPred_eq, hs]
        simpa only [Set.mem_ofPred_eq, hs] using
          setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.ge
    exact (hG.differentiableAt hmem).add
      ((differentiableAt_const ρ).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
  · dsimp only
    rw [hGL s hs, MonoidHom.galoisCharacterWeight_one, sub_add_cancel]

/-- **The `3-4-1` criterion for a Galois character.** Let `F / K` be a finite Galois extension,
`χ` a character of `Gal(F/K)`, and `s = 1 + it`. If `f` is complex differentiable at `s` and `f₂`
is continuous at `1 + 2it = 2s - 1`, and they agree on `Re s > 1` with the `L`-series of `χ` and of
`χ²` respectively, then `f s ≠ 0`. -/
theorem ne_zero_of_eqOn_LSeries_galoisCharacterWeight (χ : (F ≃ₐ[K] F) →* ℂˣ) {s : ℂ}
    (hs : s.re = 1) {f f₂ : ℂ → ℂ} (hf : DifferentiableAt ℂ f s)
    (hfL : Set.EqOn f (LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction))
      {z | 1 < z.re})
    (hf₂ : ContinuousAt f₂ (2 * s - 1))
    (hf₂L : Set.EqOn f₂
      (LSeries (normCoeff K (χ ^ 2).galoisCharacterWeight.toIdealArithmeticFunction))
      {z | 1 < z.re}) :
    f s ≠ 0 := by
  -- Write `s = 1 + it`, so that `2s - 1 = 1 + 2it`. The Euler-product bound
  -- `norm_galoisCharacterLSeries_threeFourOne_ge_one` and the simple pole of the trivial series
  -- at `s = 1` are the inputs of the analytic criterion `LSeries.ne_zero_of_threeFourOne`.
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

/-- **Nonvanishing on `Re s = 1` for a character of order at most two.** Let `F / K` be a finite
Galois extension and `χ` a character of `Gal(F/K)` with `χ² = 1`. If `f` agrees on `Re s > 1` with
the `L`-series of `χ` and is complex differentiable at a point `s ≠ 1` with `Re s = 1`, then
`f s ≠ 0`. -/
theorem ne_zero_of_eqOn_LSeries_galoisCharacterWeight_of_sq_eq_one (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (hχ : χ ^ 2 = 1) {f : ℂ → ℂ} {s : ℂ} (hs : s.re = 1) (hs1 : s ≠ 1)
    (hf : DifferentiableAt ℂ f s)
    (hfL : Set.EqOn f (LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction))
      {z | 1 < z.re}) :
    f s ≠ 0 := by
  -- The series of `χ² = 1` is the trivial one, which is differentiable at `2s - 1 ≠ 1`.
  obtain ⟨T, hT, hTL⟩ := exists_differentiableAt_eqOn_LSeries_galoisCharacterWeight_one K F
  have hs₂ : (2 * s - 1).re = 1 := by norm_num [hs]
  have hs₂1 : 2 * s - 1 ≠ 1 := fun h ↦ hs1 (by linear_combination h / 2)
  exact ne_zero_of_eqOn_LSeries_galoisCharacterWeight χ hs hf hfL (hT _ hs₂ hs₂1).continuousAt
    (by rwa [hχ])

/-- **The trivial-character series has no zeros on `Re s = 1` except at the pole.** Let `F / K`
be a finite Galois extension. If `f` agrees on `Re s > 1` with the `L`-series of the trivial
character of `Gal(F/K)`, which is the Dedekind zeta function of `K` with the Euler factors at the
ramified primes deleted, and `f` is complex differentiable at a point `s ≠ 1` with `Re s = 1`, then
`f s ≠ 0`. -/
theorem ne_zero_of_eqOn_LSeries_galoisCharacterWeight_one {f : ℂ → ℂ} {s : ℂ} (hs : s.re = 1)
    (hs1 : s ≠ 1) (hf : DifferentiableAt ℂ f s)
    (hfL : Set.EqOn f (LSeries (normCoeff K
      (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction)) {z | 1 < z.re}) :
    f s ≠ 0 :=
  ne_zero_of_eqOn_LSeries_galoisCharacterWeight_of_sq_eq_one 1
    (one_pow (M := (F ≃ₐ[K] F) →* ℂˣ) 2) hs hs1 hf hfL

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
  obtain ⟨G, hG, hGL⟩ := exists_differentiableOn_eq_LSeries_ofBadPrimes_sub K
    (ramifiedPrimes K F)
  set U := {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  set ρ := (dedekindZeta_residue K : ℂ) *
    ∏ 𝔭 ∈ ramifiedPrimes K F, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-1 : ℂ))
  set L₁ := LSeries (normCoeff K
    (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction)
  have hGL' {s : ℂ} (hs : 1 < s.re) : G s = L₁ s - ρ / (s - 1) := by
    dsimp only [L₁, ρ]
    rw [MonoidHom.galoisCharacterWeight_one]
    exact hGL s hs
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
    simp only [H, hGL' hs]
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
