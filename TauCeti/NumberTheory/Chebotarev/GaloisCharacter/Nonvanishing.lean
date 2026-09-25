/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.ThreeFourOne
import TauCeti.Analysis.Asymptotics.InvSubOne
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
import TauCeti.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Nonvanishing of Galois character series on the line `Re s = 1`

Let `F / K` be a finite Galois extension of number fields and `χ` a character of `Gal(F/K)`. This
file gives criteria for a function agreeing on `Re s > 1` with the `L`-series of
`galoisCharacterWeight χ` to be nonzero at a point `s` of the line `Re s = 1`. In particular the
series of the trivial character, which is the Dedekind zeta function of `K` with the Euler factors
at the primes ramified in `F` deleted, does not vanish at any `s ≠ 1` with `Re s = 1`.

Together with the continuation across `Re s = 1`, this is what makes the logarithmic derivatives
of these series, with the pole of the trivial one subtracted, continuous on `Re s ≥ 1`: the
boundary behaviour required to apply a Tauberian theorem to the Frobenius von Mangoldt series.

## Main results

* `NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight`: a continuation of the
  series of `χ`, differentiable at `s = 1 + it`, is nonzero at `s` provided some continuation of
  the series of `χ²` is continuous at `1 + 2it`.
* `NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight_of_sq_eq_one`: for
  `χ² = 1`, a continuation of the series of `χ` is nonzero on `Re s = 1` away from `s = 1`.
* `NumberField.Chebotarev.ne_zero_of_eqOn_LSeries_galoisCharacterWeight_one`: a continuation of
  the trivial-character series is nonzero on `Re s = 1` away from `s = 1`.

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
        exact sub_lt_self 1 (one_div_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos))
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

end NumberField.Chebotarev
