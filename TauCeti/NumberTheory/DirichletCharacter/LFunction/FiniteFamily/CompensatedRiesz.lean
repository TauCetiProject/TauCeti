/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin

/-!
# The compensated mean in a signed Dirichlet Riesz transform

For a signed family formed by all characters of one modulus and a corresponding family of
nonprincipal characters, the average of the individual Riesz transforms can also be computed
from a single mean of logarithmic derivatives. The principal character contributes the
pole-cleared derivative at `1` and the extra constant `-1 / φ(q)` in that mean. This identifies
the quotient obtained by transforming a smoothed prime sum with the sum of the individual
meromorphic Riesz expressions, to which pole calculations apply.

The normalization is that of `New.integral_primeRemainder` in
`grh/src/New/Reduction/Zeros/PrimeError.lean` of the shorter GRH formalization
(<https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh>).
-/

public section

open Complex TauCeti

namespace DirichletCharacter

/-- A finite sum of nonprincipal Riesz expressions, with the common Riesz denominator factored
out. The family may have repeated characters. -/
theorem sum_rieszRemainderMellin_of_ne_one {ι : Type*} (S : Finset ι) {N : ℕ} [NeZero N]
    (χ : ι → DirichletCharacter ℂ N) (hχ : ∀ i ∈ S, χ i ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    (∑ i ∈ S, rieszRemainderMellin (χ i).LFunction s) =
      (s * (∑ i ∈ S, logDeriv (χ i).LFunction 1) - ∑ i ∈ S, logDeriv (χ i).LFunction s) /
        (s * (s - 1)) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun i hi ↦ (χ i).rieszRemainderMellin_LFunction_of_ne_one (hχ i hi) hs

open ArithmeticFunction.vonMangoldt in
/-- The average of the Riesz expressions over all characters modulo `q`, evaluated
on `Re s > 1`, is the compensated difference quotient of the class-`1` auxiliary function
minus `1 / φ(q)`. -/
theorem sum_rieszRemainderMellin_div_totient (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    (∑ χ : DirichletCharacter ℂ q, rieszRemainderMellin χ.LFunction s) / (q.totient : ℂ) =
      ((LFunctionResidueClassAux (1 : ZMod q) s - (q.totient : ℂ)⁻¹) / s -
        (LFunctionResidueClassAux (1 : ZMod q) 1 - (q.totient : ℂ)⁻¹)) / (s - 1) := by
  classical
  let S : Finset (DirichletCharacter ℂ q) := {1}ᶜ
  have hsplit := Finset.sum_compl_add_sum ({1} : Finset (DirichletCharacter ℂ q))
    (fun χ ↦ rieszRemainderMellin χ.LFunction s)
  rw [← hsplit, Finset.sum_singleton, rieszRemainderMellin_LFunctionTrivChar q hs]
  have hsum := sum_rieszRemainderMellin_of_ne_one S id (fun χ hχ ↦ by simpa [S] using hχ) hs
  simp only [S, id_eq] at hsum
  rw [hsum]
  unfold LFunctionResidueClassAux
  simp only [ZMod.inv_one, MulChar.map_one, one_mul, logDeriv_apply]
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have h₁ : s ≠ 1 := by rintro rfl; simp at hs
  field_simp [h₀, sub_ne_zero.mpr h₁]
  ring

open ArithmeticFunction.vonMangoldt in
/-- On `Re s > 1`, the normalized signed Riesz sum agrees with the difference quotient of the
compensated logarithmic-derivative mean. The negative family consists of nonprincipal characters
so it contributes no polar term to the mean at `1`. In the quadratic twist application, `ξ χ`
is the twist of `χ`. -/
theorem sum_sub_rieszRemainderMellin_eq_compensated_mean {q N : ℕ} [NeZero q] [NeZero N]
    (ξ : DirichletCharacter ℂ q → DirichletCharacter ℂ N) (hξ : ∀ χ, ξ χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    let G (w : ℂ) := LFunctionResidueClassAux (1 : ZMod q) w +
      (∑ χ, logDeriv (ξ χ).LFunction w) / (q.totient : ℂ) - (q.totient : ℂ)⁻¹
    (∑ χ, (rieszRemainderMellin χ.LFunction s - rieszRemainderMellin (ξ χ).LFunction s)) /
        (q.totient : ℂ) = (G s / s - G 1) / (s - 1) := by
  dsimp only
  rw [Finset.sum_sub_distrib, sub_div, sum_rieszRemainderMellin_div_totient q hs]
  rw [sum_rieszRemainderMellin_of_ne_one _ ξ (fun χ _ ↦ hξ χ) hs]
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have h₁ : s ≠ 1 := by rintro rfl; simp at hs
  field_simp [h₀, sub_ne_zero.mpr h₁]
  ring

end DirichletCharacter
