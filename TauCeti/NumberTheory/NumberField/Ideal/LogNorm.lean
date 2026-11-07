/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Associated

/-!
# Logarithmic norms of prime divisors of an ideal

The product of distinct prime ideals dividing a nonzero ideal divides that ideal.
Taking absolute norms and logarithms bounds the sum of the prime logarithmic norms
by the logarithmic norm of the original ideal.
-/

public section

open NumberField IsDedekindDomain
open scoped NumberField
namespace TauCeti
variable {K : Type*} [Field K] [NumberField K]

/-- The sum of logarithmic norms of distinct prime divisors is at most the logarithmic norm
of the nonzero ideal they divide. -/
theorem sum_log_absNorm_le_log_absNorm {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ P ∈ S, P.asIdeal ∣ I) :
    ∑ P ∈ S, Real.log (Ideal.absNorm P.asIdeal) ≤ Real.log (Ideal.absNorm I) := by
  classical
  let s : Finset (Ideal (𝓞 K)) := S.image (fun P ↦ P.asIdeal)
  have hprime : ∀ P ∈ s, Prime P := by
    intro P hP
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hP
    exact Q.prime
  have hdvd : ∀ P ∈ s, P ∣ I := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact hS Q hQ
  have hprod := Finset.prod_primes_dvd I hprime hdvd
  have heq : (∏ P ∈ s, P) = ∏ P ∈ S, P.asIdeal := by
    exact Finset.prod_image (fun _ _ _ _ h ↦ HeightOneSpectrum.asIdeal_injective h)
  rw [heq] at hprod
  have hN : (∏ P ∈ S, Ideal.absNorm P.asIdeal) ≤ Ideal.absNorm I := by
    have h := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm hprod)
    simpa only [map_prod] using h
  rw [← Real.log_prod (fun P _ ↦ by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot))]
  apply Real.log_le_log
  · apply Finset.prod_pos
    intro P _
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  · exact_mod_cast hN

end TauCeti
