/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.PrimeIdealBoundary

/-!
# The prime ideal theorem

The analytic boundary data of the Dedekind zeta function supplies the generic prime-number-theorem
transfer with residue one. This gives asymptotics for the three standard counting functions of
prime ideals in a number field: Chebyshev's `ψ` and `ϑ`, and the unweighted count `π`.

## Main results

* `TauCeti.primeIdealTheorem`: `ψ_K(x) ~ x`, `ϑ_K(x) ~ x`, and `π_K(x) ~ Li(x)`.
* `TauCeti.primeCount_univ_isEquivalent_div_log`: the classical form `π_K(x) ~ x / log x`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* H. Davenport, *Multiplicative Number Theory*, Chapter 17.
-/

public section

namespace TauCeti

open NumberField Asymptotics Filter

variable (K : Type*) [Field K] [NumberField K]

/-- **The prime ideal theorem.** For a number field `K`, Chebyshev's functions satisfy
`ψ_K(x) ~ x` and `ϑ_K(x) ~ x`, and the number `π_K(x)` of prime ideals of norm at most `x`
satisfies `π_K(x) ~ Li(x)`. -/
theorem primeIdealTheorem :
    primePsi K Set.univ ~[atTop] (fun x : ℝ ↦ x) ∧
      primeTheta K Set.univ ~[atTop] (fun x : ℝ ↦ x) ∧
      primeCount K Set.univ ~[atTop] Real.logIntegral :=
  primeIdealTheorem_of_boundary (LFunctions.primeIdealVonMangoldtBoundary K)

/-- Chebyshev's function for the prime ideals of a number field has a linear bound for
all nonnegative cutoffs, not just eventually. -/
theorem exists_primePsi_univ_le_mul : ∃ C ≥ (0 : ℝ), ∀ x ≥ (0 : ℝ),
    primePsi K Set.univ x ≤ C * x := by
  obtain ⟨B, hB₀, hB⟩ := (primeIdealTheorem K).1.isBigO.exists_pos
  obtain ⟨X, hX⟩ := eventually_atTop.mp hB.bound
  have hC : 0 ≤ max B (primePsi K Set.univ X) := hB₀.le.trans (le_max_left ..)
  refine ⟨_, hC, fun x hx ↦ ?_⟩
  by_cases h : X ≤ x
  · calc
      primePsi K Set.univ x ≤ B * x := by
        refine (le_abs_self _).trans ?_
        simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hX x h
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) hx
  by_cases hx₁ : 1 ≤ x
  · calc
      primePsi K Set.univ x ≤ primePsi K Set.univ X := primePsi_mono Set.univ (le_of_not_ge h)
      _ ≤ max B (primePsi K Set.univ X) := le_max_right ..
      _ ≤ _ := le_mul_of_one_le_right hC hx₁
  · rw [primePsi_eq_zero_of_lt_two Set.univ ((lt_of_not_ge hx₁).trans one_lt_two)]
    exact mul_nonneg hC hx

/-- **The prime ideal theorem, in the form `π_K(x) ~ x / log x`.** -/
theorem primeCount_univ_isEquivalent_div_log :
    primeCount K Set.univ ~[atTop] fun x : ℝ ↦ x / Real.log x :=
  (primeIdealTheorem K).2.2.trans Real.logIntegral_isEquivalent_div_log

end TauCeti
