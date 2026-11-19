/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Hadamard

/-!
# Selected-zero formulas and checks for primitive Dirichlet L-functions

For a nonprincipal primitive Dirichlet character `χ` modulo `q`, the real-part Hadamard identity
expresses the sum over the zeros of its entire completion directly through `L'/L`, the conductor
term `½ log q`, and the archimedean logarithmic derivative. The finite retained-zero inequality
in `Hadamard.lean` then gives a real-zero bound retaining the full analytic multiplicity.

The real-zero bound is valid for `1 ≤ σ ≤ 2`, including `σ = 1`, and for complex characters:
reality of `χ` is not assumed. The multiplicity is that of `χ.LFunction` on the positive
half-plane, where it agrees with the multiplicity of the entire completion. In particular,
a double real zero contributes `2 / (σ - β)`.

A concrete primitive character modulo `5` of order `4`, with `χ⁻¹ ≠ χ`, checks that the finite
inequality applies beyond real characters. All bounds use the existing absolute constant
`TauCeti.gammaLogDerivBound`. A separate algebraic inverse-real-part calculation checks the
positive sign of a discarded term without asserting that its literal point is an L-function zero.

## Main results

* `DirichletCharacter.tsum_divisor_mul_re_one_div_sub_eq_re_logDeriv_LFunction`: the direct
  real-part identity in terms of `L'/L`.

The real-zero bound with its full multiplicity is
`DirichletCharacter.analyticOrderNatAt_LFunction_div_sub_le_re_logDeriv_LFunction_add` in
`Hadamard.lean`. The examples below check the factor two for a double zero and construct an
actual primitive nonreal quartic character modulo `5`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), Theorem 10.16 and
  Corollary 10.18, (10.37)–(10.38).
-/

public section

open Complex TauCeti TauCeti.LFunctions

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

include hχ

/-- **The sum over zeros through `L'/L`.** On the positive half-plane, away from the zeros of
`L(χ, ·)`, `∑_ρ m_ρ Re (1 / (s - ρ)) = Re (L'/L)(s, χ) + ½ log q + Re (Γℝ'/Γℝ)(s + κ)`, the sum
running over all zeros of the entire completion with multiplicity. -/
theorem tsum_divisor_mul_re_one_div_sub_eq_re_logDeriv_LFunction (hne : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (hL : χ.LFunction s ≠ 0) :
    ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re =
      (logDeriv χ.LFunction s).re + Real.log N / 2 + (logDeriv χ.gammaFactor s).re := by
  have hΛ : (dirichletData χ hχ).entireCompletion s ≠ 0 :=
    (dirichletData_entireCompletion_eq_zero_iff χ hχ hne hs).not.mpr hL
  rw [← re_logDeriv_dirichletData_entireCompletion_eq_tsum χ hχ hΛ,
    logDeriv_dirichletData_entireCompletion χ hχ hne hs hL, add_re, add_re, div_ofNat_re,
    ofReal_re]
  ring

/-- A double real zero `β` contributes `2 / (σ - β)`: weighting every zero by `1` would halve
it. -/
example (hne : χ ≠ 1) {β σ : ℝ}
    (hβ : 0 < β) (h₂ : analyticOrderNatAt χ.LFunction β = 2) (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) :
    2 / (σ - β) ≤ (logDeriv χ.LFunction σ).re + Real.log N / 2 + gammaLogDerivBound := by
  have h := analyticOrderNatAt_LFunction_div_sub_le_re_logDeriv_LFunction_add χ hχ hne hβ hσ₁ hσ₂
  rwa [h₂, Nat.cast_ofNat] at h

end DirichletCharacter

namespace TauCeti.LFunctions

open _root_.DirichletCharacter

/-- This algebraic point checks the sign of a discarded term; it is not asserted to be an
L-function zero. Reversing the denominator would give the negative real part. -/
example :
    (1 / ((2 : ℂ) - ((1 / 2 : ℂ) + 14 * I))).re = 6 / 793 ∧
      0 < (1 / ((2 : ℂ) - ((1 / 2 : ℂ) + 14 * I))).re := by
  norm_num [Complex.div_re, Complex.normSq_apply]

/-- A nonreal character: there is a primitive character `χ` modulo `5` of order `4`, so
`χ⁻¹ ≠ χ`, and with `S = ∅` at `σ = 2` the finite-sum inequality reads
`0 ≤ Re (L'/L)(2, χ) + ½ log 5 + C_Γ`. A statement restricted to real characters would say
nothing here. -/
example :
    ∃ χ : DirichletCharacter ℂ 5, orderOf χ = 4 ∧ χ⁻¹ ≠ χ ∧ χ.IsPrimitive ∧
      0 ≤ (logDeriv χ.LFunction 2).re + Real.log 5 / 2 + gammaLogDerivBound := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod 5) (n := 4)
    (by rw [ZMod.card]) isPrimitiveRoot_I
  have hne : χ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hχ
    exact absurd hχ (by norm_num)
  have hprim : DirichletCharacter.IsPrimitive χ := by
    rcases Nat.prime_five.eq_one_or_self_of_dvd _ (DirichletCharacter.conductor_dvd_level χ) with
      h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) hne
    · exact h
  refine ⟨χ, hχ, fun hinv ↦ ?_, hprim, ?_⟩
  · have h2 : χ ^ 2 = 1 := by rw [sq]; nth_rw 1 [← hinv]; exact inv_mul_cancel χ
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hχ] at this
    exact absurd this (by norm_num)
  · simpa using
      sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add
        χ hprim hne ∅ (by simp) (σ := 2) ⟨by norm_num, le_rfl⟩

end TauCeti.LFunctions
