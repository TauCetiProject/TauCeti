/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.Bound
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Hadamard

/-!
# Retained-zero inequalities for primitive Dirichlet L-functions

Let `χ` be a nonprincipal primitive Dirichlet character modulo `q`, and write `κ` for its parity
(`0` for even and `1` for odd `χ`). The partial-fraction expansion of the entire completion
`Λ₀ = q^(s/2) Λ(χ, s)` and the real-part identity `Re B(χ) = -∑_ρ m_ρ Re (1 / ρ)` give, on the
positive half-plane away from the zeros of `L(χ, ·)`,

  `∑_ρ m_ρ Re (1 / (s - ρ)) = Re (L'/L)(s, χ) + ½ log q + Re (Γℝ'/Γℝ)(s + κ)`,

the sum running over all zeros of the completion with multiplicity. For real `1 ≤ σ ≤ 2` every
summand is nonnegative, since every zero has real part below `1`, and the gamma term is at most
`C_Γ = TauCeti.gammaLogDerivBound` because `σ + κ ∈ [1, 3]`. Discarding all but finitely many
zeros, and all copies of a real zero `β` but one, gives

  `∑_{ρ ∈ S} m_ρ Re (1 / (σ - ρ)) ≤ Re (L'/L)(σ, χ) + ½ log q + C_Γ`   and
  `1 / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log q + C_Γ`,

with multiplicities `m_ρ = analyticOrderNatAt L(χ, ·) ρ` and the explicit constant `C_Γ`, which
does not depend on `S`, `q`, `χ`, `β` or `σ`. Reality of `χ` is not used: for a nonreal character
`(L'/L)(σ, χ)` is complex, and its real part stands on the right.

The zeros in `S` are required to satisfy `0 < Re ρ`. On that half-plane the zeros of `L(χ, ·)`
and of the completion agree with multiplicity, while for an even character the trivial zero at
`0` of `L(χ, ·)` is not a zero of the completion.

## Main results

* `TauCeti.LFunctions.tsum_divisor_mul_re_one_div_sub_eq_re_logDeriv_LFunction`: the identity
  above.
* `TauCeti.LFunctions.finite_zero_sum_le_logDeriv`: the finite-sum inequality.
* `TauCeti.LFunctions.analyticOrderNatAt_div_sub_le_logDeriv` and
  `TauCeti.LFunctions.one_zero_le_logDeriv`: the inequality for one real zero, with its
  multiplicity and with a single copy.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), Theorem 10.16 and
  Corollary 10.18, (10.37)–(10.38).
-/

public section

open Complex

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- For real `1 ≤ σ ≤ 2` the archimedean term `Γℝ'/Γℝ (σ + κ)` of a Dirichlet character of either
parity `κ` has norm at most `C_Γ`. -/
theorem norm_logDeriv_gammaFactor_ofReal_le {σ : ℝ} (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) :
    ‖logDeriv χ.gammaFactor σ‖ ≤ TauCeti.gammaLogDerivBound := by
  rcases χ.even_or_odd with he | ho
  · rw [he.logDeriv_gammaFactor]
    exact norm_logDeriv_Gammaℝ_ofReal_le ⟨hσ₁, by linarith⟩
  · rw [ho.logDeriv_gammaFactor, ← ofReal_one, ← ofReal_add]
    exact norm_logDeriv_Gammaℝ_ofReal_le ⟨by linarith, by linarith⟩

end DirichletCharacter

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

include hχ

/-- On the positive half-plane the multiplicity read from the divisor of the entire completion is
the analytic order of `L(χ, ·)`. -/
theorem divisor_dirichletData_entireCompletion_toNat_eq_analyticOrderNatAt (hne : χ ≠ 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat =
      analyticOrderNatAt χ.LFunction ρ := by
  have h := dirichletData_hasMeromorphicContinuation χ hχ
  rw [MeromorphicOn.divisor_eq_analyticOrderNatAt h.meromorphicOn_entireCompletion
    (h.analyticAt_entireCompletion ρ) (Set.mem_univ ρ), Int.toNat_natCast, analyticOrderNatAt,
    analyticOrderNatAt, analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hρ]

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
  rw [← re_logDeriv_dirichletData_entireCompletion_eq_tsum χ hχ hne hΛ,
    logDeriv_dirichletData_entireCompletion χ hχ hne hs hL, add_re, add_re, div_ofNat_re,
    ofReal_re]
  ring

/-- **Finitely many zeros.** For a nonprincipal primitive character `χ` modulo `q`, real
`1 ≤ σ ≤ 2` and a finite set `S` of points with `0 < Re ρ`,
`∑_{ρ ∈ S} m_ρ Re (1 / (σ - ρ)) ≤ Re (L'/L)(σ, χ) + ½ log q + C_Γ`, where `m_ρ` is the analytic
order of `L(χ, ·)` at `ρ`, so that only the zeros of `L(χ, ·)` in `S` contribute. The constant
`C_Γ` is fixed before `S`, `q`, `χ` and `σ`, and reality of `χ` is not used. -/
theorem finite_zero_sum_le_logDeriv (hne : χ ≠ 1) (S : Finset ℂ) (hS : ∀ ρ ∈ S, 0 < ρ.re)
    {σ : ℝ} (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) :
    ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (σ - ρ)).re ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + gammaLogDerivBound := by
  set d := MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ
  set f : ℂ → ℝ := fun ρ ↦ ((d ρ).toNat : ℝ) * (1 / ((σ : ℂ) - ρ)).re
  have hσre : 1 ≤ (σ : ℂ).re := by rwa [ofReal_re]
  have hL : χ.LFunction σ ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inl hne) hσre
  have hΛ : (dirichletData χ hχ).entireCompletion σ ≠ 0 :=
    dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne hσre
  -- Extend the sum over the zeros by zero to all of `ℂ`.
  have hsupp : Function.support f ⊆ d.support := fun ρ hρ hd ↦ hρ (by simp [f, hd])
  have hsum : Summable f := by
    have h : Summable fun ρ : d.support ↦ f ρ :=
      summable_divisor_dirichletData_entireCompletion_mul_re_one_div_sub χ hχ hne hΛ
    rw [← Set.indicator_eq_self.mpr hsupp]
    exact summable_subtype_iff_indicator.mp h
  calc ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (σ - ρ)).re
      = ∑ ρ ∈ S, f ρ := Finset.sum_congr rfl fun ρ hρ ↦ by
        simp only [f, d, divisor_dirichletData_entireCompletion_toNat_eq_analyticOrderNatAt χ hχ
          hne (hS ρ hρ)]
    _ ≤ ∑' ρ, f ρ := hsum.sum_le_tsum S fun ρ _ ↦
        divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg χ hχ hne hσre ρ
    _ = ∑' ρ : d.support, f ρ := (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = (logDeriv χ.LFunction σ).re + Real.log N / 2 + (logDeriv χ.gammaFactor σ).re :=
        tsum_divisor_mul_re_one_div_sub_eq_re_logDeriv_LFunction χ hχ hne
          (by rw [ofReal_re]; linarith) hL
    _ ≤ (logDeriv χ.LFunction σ).re + Real.log N / 2 + gammaLogDerivBound := by
        gcongr
        exact (re_le_norm _).trans (χ.norm_logDeriv_gammaFactor_ofReal_le hσ₁ hσ₂)

/-- **A real zero with its multiplicity.** For a nonprincipal primitive character `χ` modulo `q`,
real `0 < β` and `1 ≤ σ ≤ 2`, `m_β / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log q + C_Γ`, where `m_β` is the
analytic order of `L(χ, ·)` at `β`. -/
theorem analyticOrderNatAt_div_sub_le_logDeriv (hne : χ ≠ 1) {β σ : ℝ} (hβ : 0 < β)
    (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) :
    (analyticOrderNatAt χ.LFunction β : ℝ) / (σ - β) ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + gammaLogDerivBound := by
  have h := finite_zero_sum_le_logDeriv χ hχ hne {(β : ℂ)}
    (by simpa only [Finset.mem_singleton, forall_eq, ofReal_re] using hβ) hσ₁ hσ₂
  rwa [Finset.sum_singleton, ← ofReal_sub, one_div, ← ofReal_inv, ofReal_re,
    ← div_eq_mul_inv] at h

/-- **One retained zero.** For a nonprincipal primitive character `χ` modulo `q`, a real zero
`0 < β` of `L(χ, ·)` and real `1 ≤ σ ≤ 2`, `1 / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log q + C_Γ`. The
constant `C_Γ` is fixed before `q`, `χ`, `β` and `σ`, the zero may have any positive multiplicity,
and reality of `χ` is not used. -/
theorem one_zero_le_logDeriv (hne : χ ≠ 1) {β σ : ℝ} (hβ : 0 < β) (hLβ : χ.LFunction β = 0)
    (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) :
    1 / (σ - β) ≤ (logDeriv χ.LFunction σ).re + Real.log N / 2 + gammaLogDerivBound := by
  have hβ₁ : β < 1 := by
    by_contra h
    exact χ.LFunction_ne_zero_of_one_le_re (.inl hne) (by simpa using not_lt.mp h) hLβ
  -- The analytic order at `β` is finite, as for the completion, and positive.
  have hβre : 0 < (β : ℂ).re := by rwa [ofReal_re]
  have hord : analyticOrderAt χ.LFunction β ≠ ⊤ := by
    rw [← analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hβre]
    exact analyticOrderAt_dirichletData_entireCompletion_ne_top χ hχ hne β
  have hord₀ : analyticOrderAt χ.LFunction β ≠ 0 :=
    ((DirichletCharacter.differentiable_LFunction hne).analyticAt _).analyticOrderAt_ne_zero.mpr
      hLβ
  have hm : (1 : ℝ) ≤ analyticOrderNatAt χ.LFunction β := by
    rw [Nat.one_le_cast, Nat.one_le_iff_ne_zero, analyticOrderNatAt, Ne, ENat.toNat_eq_zero]
    exact not_or_intro hord₀ hord
  refine le_trans ?_ (analyticOrderNatAt_div_sub_le_logDeriv χ hχ hne hβ hσ₁ hσ₂)
  gcongr
  linarith

/-! ### Checks -/

/-- A double real zero `β` contributes `2 / (σ - β)`: weighting every zero by `1` would halve
it. -/
theorem two_div_sub_le_logDeriv_of_analyticOrderNatAt_eq_two (hne : χ ≠ 1) {β σ : ℝ}
    (hβ : 0 < β) (h₂ : analyticOrderNatAt χ.LFunction β = 2) (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) :
    2 / (σ - β) ≤ (logDeriv χ.LFunction σ).re + Real.log N / 2 + gammaLogDerivBound := by
  have h := analyticOrderNatAt_div_sub_le_logDeriv χ hχ hne hβ hσ₁ hσ₂
  rwa [h₂, Nat.cast_ofNat] at h

omit [NeZero N] hχ in
/-- A nonreal character: there is a primitive character `χ` modulo `5` of order `4`, so
`χ⁻¹ ≠ χ`, and with `S = ∅` at `σ = 2` the finite-sum inequality reads
`0 ≤ Re (L'/L)(2, χ) + ½ log 5 + C_Γ`. A statement restricted to real characters would say
nothing here. -/
theorem exists_quartic_dirichletCharacter_five_logDeriv :
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
  · simpa using finite_zero_sum_le_logDeriv χ hprim hne ∅ (by simp) (σ := 2) (by norm_num)
      le_rfl

end TauCeti.LFunctions
