/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.RealPart
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.LogDeriv
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros

/-!
# Hadamard expansion of primitive Dirichlet entire completions

Let `χ` be a nonprincipal primitive Dirichlet character and `Λ₀ = Λ₀(χ)` the entire completion
of its analytic record, with zero multiplicities `m_ρ` read from the divisor of `Λ₀` on `ℂ`.
Since `Λ₀` is entire of order at most one and `Λ₀(0) ≠ 0`, Hadamard's theorem gives, off the
zeros,

  `Λ₀'/Λ₀ (s) = B(χ) + ∑_ρ m_ρ (1 / (s - ρ) + 1 / ρ)`,   `B(χ) = Λ₀'/Λ₀ (0)`,

absolutely and locally uniformly. Because every zero lies in `0 < Re ρ < 1`, the real parts
`m_ρ Re (1 / ρ)` and `m_ρ Re (1 / (s - ρ))` are separately summable, the latter at every `s` off
the zeros, and for `1 ≤ Re s` every summand `m_ρ Re (1 / (s - ρ))` is nonnegative.

The functional equation against `χ⁻¹` and conjugation give
`Λ₀'/Λ₀ (1 - conj s) = -conj (Λ₀'/Λ₀ (s))`, and `ρ ↦ 1 - conj ρ` permutes the zeros with their
multiplicities. The general real-part identity of `TauCeti.OrderLE.re_logDeriv_zero_eq_neg_tsum`
therefore yields

  `Re B(χ) = -∑_ρ m_ρ Re (1 / ρ)`,

so `Re (Λ₀'/Λ₀ (s)) = ∑_ρ m_ρ Re (1 / (s - ρ))` off the zeros. Reality of `χ` is not used.

## Main results

* `TauCeti.LFunctions.logDeriv_dirichletData_entireCompletion_eq_add_tsum`,
  `summable_norm_divisor_dirichletData_entireCompletion_mul_one_div_sub_add_one_div` and
  `TauCeti.LFunctions.hasSumLocallyUniformlyOn_logDeriv_dirichletData_entireCompletion_sub`:
  the partial-fraction expansion.
* `TauCeti.LFunctions.re_logDeriv_dirichletData_entireCompletion_zero`: the real-part identity
  `Re B(χ) = -∑_ρ m_ρ Re (1 / ρ)`.
* `TauCeti.LFunctions.re_logDeriv_dirichletData_entireCompletion_eq_tsum` and
  `TauCeti.LFunctions.tsum_divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg`:
  the real part of `Λ₀'/Λ₀` as a sum over zeros, nonnegative for `1 ≤ Re s`, with each summand at
  a zero positive there
  (`TauCeti.LFunctions.divisor_dirichletData_entireCompletion_mul_re_one_div_sub_pos`).

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), Theorem 10.16 and
  Corollary 10.18, (10.37)–(10.38).
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 12.
-/

public section

open Complex ComplexConjugate

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- **Partial fractions.** Off its zeros, the logarithmic derivative of a nonprincipal primitive
Dirichlet entire completion is `B(χ) + ∑_ρ m_ρ (1 / (s - ρ) + 1 / ρ)` with `B(χ) = Λ₀'/Λ₀ (0)`. -/
theorem logDeriv_dirichletData_entireCompletion_eq_add_tsum (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    logDeriv (dirichletData χ hχ).entireCompletion s =
      logDeriv (dirichletData χ hχ).entireCompletion 0 +
        ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
          ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
            (1 / (s - ρ) + 1 / ρ) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).logDeriv_eq_add_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne) hs

/-- The partial-fraction series of a nonprincipal primitive Dirichlet entire completion converges
absolutely off its zeros. -/
theorem summable_norm_divisor_dirichletData_entireCompletion_mul_one_div_sub_add_one_div
    (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    Summable (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion
        Set.univ).support ↦
      ‖((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
        (1 / (s - ρ) + 1 / ρ)‖) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ
    hne).summable_norm_divisor_mul_one_div_sub_add_one_div
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne) (by norm_num) hs

/-- The partial-fraction series of a nonprincipal primitive Dirichlet entire completion converges
locally uniformly off its zeros to `Λ₀'/Λ₀ - B(χ)`. -/
theorem hasSumLocallyUniformlyOn_logDeriv_dirichletData_entireCompletion_sub (hne : χ ≠ 1) :
    HasSumLocallyUniformlyOn
      (fun (ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support)
          s ↦
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
          (1 / (s - ρ) + 1 / ρ))
      (fun s ↦ logDeriv (dirichletData χ hχ).entireCompletion s -
        logDeriv (dirichletData χ hχ).entireCompletion 0)
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support)ᶜ :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).hasSumLocallyUniformlyOn_logDeriv_sub
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)

/-! ### Real parts of the sum over zeros -/

/-- Every zero of `Λ₀` has `0 ≤ Re ρ`, the zero-location hypothesis of the general real-part
lemmas. -/
private theorem re_nonneg_of_divisor_dirichletData_entireCompletion_pos (hne : χ ≠ 1) (ρ : ℂ)
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    0 ≤ ρ.re :=
  (re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hne hρ).1.le

/-- Every zero of `Λ₀` has `|Re ρ| ≤ 1`. -/
private theorem abs_re_le_one_of_divisor_dirichletData_entireCompletion_pos (hne : χ ≠ 1) (ρ : ℂ)
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    |ρ.re| ≤ 1 :=
  have h := re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hne hρ
  abs_le.mpr ⟨by linarith [h.1], h.2.le⟩

/-- The real parts `m_ρ Re (1 / ρ)` over the zeros form a summable family. -/
theorem summable_divisor_dirichletData_entireCompletion_mul_re_one_div (hne : χ ≠ 1) :
    Summable (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion
        Set.univ).support ↦
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (ρ : ℂ)).re) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).summable_divisor_mul_re_one_div
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (by norm_num) (abs_re_le_one_of_divisor_dirichletData_entireCompletion_pos χ hχ hne)

/-- Off the zeros, the real parts `m_ρ Re (1 / (s - ρ))` form a summable family. The complex
terms `m_ρ / (s - ρ)` are not absolutely summable. -/
theorem summable_divisor_dirichletData_entireCompletion_mul_re_one_div_sub (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    Summable (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion
        Set.univ).support ↦
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (s - ρ)).re) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).summable_divisor_mul_re_one_div_sub
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne) (by norm_num)
    (abs_re_le_one_of_divisor_dirichletData_entireCompletion_pos χ hχ hne) hs

/-- **The real part of `B(χ)`.** For a nonprincipal primitive character,
`Re B(χ) = -∑_ρ m_ρ Re (1 / ρ)`, where `B(χ) = Λ₀'/Λ₀ (0)`. Reality of `χ` is not used. -/
theorem re_logDeriv_dirichletData_entireCompletion_zero (hne : χ ≠ 1) :
    (logDeriv (dirichletData χ hχ).entireCompletion 0).re =
      -∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (ρ : ℂ)).re :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).re_logDeriv_zero_eq_neg_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)
    ((dirichletData_hasFunctionalEquation χ hχ).divisor_entireCompletion_one_sub_conj
      (dirichletData_hasMeromorphicContinuation χ hχ))
    (logDeriv_dirichletData_entireCompletion_one_sub_conj χ hχ hne)
    (re_nonneg_of_divisor_dirichletData_entireCompletion_pos χ hχ hne)

/-- **The real part of `Λ₀'/Λ₀` as a sum over zeros.** Off the zeros,
`Re (Λ₀'/Λ₀ (s)) = ∑_ρ m_ρ Re (1 / (s - ρ))`. -/
theorem re_logDeriv_dirichletData_entireCompletion_eq_tsum (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    (logDeriv (dirichletData χ hχ).entireCompletion s).re =
      ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).re_logDeriv_eq_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)
    ((dirichletData_hasFunctionalEquation χ hχ).divisor_entireCompletion_one_sub_conj
      (dirichletData_hasMeromorphicContinuation χ hχ))
    (logDeriv_dirichletData_entireCompletion_one_sub_conj χ hχ hne)
    (re_nonneg_of_divisor_dirichletData_entireCompletion_pos χ hχ hne) hs

/-- For `1 ≤ Re s`, each weighted summand `m_ρ Re (1 / (s - ρ))` is nonnegative. -/
theorem divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg (hne : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) (ρ : ℂ) :
    0 ≤ ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
      (1 / (s - ρ)).re :=
  divisor_mul_re_one_div_sub_nonneg fun hρ ↦
    (re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hne hρ).2.le.trans hs

/-- For `1 ≤ Re s`, the weighted summand `m_ρ Re (1 / (s - ρ))` at a zero `ρ` is positive, since
`Re ρ < 1 ≤ Re s`. -/
theorem divisor_dirichletData_entireCompletion_mul_re_one_div_sub_pos (hne : χ ≠ 1) {s ρ : ℂ}
    (hs : 1 ≤ s.re)
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    0 < ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
      (1 / (s - ρ)).re :=
  divisor_mul_re_one_div_sub_pos hρ
    ((re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hne hρ).2.trans_le hs)

/-- **Positivity of the sum over zeros.** For `1 ≤ Re s`, `0 ≤ ∑_ρ m_ρ Re (1 / (s - ρ))`, an
absolutely convergent sum of nonnegative terms. -/
theorem tsum_divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg (hne : χ ≠ 1)
    {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (s - ρ)).re :=
  tsum_nonneg fun ρ ↦
    divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg χ hχ hne hs ρ

/-- For `1 ≤ Re s`, the real part of `Λ₀'/Λ₀ (s)` is nonnegative. -/
theorem re_logDeriv_dirichletData_entireCompletion_nonneg (hne : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) : 0 ≤ (logDeriv (dirichletData χ hχ).entireCompletion s).re := by
  rw [re_logDeriv_dirichletData_entireCompletion_eq_tsum χ hχ hne
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne hs)]
  exact tsum_divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg χ hχ hne hs

end TauCeti.LFunctions
