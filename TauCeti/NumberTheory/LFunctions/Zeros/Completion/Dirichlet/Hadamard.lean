/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
public import TauCeti.Analysis.Complex.Hadamard.OrderOne
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
multiplicities. Comparing the real parts of the expansions at `2` and at `1 - conj 2 = -1` yields

  `Re B(χ) = -∑_ρ m_ρ Re (1 / ρ)`,

so `Re (Λ₀'/Λ₀ (s)) = ∑_ρ m_ρ Re (1 / (s - ρ))` off the zeros. Reality of `χ` is not used.

## Main results

* `TauCeti.LFunctions.dirichletData_entireCompletion_orderLE_one`: `Λ₀` has order at most one.
* `TauCeti.LFunctions.logDeriv_dirichletData_entireCompletion_eq_add_tsum`,
  `TauCeti.LFunctions.summable_norm_dirichletData_entireCompletion_partialFraction` and
  `TauCeti.LFunctions.hasSumLocallyUniformlyOn_logDeriv_dirichletData_entireCompletion_sub`:
  the partial-fraction expansion.
* `TauCeti.LFunctions.re_logDeriv_dirichletData_entireCompletion_zero`: the real-part identity
  `Re B(χ) = -∑_ρ m_ρ Re (1 / ρ)`.
* `TauCeti.LFunctions.re_logDeriv_dirichletData_entireCompletion_eq_tsum` and
  `TauCeti.LFunctions.tsum_divisor_mul_re_one_div_sub_dirichletData_entireCompletion_nonneg`:
  the real part of `Λ₀'/Λ₀` as a sum over zeros, nonnegative for `1 ≤ Re s`, with each summand at
  a zero positive there
  (`TauCeti.LFunctions.divisor_mul_re_one_div_sub_dirichletData_entireCompletion_pos`).

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), Theorem 10.16 and
  Corollary 10.18, (10.37)–(10.38).
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 12.
-/

public section

open Complex ComplexConjugate

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- The entire completion of a nonprincipal primitive Dirichlet record has order at most one. -/
theorem dirichletData_entireCompletion_orderLE_one (hne : χ ≠ 1) :
    OrderLE (dirichletData χ hχ).entireCompletion 1 := by
  rw [dirichletData_entireCompletion_of_ne_one χ hχ hne]
  exact dirichletData_completed_orderLE_one χ hχ hne

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
theorem summable_norm_dirichletData_entireCompletion_partialFraction (hne : χ ≠ 1) {s : ℂ}
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

/-- The weighted summand `m_ρ Re (1 / ρ)` lies between `0` and `m_ρ ‖ρ⁻¹‖ ^ 2`. -/
theorem divisor_mul_re_one_div_mem_Icc_dirichletData_entireCompletion (hne : χ ≠ 1) (ρ : ℂ) :
    ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / ρ).re ∈ Set.Icc 0
      (((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        ‖ρ⁻¹‖ ^ 2) := by
  set m := (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  have hρ := re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hne
    (Int.pos_iff_toNat_pos.mpr hm)
  have hn : 0 ≤ normSq ρ := normSq_nonneg ρ
  rw [one_div, inv_re, norm_inv, inv_pow, Complex.sq_norm, ← one_div]
  exact ⟨by have := hρ.1.le; positivity,
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hρ.2.le hn) (by positivity)⟩

/-- The real parts `m_ρ Re (1 / ρ)` over the zeros form a summable family. -/
theorem summable_divisor_mul_re_one_div_dirichletData_entireCompletion (hne : χ ≠ 1) :
    Summable (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion
        Set.univ).support ↦
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (ρ : ℂ)).re) :=
  ((dirichletData_entireCompletion_orderLE_one χ hχ hne).summable_divisor_toNat_mul_norm_inv_sq
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (by norm_num)).of_nonneg_of_le
    (fun ρ ↦ (divisor_mul_re_one_div_mem_Icc_dirichletData_entireCompletion χ hχ hne ρ).1)
    (fun ρ ↦ (divisor_mul_re_one_div_mem_Icc_dirichletData_entireCompletion χ hχ hne ρ).2)

/-- Off the zeros, the real parts `m_ρ Re (1 / (s - ρ))` form a summable family. The complex
terms `m_ρ / (s - ρ)` are not absolutely summable. -/
theorem summable_divisor_mul_re_one_div_sub_dirichletData_entireCompletion (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    Summable (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion
        Set.univ).support ↦
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (s - ρ)).re) := by
  refine (((summable_norm_dirichletData_entireCompletion_partialFraction χ hχ hne
    hs).of_norm.mapL reCLM).sub
    (summable_divisor_mul_re_one_div_dirichletData_entireCompletion χ hχ hne)).congr fun ρ ↦ ?_
  simp only [reCLM_apply, mul_re, natCast_re, natCast_im, add_re, zero_mul, sub_zero]
  ring

/-- The real part of the partial-fraction expansion, with the two sums taken separately. -/
theorem re_logDeriv_dirichletData_entireCompletion_eq_add_tsum (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    (logDeriv (dirichletData χ hχ).entireCompletion s).re =
      (logDeriv (dirichletData χ hχ).entireCompletion 0).re +
        ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
          ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
            (1 / (s - ρ)).re +
        ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
          ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
            (1 / (ρ : ℂ)).re := by
  rw [logDeriv_dirichletData_entireCompletion_eq_add_tsum χ hχ hne hs, add_re,
    re_tsum (summable_norm_dirichletData_entireCompletion_partialFraction χ hχ hne hs).of_norm,
    add_assoc, ← (summable_divisor_mul_re_one_div_sub_dirichletData_entireCompletion χ hχ hne
      hs).tsum_add (summable_divisor_mul_re_one_div_dirichletData_entireCompletion χ hχ hne)]
  congr 2
  funext ρ
  simp only [mul_re, natCast_re, natCast_im, add_re, zero_mul, sub_zero]
  ring

/-- The functional equation against `χ⁻¹` and conjugation together reflect the logarithmic
derivative across the critical line: `Λ₀'/Λ₀ (1 - conj s) = -conj (Λ₀'/Λ₀ (s))`. -/
theorem logDeriv_dirichletData_entireCompletion_one_sub_conj (hne : χ ≠ 1) (s : ℂ) :
    logDeriv (dirichletData χ hχ).entireCompletion (1 - conj s) =
      -conj (logDeriv (dirichletData χ hχ).entireCompletion s) := by
  rw [logDeriv_dirichletData_entireCompletion_one_sub χ hχ hne,
    logDeriv_dirichletData_entireCompletion_inv_conj χ hχ hne]

/-- The reflection `ρ ↦ 1 - conj ρ` preserves the divisor of a primitive Dirichlet entire
completion. -/
theorem divisor_dirichletData_entireCompletion_one_sub_conj (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ (1 - conj s) =
      MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s := by
  rw [divisor_dirichletData_entireCompletion_one_sub χ hχ,
    divisor_dirichletData_inv_entireCompletion_conj χ hχ]

/-- **The real part of `B(χ)`.** For a nonprincipal primitive character,
`Re B(χ) = -∑_ρ m_ρ Re (1 / ρ)`, where `B(χ) = Λ₀'/Λ₀ (0)`. Reality of `χ` is not used. -/
theorem re_logDeriv_dirichletData_entireCompletion_zero (hne : χ ≠ 1) :
    (logDeriv (dirichletData χ hχ).entireCompletion 0).re =
      -∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (ρ : ℂ)).re := by
  set d := MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ
  have h2 : (dirichletData χ hχ).entireCompletion 2 ≠ 0 :=
    dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne (by norm_num)
  have hm1 : (dirichletData χ hχ).entireCompletion (1 - conj 2) ≠ 0 :=
    dirichletData_entireCompletion_ne_zero_of_re_nonpos χ hχ hne (by norm_num)
  have hFE := congrArg re (logDeriv_dirichletData_entireCompletion_one_sub_conj χ hχ hne 2)
  rw [neg_re, conj_re, re_logDeriv_dirichletData_entireCompletion_eq_add_tsum χ hχ hne hm1,
    re_logDeriv_dirichletData_entireCompletion_eq_add_tsum χ hχ hne h2] at hFE
  -- Reindexing by `ρ ↦ 1 - conj ρ` turns the sum at `1 - conj 2` into minus the sum at `2`.
  have hdiv (s : ℂ) : d (1 - conj s) = d s :=
    divisor_dirichletData_entireCompletion_one_sub_conj χ hχ s
  let e : d.support ≃ d.support :=
    (Function.Involutive.toPerm (fun s : ℂ ↦ 1 - conj s) fun s ↦ by simp).subtypeEquiv
      fun s ↦ by
        change d s ≠ 0 ↔ d (1 - conj s) ≠ 0
        rw [hdiv]
  have hreflect : ∑' ρ : d.support, ((d ρ).toNat : ℝ) * (1 / (1 - conj 2 - (ρ : ℂ))).re =
      -∑' ρ : d.support, ((d ρ).toNat : ℝ) * (1 / (2 - (ρ : ℂ))).re := by
    rw [← e.tsum_eq, ← tsum_neg]
    congr 1
    funext ρ
    rw [show ((e ρ : d.support) : ℂ) = 1 - conj (ρ : ℂ) from rfl, hdiv, ← mul_neg,
      show (1 : ℂ) - conj 2 - (1 - conj (ρ : ℂ)) = -conj (2 - (ρ : ℂ)) by rw [map_sub]; ring,
      one_div, one_div, inv_neg, neg_re, ← map_inv₀, conj_re]
  linarith

/-- **The real part of `Λ₀'/Λ₀` as a sum over zeros.** Off the zeros,
`Re (Λ₀'/Λ₀ (s)) = ∑_ρ m_ρ Re (1 / (s - ρ))`. -/
theorem re_logDeriv_dirichletData_entireCompletion_eq_tsum (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    (logDeriv (dirichletData χ hχ).entireCompletion s).re =
      ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re := by
  rw [re_logDeriv_dirichletData_entireCompletion_eq_add_tsum χ hχ hne hs,
    re_logDeriv_dirichletData_entireCompletion_zero χ hχ hne]
  ring

/-- For `1 ≤ Re s`, each weighted summand `m_ρ Re (1 / (s - ρ))` is nonnegative. -/
theorem divisor_mul_re_one_div_sub_dirichletData_entireCompletion_nonneg (hne : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) (ρ : ℂ) :
    0 ≤ ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
      (1 / (s - ρ)).re := by
  set m := (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  have hρ := re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hne
    (Int.pos_iff_toNat_pos.mpr hm)
  refine mul_nonneg (Nat.cast_nonneg m) ?_
  rw [one_div, inv_re, sub_re]
  exact div_nonneg (by linarith [hρ.2]) (normSq_nonneg _)

/-- For `1 ≤ Re s`, the weighted summand `m_ρ Re (1 / (s - ρ))` at a zero `ρ` is positive, since
`Re ρ < 1 ≤ Re s`. -/
theorem divisor_mul_re_one_div_sub_dirichletData_entireCompletion_pos (hne : χ ≠ 1) {s ρ : ℂ}
    (hs : 1 ≤ s.re)
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    0 < ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
      (1 / (s - ρ)).re := by
  have hre := re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hne hρ
  have hsub : 0 < (s - ρ).re := by rw [sub_re]; linarith [hre.2]
  refine mul_pos (Nat.cast_pos.mpr (Int.pos_iff_toNat_pos.mp hρ)) ?_
  rw [one_div, inv_re]
  exact div_pos hsub (normSq_pos.mpr fun h ↦ by simp [h] at hsub)

/-- **Positivity of the sum over zeros.** For `1 ≤ Re s`, `0 ≤ ∑_ρ m_ρ Re (1 / (s - ρ))`, an
absolutely convergent sum of nonnegative terms. -/
theorem tsum_divisor_mul_re_one_div_sub_dirichletData_entireCompletion_nonneg (hne : χ ≠ 1)
    {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (s - ρ)).re :=
  tsum_nonneg fun ρ ↦
    divisor_mul_re_one_div_sub_dirichletData_entireCompletion_nonneg χ hχ hne hs ρ

/-- For `1 ≤ Re s`, the real part of `Λ₀'/Λ₀ (s)` is nonnegative. -/
theorem re_logDeriv_dirichletData_entireCompletion_nonneg (hne : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) : 0 ≤ (logDeriv (dirichletData χ hχ).entireCompletion s).re := by
  rw [re_logDeriv_dirichletData_entireCompletion_eq_tsum χ hχ hne
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne hs)]
  exact tsum_divisor_mul_re_one_div_sub_dirichletData_entireCompletion_nonneg χ hχ hne hs

end TauCeti.LFunctions
