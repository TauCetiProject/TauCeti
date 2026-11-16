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
# Hadamard factorization and real-part partial fractions for primitive Dirichlet completions

Let `χ` be a nonprincipal primitive Dirichlet character of conductor `N`, and write
`Λ₀(χ) = (dirichletData χ hχ).entireCompletion`. Because `Λ₀(χ)` is entire of order at most one
and nonzero at `0` and `1`, Hadamard's factorization writes
`Λ₀(χ)(s) = exp (A(χ) + B(χ) s) ∏_ρ E₁(s / ρ) ^ m_ρ` with `B(χ) = logDeriv Λ₀(χ) 0`.

Combining the functional equation `logDeriv Λ₀(χ) (1 - s) = -logDeriv Λ₀(χ⁻¹) s` with the
conjugation symmetry `logDeriv Λ₀(χ⁻¹) (conj s) = conj (logDeriv Λ₀(χ) s)` at `s = 1` gives
`(logDeriv Λ₀(χ) 1).re = -(logDeriv Λ₀(χ) 0).re` for every nonprincipal primitive character `χ`,
real or complex. Since the zeros of `Λ₀(χ)` lie in `0 < Re ρ < 1` and have multiplicities
invariant under `ρ ↦ 1 - conj ρ`, `TauCeti.OrderLE.re_logDeriv_zero_eq_neg_tsum` and
`TauCeti.OrderLE.re_logDeriv_eq_tsum` give Montgomery–Vaughan's Corollary 10.18:
`Re B(χ) = -∑_ρ m_ρ Re (1 / ρ)` and, at every `s` off the zeros,
`Re (logDeriv Λ₀(χ) s) = ∑_ρ m_ρ Re (1 / (s - ρ))`.

On the closed half-plane `1 ≤ Re s`, `Λ₀(χ)` has no zeros and every summand `m_ρ Re (1 / (s - ρ))`
is nonnegative, so `0 ≤ Re (logDeriv Λ₀(χ) s)` and every finite partial sum of zero terms bounds
`Re (logDeriv Λ₀(χ) s)` from below. Finally, `divisor_toNat_dirichletData_entireCompletion_eq`
identifies the completion multiplicities `(divisor Λ₀(χ) univ ρ).toNat` with
`analyticOrderNatAt χ.LFunction ρ` on `0 < Re ρ` and `0` on `Re ρ ≤ 0`, eliminating trivial zeros
at the completion boundary.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), Theorem 10.16 and
  Corollary 10.18, pp. 351–353.
-/

public section

open Complex ComplexConjugate
open scoped BigOperators

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- The entire completion of a primitive Dirichlet record is differentiable on `ℂ`. -/
theorem differentiable_dirichletData_entireCompletion :
    Differentiable ℂ (dirichletData χ hχ).entireCompletion := fun s ↦
  ((dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion s).differentiableAt

/-- The entire completion of a nonprincipal primitive Dirichlet record has order at most one. -/
theorem dirichletData_entireCompletion_orderLE_one (hne : χ ≠ 1) :
    OrderLE (dirichletData χ hχ).entireCompletion 1 := by
  rw [dirichletData_entireCompletion_of_ne_one χ hχ hne]
  exact dirichletData_completed_orderLE_one χ hχ hne

/-- The whole-plane divisor of a primitive Dirichlet entire completion is invariant under
`ρ ↦ 1 - conj ρ`. -/
theorem divisor_dirichletData_entireCompletion_one_sub_conj (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ (1 - conj s) =
      MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s := by
  rw [divisor_dirichletData_entireCompletion_one_sub χ hχ,
    divisor_dirichletData_inv_entireCompletion_conj χ hχ]

/-- Every point in the divisor support of a nonprincipal primitive Dirichlet entire completion
lies in the open critical strip `0 < Re ρ < 1`. -/
theorem re_mem_Ioo_of_mem_divisor_support_dirichletData_entireCompletion (hne : χ ≠ 1) {ρ : ℂ}
    (hρ : ρ ∈ (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support) :
    ρ.re ∈ Set.Ioo 0 1 := by
  have hfa : AnalyticOnNhd ℂ (dirichletData χ hχ).entireCompletion Set.univ :=
    fun z _ ↦ (dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion z
  have hnonneg := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa ρ
  exact re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hne
    (lt_of_le_of_ne hnonneg (Function.mem_support.mp hρ).symm)

/-- For any nonprincipal primitive character (real or complex), the real parts of
`logDeriv Λ₀(χ)` at `1` and `0` are negatives of each other. -/
theorem re_logDeriv_dirichletData_entireCompletion_one (hne : χ ≠ 1) :
    (logDeriv (dirichletData χ hχ).entireCompletion 1).re =
      -(logDeriv (dirichletData χ hχ).entireCompletion 0).re := by
  have h01 := logDeriv_dirichletData_entireCompletion_one_sub χ hχ hne 1
  rw [sub_self] at h01
  have hconj := logDeriv_dirichletData_entireCompletion_inv_conj χ hχ hne 1
  rw [map_one] at hconj
  rw [hconj] at h01
  have hre := congrArg re h01
  simp only [neg_re, conj_re] at hre
  linarith

/-- **Hadamard factorization for a primitive Dirichlet entire completion.** -/
theorem exists_dirichletData_entireCompletion_eq_cexp_mul_divisorProductOne (hne : χ ≠ 1) :
    ∃ a : ℂ, exp a = (dirichletData χ hχ).entireCompletion 0 ∧
      ∀ s, (dirichletData χ hχ).entireCompletion s =
        exp (a + logDeriv (dirichletData χ hχ).entireCompletion 0 * s) *
          divisorProductOne (dirichletData χ hχ).entireCompletion s :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).exists_eq_cexp_mul_divisorProductOne
    (differentiable_dirichletData_entireCompletion χ hχ)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)

/-- Off its zeros, the logarithmic derivative of a nonprincipal primitive Dirichlet entire
completion has the paired partial-fraction expansion
`logDeriv Λ₀(χ) s = logDeriv Λ₀(χ) 0 + ∑ m_ρ (1 / (s - ρ) + 1 / ρ)`. -/
theorem logDeriv_dirichletData_entireCompletion_eq_add_tsum (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    logDeriv (dirichletData χ hχ).entireCompletion s =
      logDeriv (dirichletData χ hχ).entireCompletion 0 +
        ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
          ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
            (1 / (s - ρ) + 1 / ρ) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).logDeriv_eq_add_tsum
    (differentiable_dirichletData_entireCompletion χ hχ)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne) hs

/-- The unpaired real-part series `∑ m_ρ Re (1 / ρ)` of a nonprincipal primitive Dirichlet entire
completion is summable over `ℂ`. -/
theorem summable_divisor_dirichletData_entireCompletion_mul_re_one_div (hne : χ ≠ 1) :
    Summable (fun ρ : ℂ ↦
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / ρ).re) := by
  refine (dirichletData_entireCompletion_orderLE_one χ hχ hne).summable_divisor_mul_re_one_div
    (differentiable_dirichletData_entireCompletion χ hχ) (by norm_num) (B := 1) fun ρ hρ ↦ ?_
  have hmem := re_mem_Ioo_of_mem_divisor_support_dirichletData_entireCompletion χ hχ hne hρ
  exact abs_le.mpr ⟨by linarith [hmem.1], hmem.2.le⟩

/-- The unpaired real-part series `∑ m_ρ Re (1 / (s - ρ))` of a nonprincipal primitive Dirichlet
entire completion is summable over `ℂ` at every `s : ℂ`. -/
theorem summable_divisor_dirichletData_entireCompletion_mul_re_one_div_sub (hne : χ ≠ 1) (s : ℂ) :
    Summable (fun ρ : ℂ ↦
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (s - ρ)).re) := by
  refine (dirichletData_entireCompletion_orderLE_one χ hχ hne).summable_divisor_mul_re_one_div_sub
    (differentiable_dirichletData_entireCompletion χ hχ) (by norm_num) (B := 1) (fun ρ hρ ↦ ?_) s
  have hmem := re_mem_Ioo_of_mem_divisor_support_dirichletData_entireCompletion χ hχ hne hρ
  exact abs_le.mpr ⟨by linarith [hmem.1], hmem.2.le⟩

/-- **Real part of the Hadamard constant `B(χ)`** (Montgomery–Vaughan, Corollary 10.18). For any
nonprincipal primitive Dirichlet character `χ`, real or complex,
`Re (logDeriv Λ₀(χ) 0) = -∑_ρ m_ρ Re (1 / ρ)`. -/
theorem re_logDeriv_dirichletData_entireCompletion_zero (hne : χ ≠ 1) :
    (logDeriv (dirichletData χ hχ).entireCompletion 0).re =
      -∑' ρ : ℂ,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / ρ).re := by
  refine (dirichletData_entireCompletion_orderLE_one χ hχ hne).re_logDeriv_zero_eq_neg_tsum
    (differentiable_dirichletData_entireCompletion χ hχ)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne) (c := 1) (B := 1)
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne (by simp))
    (fun ρ hρ ↦
      (re_mem_Ioo_of_mem_divisor_support_dirichletData_entireCompletion χ hχ hne hρ).2.le)
    (fun ρ ↦ by
      simpa using divisor_dirichletData_entireCompletion_one_sub_conj χ hχ ρ)
    (by simpa using re_logDeriv_dirichletData_entireCompletion_one χ hχ hne)

/-- **Unpaired real-part partial fractions for `Λ₀(χ)`** (Montgomery–Vaughan, Corollary 10.18).
At every `s : ℂ` where `Λ₀(χ) s ≠ 0`, `Re (logDeriv Λ₀(χ) s) = ∑_ρ m_ρ Re (1 / (s - ρ))`. -/
theorem re_logDeriv_dirichletData_entireCompletion (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    (logDeriv (dirichletData χ hχ).entireCompletion s).re =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re := by
  refine (dirichletData_entireCompletion_orderLE_one χ hχ hne).re_logDeriv_eq_tsum
    (differentiable_dirichletData_entireCompletion χ hχ)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne) (c := 1) (B := 1)
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne (by simp))
    (fun ρ hρ ↦
      (re_mem_Ioo_of_mem_divisor_support_dirichletData_entireCompletion χ hχ hne hρ).2.le)
    (fun ρ ↦ by
      simpa using divisor_dirichletData_entireCompletion_one_sub_conj χ hχ ρ)
    (by simpa using re_logDeriv_dirichletData_entireCompletion_one χ hχ hne) hs

/-- On `1 ≤ Re s`, `Λ₀(χ)` has no zeros and
`Re (logDeriv Λ₀(χ) s) = ∑_ρ m_ρ Re (1 / (s - ρ))`. -/
theorem re_logDeriv_dirichletData_entireCompletion_of_one_le_re (hne : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) :
    (logDeriv (dirichletData χ hχ).entireCompletion s).re =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re :=
  re_logDeriv_dirichletData_entireCompletion χ hχ hne
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne hs)

/-- On `1 ≤ Re s`, every finite partial sum of zero terms bounds `Re (logDeriv Λ₀(χ) s)` from
below. -/
theorem sum_divisor_mul_re_one_div_sub_le_re_logDeriv_dirichletData_entireCompletion
    (hne : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) (S : Finset ℂ) :
    (∑ ρ ∈ S,
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (s - ρ)).re) ≤
      (logDeriv (dirichletData χ hχ).entireCompletion s).re := by
  have hor := dirichletData_entireCompletion_orderLE_one χ hχ hne
  refine hor.sum_divisor_mul_re_one_div_sub_le_re_logDeriv
    (differentiable_dirichletData_entireCompletion χ hχ)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne) (c := 1) (B := 1)
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne (by simp))
    (fun ρ hρ ↦
      (re_mem_Ioo_of_mem_divisor_support_dirichletData_entireCompletion χ hχ hne hρ).2.le)
    (fun ρ ↦ by
      simpa using divisor_dirichletData_entireCompletion_one_sub_conj χ hχ ρ)
    (by simpa using re_logDeriv_dirichletData_entireCompletion_one χ hχ hne)
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne hs) hs S

/-- On `1 ≤ Re s`, `Re (logDeriv Λ₀(χ) s)` is nonnegative. -/
theorem re_logDeriv_dirichletData_entireCompletion_nonneg_of_one_le_re (hne : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) :
    0 ≤ (logDeriv (dirichletData χ hχ).entireCompletion s).re := by
  simpa using
    sum_divisor_mul_re_one_div_sub_le_re_logDeriv_dirichletData_entireCompletion χ hχ hne hs ∅

/-- At every point `ρ : ℂ`, the natural divisor multiplicity of `Λ₀(χ)` equals
`analyticOrderNatAt χ.LFunction ρ` on `0 < Re ρ` and vanishes on `Re ρ ≤ 0` (where the archimedean
poles cancel any trivial zeros of `L(χ, ·)`). -/
theorem divisor_toNat_dirichletData_entireCompletion_eq (hne : χ ≠ 1) (ρ : ℂ) :
    (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat =
      if 0 < ρ.re then analyticOrderNatAt χ.LFunction ρ else 0 := by
  have hm := dirichletData_hasMeromorphicContinuation χ hχ
  split_ifs with hρ
  · rw [MeromorphicOn.divisor_eq_analyticOrderNatAt hm.meromorphicOn_entireCompletion
      (hm.analyticAt_entireCompletion ρ) (Set.mem_univ ρ), Int.toNat_natCast,
      analyticOrderNatAt, analyticOrderNatAt,
      analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hρ]
  · have hne0 := dirichletData_entireCompletion_ne_zero_of_re_nonpos χ hχ hne (le_of_not_gt hρ)
    rw [(hm.analyticAt_entireCompletion ρ).divisor_apply_eq_zero hne0]
    rfl

end TauCeti.LFunctions
