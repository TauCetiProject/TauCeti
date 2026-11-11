/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Basic
public import TauCeti.Analysis.Meromorphic.Divisor
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic

/-!
# Zeros of primitive Dirichlet entire completions

Let `χ` be a nonprincipal primitive Dirichlet character and `Λ₀(χ)` the entire completion of its
analytic record. This file locates the zeros of `Λ₀(χ)` in the open critical strip and records
the symmetries of their multiplicities.

* `Λ₀(χ)` has no zeros on `1 ≤ Re s`, by the nonvanishing of `L(χ, s)` there, and none on
  `Re s ≤ 0`, by the functional equation against `χ⁻¹`.
* Specializing the order symmetries of `Completion/Basic.lean` through
  `dirichletData_dual`: `ord_{1 - s} Λ₀(χ) = ord_s Λ₀(χ⁻¹)` and
  `ord_{conj s} Λ₀(χ⁻¹) = ord_s Λ₀(χ)`. Hence `ρ ↦ 1 - conj ρ` preserves the zero orders of
  `Λ₀(χ)`, and for a real character the orders are invariant under `conj` and under `s ↦ 1 - s`
  separately.
* For a zero `ρ` and `1 ≤ Re s`, the summand `Re (1 / (s - ρ))` of the partial-fraction
  expansion of `Λ₀'/Λ₀` is positive.

These are the edge statements of the zero-free region at `K = ℚ` and the zero-location input to
the positivity of the sum over zeros in the Hadamard corollaries.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2 and §11.1.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §12 and §14.
-/

public section

open Complex ComplexConjugate

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- A nonprincipal primitive Dirichlet entire completion has no zeros on `1 ≤ Re s`. -/
theorem dirichletData_entireCompletion_ne_zero_of_one_le_re (hne : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) : (dirichletData χ hχ).entireCompletion s ≠ 0 := by
  rw [dirichletData_entireCompletion_of_ne_one χ hχ hne, dirichletData_completed]
  exact mul_ne_zero (by simp [NeZero.ne N])
    (DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (.inl hne) hs)

/-- A nonprincipal primitive Dirichlet entire completion has no zeros on `Re s ≤ 0`. -/
theorem dirichletData_entireCompletion_ne_zero_of_re_nonpos (hne : χ ≠ 1) {s : ℂ}
    (hs : s.re ≤ 0) : (dirichletData χ hχ).entireCompletion s ≠ 0 := by
  rw [← sub_sub_cancel 1 s, dirichletData_entireCompletion_one_sub χ hχ hne]
  refine mul_ne_zero (DirichletCharacter.rootNumber_ne_zero hχ) ?_
  exact dirichletData_entireCompletion_ne_zero_of_one_le_re χ⁻¹ hχ.inv (inv_ne_one.mpr hne)
    (by simp only [sub_re, one_re]; linarith)

/-- Every zero of a nonprincipal primitive Dirichlet entire completion lies in the open
critical strip. -/
theorem re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero (hne : χ ≠ 1) {ρ : ℂ}
    (hρ : (dirichletData χ hχ).entireCompletion ρ = 0) : ρ.re ∈ Set.Ioo 0 1 := by
  by_contra h
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at h
  rcases h with h | h
  · exact dirichletData_entireCompletion_ne_zero_of_re_nonpos χ hχ hne h hρ
  · exact dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne h hρ

/-- The divisor form of the zero location: a point of positive divisor of a nonprincipal
primitive Dirichlet entire completion lies in the open critical strip. -/
theorem re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos (hne : χ ≠ 1) {ρ : ℂ}
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    ρ.re ∈ Set.Ioo 0 1 := by
  have h := dirichletData_hasMeromorphicContinuation χ hχ
  refine re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hne ?_
  by_contra h0
  rw [MeromorphicOn.divisor_eq_analyticOrderNatAt h.meromorphicOn_entireCompletion
    (h.analyticAt_entireCompletion ρ) (Set.mem_univ ρ), analyticOrderNatAt,
    (h.analyticAt_entireCompletion ρ).analyticOrderAt_eq_zero.mpr h0] at hρ
  simp at hρ

/-- For a zero `ρ` of a nonprincipal primitive Dirichlet entire completion and `1 ≤ Re s`,
the summand `Re (1 / (s - ρ))` is positive. -/
theorem re_one_div_sub_pos_of_dirichletData_entireCompletion_eq_zero (hne : χ ≠ 1) {ρ s : ℂ}
    (hρ : (dirichletData χ hχ).entireCompletion ρ = 0) (hs : 1 ≤ s.re) :
    0 < (1 / (s - ρ)).re := by
  rw [one_div, Complex.inv_re_pos, sub_re, sub_pos]
  exact (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hne hρ).2.trans_le hs

/-! ### Symmetries of the zero orders -/

/-- The functional equation transports zero orders from `Λ₀(χ⁻¹)` at `s` to `Λ₀(χ)` at
`1 - s`. -/
theorem analyticOrderAt_dirichletData_entireCompletion_one_sub (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion (1 - s) =
      analyticOrderAt (dirichletData χ⁻¹ hχ.inv).entireCompletion s := by
  have h := dirichletData_hasMeromorphicContinuation χ hχ
  have hm := (dirichletData_hasFunctionalEquation χ hχ).meromorphicOrderAt_entireCompletion_one_sub
    h s
  rw [(h.analyticAt_entireCompletion _).meromorphicOrderAt_eq,
    (h.dual.analyticAt_entireCompletion _).meromorphicOrderAt_eq, dirichletData_dual] at hm
  exact ENat.map_natCast_injective hm

/-- Reflection across the real axis transports zero orders from `Λ₀(χ)` at `s` to `Λ₀(χ⁻¹)`
at `conj s`. -/
theorem analyticOrderAt_dirichletData_inv_entireCompletion_conj (s : ℂ) :
    analyticOrderAt (dirichletData χ⁻¹ hχ.inv).entireCompletion (conj s) =
      analyticOrderAt (dirichletData χ hχ).entireCompletion s := by
  have h := dirichletData_hasMeromorphicContinuation χ hχ
  have hm := h.meromorphicOrderAt_dual_entireCompletion_conj s
  rw [(h.analyticAt_entireCompletion _).meromorphicOrderAt_eq,
    (h.dual.analyticAt_entireCompletion _).meromorphicOrderAt_eq, dirichletData_dual] at hm
  exact ENat.map_natCast_injective hm

/-- The composite `ρ ↦ 1 - conj ρ` preserves the zero orders of a primitive Dirichlet entire
completion. -/
theorem analyticOrderAt_dirichletData_entireCompletion_one_sub_conj (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion (1 - conj s) =
      analyticOrderAt (dirichletData χ hχ).entireCompletion s := by
  rw [analyticOrderAt_dirichletData_entireCompletion_one_sub χ hχ,
    analyticOrderAt_dirichletData_inv_entireCompletion_conj χ hχ]

/-- For a real character, conjugation preserves the zero orders of the entire completion. -/
theorem analyticOrderAt_dirichletData_entireCompletion_conj_of_inv_eq (hreal : χ⁻¹ = χ)
    (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion (conj s) =
      analyticOrderAt (dirichletData χ hχ).entireCompletion s := by
  simpa only [dirichletData_inv_of_inv_eq χ hχ hreal] using
    analyticOrderAt_dirichletData_inv_entireCompletion_conj χ hχ s

/-- For a real character, the reflection `s ↦ 1 - s` preserves the zero orders of the entire
completion. -/
theorem analyticOrderAt_dirichletData_entireCompletion_one_sub_of_inv_eq (hreal : χ⁻¹ = χ)
    (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion (1 - s) =
      analyticOrderAt (dirichletData χ hχ).entireCompletion s := by
  simpa only [dirichletData_inv_of_inv_eq χ hχ hreal] using
    analyticOrderAt_dirichletData_entireCompletion_one_sub χ hχ s

/-! ### Divisor forms -/

/-- The divisor form of `analyticOrderAt_dirichletData_entireCompletion_one_sub`. -/
theorem divisor_dirichletData_entireCompletion_one_sub (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ (1 - s) =
      MeromorphicOn.divisor (dirichletData χ⁻¹ hχ.inv).entireCompletion Set.univ s := by
  simpa only [dirichletData_dual] using
    (dirichletData_hasFunctionalEquation χ hχ).divisor_entireCompletion_one_sub
      (dirichletData_hasMeromorphicContinuation χ hχ) s

/-- The divisor form of `analyticOrderAt_dirichletData_inv_entireCompletion_conj`. -/
theorem divisor_dirichletData_inv_entireCompletion_conj (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ⁻¹ hχ.inv).entireCompletion Set.univ (conj s) =
      MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s := by
  simpa only [dirichletData_dual] using
    (dirichletData_hasMeromorphicContinuation χ hχ).divisor_dual_entireCompletion_conj s

/-- The divisor form of `analyticOrderAt_dirichletData_entireCompletion_conj_of_inv_eq`. -/
theorem divisor_dirichletData_entireCompletion_conj_of_inv_eq (hreal : χ⁻¹ = χ) (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ (conj s) =
      MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s := by
  simpa only [dirichletData_inv_of_inv_eq χ hχ hreal] using
    divisor_dirichletData_inv_entireCompletion_conj χ hχ s

/-- The divisor form of `analyticOrderAt_dirichletData_entireCompletion_one_sub_of_inv_eq`. -/
theorem divisor_dirichletData_entireCompletion_one_sub_of_inv_eq (hreal : χ⁻¹ = χ) (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ (1 - s) =
      MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s := by
  simpa only [dirichletData_inv_of_inv_eq χ hχ hreal] using
    divisor_dirichletData_entireCompletion_one_sub χ hχ s

end TauCeti.LFunctions
