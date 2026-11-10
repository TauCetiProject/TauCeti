/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet
public import TauCeti.Analysis.Meromorphic.Conj

/-!
# Zeros of primitive Dirichlet entire completions

Let `χ` be a nonprincipal primitive Dirichlet character and `Λ₀(χ)` the entire completion of its
analytic record. This file locates the zeros of `Λ₀(χ)` in the open critical strip and records
the symmetries of their multiplicities.

* `Λ₀(χ)` has no zeros on `1 ≤ Re s`, by the nonvanishing of `L(χ, s)` there, and none on
  `Re s ≤ 0`, by the functional equation against `χ⁻¹`.
* The functional equation `Λ₀(χ) s = ε(χ) Λ₀(χ⁻¹) (1 - s)` with `ε(χ) ≠ 0` gives
  `ord_{1 - s} Λ₀(χ) = ord_s Λ₀(χ⁻¹)`, and the reflection `Λ₀(χ⁻¹) = conj ∘ Λ₀(χ) ∘ conj` gives
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

/-- A point strictly to the right of `ρ` makes `Re (1 / (s - ρ))` positive. -/
theorem Complex.re_one_div_sub_pos {s ρ : ℂ} (h : ρ.re < s.re) : 0 < (1 / (s - ρ)).re := by
  have hre : 0 < (s - ρ).re := by simpa [sub_re] using h
  have hne : s - ρ ≠ 0 := fun h0 ↦ by simp [h0] at hre
  rw [one_div, inv_re]
  exact div_pos hre (normSq_pos.mpr hne)

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- The functional equation of a nonprincipal primitive Dirichlet entire completion,
against the entire completion of the inverse character. -/
theorem dirichletData_entireCompletion_one_sub (hne : χ ≠ 1) (s : ℂ) :
    (dirichletData χ hχ).entireCompletion s =
      χ.rootNumber * (dirichletData χ⁻¹ hχ.inv).entireCompletion (1 - s) := by
  have hp := dirichletData_polarOrder_eq_zero χ hχ hne
  rw [dirichletData_entireCompletion_of_ne_one χ hχ hne,
    dirichletData_entireCompletion_of_ne_one χ⁻¹ hχ.inv (inv_ne_one.mpr hne),
    (dirichletData_hasFunctionalEquation χ hχ).completed_eq s
      (by simp only [hp, Finsupp.zero_apply]) (by simp only [hp, Finsupp.zero_apply]),
    dirichletData_dual, dirichletData_rootNumber]

/-- The entire completion of the inverse character is the reflection of the entire completion
across the real axis. -/
theorem dirichletData_inv_entireCompletion (hne : χ ≠ 1) (s : ℂ) :
    (dirichletData χ⁻¹ hχ.inv).entireCompletion s =
      conj ((dirichletData χ hχ).entireCompletion (conj s)) := by
  rw [dirichletData_entireCompletion_of_ne_one χ hχ hne,
    dirichletData_entireCompletion_of_ne_one χ⁻¹ hχ.inv (inv_ne_one.mpr hne),
    ← dirichletData_dual, AnalyticLFunctionData.dual_completed_apply]

/-- A nonprincipal primitive Dirichlet entire completion has no zeros on `1 ≤ Re s`. -/
theorem dirichletData_entireCompletion_ne_zero_of_one_le_re (hne : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) : (dirichletData χ hχ).entireCompletion s ≠ 0 := by
  rw [dirichletData_entireCompletion_of_ne_one χ hχ hne, dirichletData_completed]
  exact mul_ne_zero (by simp [NeZero.ne N])
    (DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (.inl hne) hs)

/-- A nonprincipal primitive Dirichlet entire completion has no zeros on `Re s ≤ 0`. -/
theorem dirichletData_entireCompletion_ne_zero_of_re_nonpos (hne : χ ≠ 1) {s : ℂ}
    (hs : s.re ≤ 0) : (dirichletData χ hχ).entireCompletion s ≠ 0 := by
  rw [dirichletData_entireCompletion_one_sub χ hχ hne]
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

/-- On `ℂ`, the divisor of a nonprincipal primitive Dirichlet entire completion is its
analytic order. -/
theorem divisor_dirichletData_entireCompletion (hne : χ ≠ 1) (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s =
      ((analyticOrderAt (dirichletData χ hχ).entireCompletion s).toNat : ℤ) := by
  have ha : AnalyticOnNhd ℂ (dirichletData χ hχ).entireCompletion Set.univ :=
    fun z _ ↦ (dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion z
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (analyticOrderAt_dirichletData_entireCompletion_ne_top χ hχ hne s)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ s), ← hn]
  simp

/-- The divisor form of the zero location: a point of positive divisor of a nonprincipal
primitive Dirichlet entire completion lies in the open critical strip. -/
theorem re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos (hne : χ ≠ 1) {ρ : ℂ}
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    ρ.re ∈ Set.Ioo 0 1 := by
  refine re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hne ?_
  by_contra h
  have ha := (dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion ρ
  rw [divisor_dirichletData_entireCompletion χ hχ hne, ha.analyticOrderAt_eq_zero.mpr h] at hρ
  simp at hρ

/-- For a zero `ρ` of a nonprincipal primitive Dirichlet entire completion and `1 ≤ Re s`,
the summand `Re (1 / (s - ρ))` is positive. -/
theorem re_one_div_sub_pos_of_dirichletData_entireCompletion_eq_zero (hne : χ ≠ 1) {ρ s : ℂ}
    (hρ : (dirichletData χ hχ).entireCompletion ρ = 0) (hs : 1 ≤ s.re) :
    0 < (1 / (s - ρ)).re :=
  Complex.re_one_div_sub_pos
    ((re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hne hρ).2.trans_le hs)

/-! ### Symmetries of the zero orders -/

/-- The functional equation transports zero orders from `Λ₀(χ⁻¹)` at `s` to `Λ₀(χ)` at
`1 - s`. -/
theorem analyticOrderAt_dirichletData_entireCompletion_one_sub (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion (1 - s) =
      analyticOrderAt (dirichletData χ⁻¹ hχ.inv).entireCompletion s := by
  have hfe : (dirichletData χ hχ).entireCompletion = fun z ↦
      χ.rootNumber * ((dirichletData χ⁻¹ hχ.inv).entireCompletion ∘ (fun z ↦ 1 - z)) z :=
    funext (dirichletData_entireCompletion_one_sub χ hχ hne)
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) (1 - s) := by fun_prop
  have hcomp : analyticOrderAt ((dirichletData χ⁻¹ hχ.inv).entireCompletion ∘
      (fun z ↦ 1 - z)) (1 - s) = analyticOrderAt (dirichletData χ⁻¹ hχ.inv).entireCompletion s := by
    rw [analyticOrderAt_comp_of_deriv_ne_zero hg (by simp), sub_sub_cancel]
  have ha : AnalyticAt ℂ ((dirichletData χ⁻¹ hχ.inv).entireCompletion ∘ (fun z ↦ 1 - z))
      (1 - s) :=
    ((dirichletData_hasMeromorphicContinuation χ⁻¹ hχ.inv).analyticAt_entireCompletion _).comp hg
  rw [hfe, ← Pi.mul_def (f := fun _ ↦ χ.rootNumber), analyticOrderAt_mul analyticAt_const ha,
    analyticAt_const.analyticOrderAt_eq_zero.mpr (DirichletCharacter.rootNumber_ne_zero hχ),
    zero_add, hcomp]

/-- Reflection across the real axis transports zero orders from `Λ₀(χ)` at `s` to `Λ₀(χ⁻¹)`
at `conj s`. -/
theorem analyticOrderAt_dirichletData_inv_entireCompletion_conj (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (dirichletData χ⁻¹ hχ.inv).entireCompletion (conj s) =
      analyticOrderAt (dirichletData χ hχ).entireCompletion s := by
  have hfe : (dirichletData χ⁻¹ hχ.inv).entireCompletion =
      conj ∘ (dirichletData χ hχ).entireCompletion ∘ conj :=
    funext (dirichletData_inv_entireCompletion χ hχ hne)
  have h₁ := (dirichletData_hasMeromorphicContinuation χ⁻¹ hχ.inv).analyticAt_entireCompletion
    (conj s)
  have h₂ := (dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion s
  have hm := TauCeti.meromorphicOrderAt_conj_conj
    (f := (dirichletData χ hχ).entireCompletion) (x := conj s)
  rw [← hfe, Complex.conj_conj, h₁.meromorphicOrderAt_eq, h₂.meromorphicOrderAt_eq] at hm
  exact ENat.map_natCast_injective hm

/-- The composite `ρ ↦ 1 - conj ρ` preserves the zero orders of a nonprincipal primitive
Dirichlet entire completion. -/
theorem analyticOrderAt_dirichletData_entireCompletion_one_sub_conj (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion (1 - conj s) =
      analyticOrderAt (dirichletData χ hχ).entireCompletion s := by
  rw [analyticOrderAt_dirichletData_entireCompletion_one_sub χ hχ hne,
    analyticOrderAt_dirichletData_inv_entireCompletion_conj χ hχ hne]

/-- For a real character, the inverse character has the same analytic record. Mathlib's
`MulChar.IsQuadratic.inv` supplies the hypothesis for quadratic characters. -/
theorem dirichletData_inv_of_inv_eq (hreal : χ⁻¹ = χ) :
    dirichletData χ⁻¹ hχ.inv = dirichletData χ hχ := by
  generalize hχ.inv = hχ'
  revert hχ'
  rw [hreal]
  exact fun _ ↦ rfl

/-- For a real character, conjugation preserves the zero orders of the entire completion. -/
theorem analyticOrderAt_dirichletData_entireCompletion_conj_of_inv_eq (hne : χ ≠ 1)
    (hreal : χ⁻¹ = χ) (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion (conj s) =
      analyticOrderAt (dirichletData χ hχ).entireCompletion s := by
  simpa only [dirichletData_inv_of_inv_eq χ hχ hreal] using
    analyticOrderAt_dirichletData_inv_entireCompletion_conj χ hχ hne s

/-- For a real character, the reflection `s ↦ 1 - s` preserves the zero orders of the entire
completion. -/
theorem analyticOrderAt_dirichletData_entireCompletion_one_sub_of_inv_eq (hne : χ ≠ 1)
    (hreal : χ⁻¹ = χ) (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion (1 - s) =
      analyticOrderAt (dirichletData χ hχ).entireCompletion s := by
  simpa only [dirichletData_inv_of_inv_eq χ hχ hreal] using
    analyticOrderAt_dirichletData_entireCompletion_one_sub χ hχ hne s

/-! ### Divisor forms -/

/-- The divisor form of `analyticOrderAt_dirichletData_entireCompletion_one_sub`. -/
theorem divisor_dirichletData_entireCompletion_one_sub (hne : χ ≠ 1) (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ (1 - s) =
      MeromorphicOn.divisor (dirichletData χ⁻¹ hχ.inv).entireCompletion Set.univ s := by
  rw [divisor_dirichletData_entireCompletion χ hχ hne,
    divisor_dirichletData_entireCompletion χ⁻¹ hχ.inv (inv_ne_one.mpr hne),
    analyticOrderAt_dirichletData_entireCompletion_one_sub χ hχ hne]

/-- The divisor form of `analyticOrderAt_dirichletData_inv_entireCompletion_conj`. -/
theorem divisor_dirichletData_inv_entireCompletion_conj (hne : χ ≠ 1) (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ⁻¹ hχ.inv).entireCompletion Set.univ (conj s) =
      MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s := by
  rw [divisor_dirichletData_entireCompletion χ hχ hne,
    divisor_dirichletData_entireCompletion χ⁻¹ hχ.inv (inv_ne_one.mpr hne),
    analyticOrderAt_dirichletData_inv_entireCompletion_conj χ hχ hne]

/-- The divisor form of `analyticOrderAt_dirichletData_entireCompletion_one_sub_conj`. -/
theorem divisor_dirichletData_entireCompletion_one_sub_conj (hne : χ ≠ 1) (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ (1 - conj s) =
      MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s := by
  rw [divisor_dirichletData_entireCompletion χ hχ hne,
    divisor_dirichletData_entireCompletion χ hχ hne,
    analyticOrderAt_dirichletData_entireCompletion_one_sub_conj χ hχ hne]

/-- The divisor form of `analyticOrderAt_dirichletData_entireCompletion_conj_of_inv_eq`. -/
theorem divisor_dirichletData_entireCompletion_conj_of_inv_eq (hne : χ ≠ 1)
    (hreal : χ⁻¹ = χ) (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ (conj s) =
      MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s := by
  rw [divisor_dirichletData_entireCompletion χ hχ hne,
    divisor_dirichletData_entireCompletion χ hχ hne,
    analyticOrderAt_dirichletData_entireCompletion_conj_of_inv_eq χ hχ hne hreal]

/-- The divisor form of `analyticOrderAt_dirichletData_entireCompletion_one_sub_of_inv_eq`. -/
theorem divisor_dirichletData_entireCompletion_one_sub_of_inv_eq (hne : χ ≠ 1)
    (hreal : χ⁻¹ = χ) (s : ℂ) :
    MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ (1 - s) =
      MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s := by
  rw [divisor_dirichletData_entireCompletion χ hχ hne,
    divisor_dirichletData_entireCompletion χ hχ hne,
    analyticOrderAt_dirichletData_entireCompletion_one_sub_of_inv_eq χ hχ hne hreal]

end TauCeti.LFunctions
