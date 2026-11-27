/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Basic
public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic

import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

/-!
# Zeros of primitive Dirichlet entire completions

Let `χ` be a primitive Dirichlet character and `Λ₀(χ)` the entire completion of its analytic
record. This file locates the zeros of `Λ₀(χ)` in the open critical strip and records the
symmetries of their multiplicities.

* `Λ₀(χ)` has no zeros on `1 ≤ Re s` (from `zetaEntireCompletion` at conductor `1` and nonvanishing
  of `L(χ, s)` for `χ ≠ 1`) and none on `Re s ≤ 0`, by the functional equation against `χ⁻¹`.
* Specializing the order symmetries of `Completion/Basic.lean` through
  `dirichletData_dual`: `ord_{1 - s} Λ₀(χ) = ord_s Λ₀(χ⁻¹)` and
  `ord_{conj s} Λ₀(χ⁻¹) = ord_s Λ₀(χ)`. Hence `ρ ↦ 1 - conj ρ` preserves the zero orders of
  `Λ₀(χ)`, and for a real character the orders are invariant under `conj` and under `s ↦ 1 - s`
  separately.
* For a zero `ρ` and `1 ≤ Re s`, the summand `Re (1 / (s - ρ))` of the partial-fraction
  expansion of `Λ₀'/Λ₀` is positive.
* On the positive half-plane, `Λ₀(χ)` and `χ.LFunction` have the same divisor (away from the
  pole of `riemannZeta` at `s = 1` when `χ = 1`) and the same zero count on any region
  `R ⊆ {0 < Re s}` (including `χ = 1` at `N = 1`, where both positive divisor multiplicities
  vanish at `1`); on any region `R`, `zeroCount` of `Λ₀(χ)` equals `zeroCount` of
  `χ.LFunction` on `R ∩ {0 < Re s < 1}` (`divisor_dirichletData_entireCompletion_eq_LFunction`,
  `zeroCount_dirichletData_entireCompletion_eq_LFunction`,
  `zeroCount_dirichletData_entireCompletion_eq_LFunction_inter`).

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

/-- Every primitive Dirichlet entire completion has no zeros on `1 ≤ Re s`. -/
theorem dirichletData_entireCompletion_ne_zero_of_one_le_re {s : ℂ}
    (hs : 1 ≤ s.re) : (dirichletData χ hχ).entireCompletion s ≠ 0 := by
  by_cases hN : N = 1
  · subst N
    rw [dirichletData_modOne, riemannZetaData_entireCompletion]
    exact zetaEntireCompletion_ne_zero_of_one_le_re hs
  · have hne : χ ≠ 1 := mt hχ.eq_one_iff.mp hN
    rw [dirichletData_entireCompletion_of_ne_one χ hχ hne, dirichletData_completed]
    exact mul_ne_zero (by simp [NeZero.ne N])
      (DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (.inl hne) hs)

/-- Every primitive Dirichlet entire completion has no zeros on `Re s ≤ 0`. -/
theorem dirichletData_entireCompletion_ne_zero_of_re_nonpos {s : ℂ}
    (hs : s.re ≤ 0) : (dirichletData χ hχ).entireCompletion s ≠ 0 :=
  (dirichletData_hasFunctionalEquation χ hχ).entireCompletion_ne_zero_of_re_nonpos
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (fun _ ↦ dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ) hs

/-- Every zero of a primitive Dirichlet entire completion lies in the open critical strip. -/
theorem re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero {ρ : ℂ}
    (hρ : (dirichletData χ hχ).entireCompletion ρ = 0) : ρ.re ∈ Set.Ioo 0 1 :=
  (dirichletData_hasFunctionalEquation χ hχ).re_mem_Ioo_of_entireCompletion_eq_zero
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (fun _ ↦ dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ) hρ

/-- The divisor form of the zero location: a point of positive divisor of a primitive Dirichlet
entire completion lies in the open critical strip. -/
theorem re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos {ρ : ℂ}
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    ρ.re ∈ Set.Ioo 0 1 :=
  re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ <|
    ((dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion ρ
      ).apply_eq_zero_of_divisor_ne_zero hρ.ne'

/-- For a zero `ρ` of a primitive Dirichlet entire completion and `1 ≤ Re s`,
the summand `Re (1 / (s - ρ))` is positive. -/
theorem re_one_div_sub_pos_of_dirichletData_entireCompletion_eq_zero {ρ s : ℂ}
    (hρ : (dirichletData χ hχ).entireCompletion ρ = 0) (hs : 1 ≤ s.re) :
    0 < (1 / (s - ρ)).re := by
  rw [one_div, Complex.inv_re_pos, sub_re, sub_pos]
  exact (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hρ).2.trans_le hs

/-! ### Symmetries of the zero orders -/

/-- The functional equation transports zero orders from `Λ₀(χ⁻¹)` at `s` to `Λ₀(χ)` at
`1 - s`. -/
theorem analyticOrderAt_dirichletData_entireCompletion_one_sub (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion (1 - s) =
      analyticOrderAt (dirichletData χ⁻¹ hχ.inv).entireCompletion s := by
  simpa only [dirichletData_dual] using
    (dirichletData_hasFunctionalEquation χ hχ).analyticOrderAt_entireCompletion_one_sub
      (dirichletData_hasMeromorphicContinuation χ hχ) s

/-- Reflection across the real axis transports zero orders from `Λ₀(χ)` at `s` to `Λ₀(χ⁻¹)`
at `conj s`. -/
theorem analyticOrderAt_dirichletData_inv_entireCompletion_conj (s : ℂ) :
    analyticOrderAt (dirichletData χ⁻¹ hχ.inv).entireCompletion (conj s) =
      analyticOrderAt (dirichletData χ hχ).entireCompletion s := by
  simpa only [dirichletData_dual] using
    (dirichletData_hasMeromorphicContinuation χ hχ).analyticOrderAt_dual_entireCompletion_conj s

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

/-- On the positive half-plane away from the pole at `1` of the principal character, a primitive
Dirichlet entire completion and its ordinary L-function have the same divisor. -/
theorem divisor_dirichletData_entireCompletion_eq_LFunction {s : ℂ} (hs : 0 < s.re)
    (h1 : s ≠ 1 ∨ χ ≠ 1) :
    MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s =
      MeromorphicOn.divisor χ.LFunction Set.univ s := by
  have ha := dirichletData_hasMeromorphicContinuation χ hχ
  rw [ha.meromorphicOn_entireCompletion.divisor_eq_analyticOrderNatAt
      (ha.analyticAt_entireCompletion s) (Set.mem_univ s),
    χ.meromorphic_LFunction.meromorphicOn.divisor_eq_analyticOrderNatAt
      (χ.analyticAt_LFunction h1) (Set.mem_univ s)]
  simp only [analyticOrderNatAt,
    analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hs]

/-- On the positive half-plane, the natural divisor multiplicity of the entire completion equals
the analytic vanishing order `analyticOrderNatAt χ.LFunction s` (including for `χ = 1` at `s = 1`,
where both vanish). -/
theorem toNat_divisor_dirichletData_entireCompletion_eq_analyticOrderNatAt
    {s : ℂ} (hs : 0 < s.re) :
    (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s).toNat =
      analyticOrderNatAt χ.LFunction s := by
  have hm := dirichletData_hasMeromorphicContinuation χ hχ
  rw [MeromorphicOn.divisor_eq_analyticOrderNatAt hm.meromorphicOn_entireCompletion
    (hm.analyticAt_entireCompletion s) (Set.mem_univ s), Int.toNat_natCast,
    analyticOrderNatAt_dirichletData_entireCompletion_eq_LFunction χ hχ hs]

/-- On any region in the positive half-plane, a primitive Dirichlet entire completion and its
ordinary L-function have the same zero count (including for the principal character at `N = 1`,
where both positive divisor multiplicities vanish at `s = 1`). -/
theorem zeroCount_dirichletData_entireCompletion_eq_LFunction {R : Set ℂ}
    (hR : ∀ s ∈ R, 0 < s.re) :
    zeroCount (dirichletData χ hχ).entireCompletion Set.univ R =
      zeroCount χ.LFunction Set.univ R := by
  rcases eq_or_ne χ 1 with h1 | hne
  · obtain ⟨he, hL⟩ := dirichletData_entireCompletion_of_eq_one χ hχ h1
    rw [he, hL]
    exact zeroCount_zetaEntireCompletion_eq_riemannZeta hR
  · exact zeroCount_congr_divisor fun s hs ↦
      congrArg Int.toNat
        (divisor_dirichletData_entireCompletion_eq_LFunction χ hχ (hR s hs) (.inr hne))

/-- On any region `R`, the zero count of a primitive Dirichlet entire completion is the zero count
of its ordinary L-function on the intersection of `R` with the open critical strip: every zero of
`Λ₀(χ)` lies in `0 < Re s < 1`, where `Λ₀(χ)` and `L(χ, s)` have the same zero multiplicities. -/
theorem zeroCount_dirichletData_entireCompletion_eq_LFunction_inter (R : Set ℂ) :
    zeroCount (dirichletData χ hχ).entireCompletion Set.univ R =
      zeroCount χ.LFunction Set.univ (R ∩ {s | s.re ∈ Set.Ioo 0 1}) := by
  rw [← zeroCount_inter_eq_self (S := {s | s.re ∈ Set.Ioo 0 1})
    fun s _ hs ↦ re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hs]
  exact zeroCount_dirichletData_entireCompletion_eq_LFunction χ hχ fun _ hs ↦ hs.2.1

end TauCeti.LFunctions
