/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Zeros.Divisor
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# The entire completion of the Riemann zeta function

The explicit function `zetaEntireCompletion` is twice Riemann's ξ-function. It agrees with
`s * (s - 1) * completedRiemannZeta s` away from the two poles, but takes the value `1` at
both `0` and `1`. In particular, clearing the poles introduces no artificial zeros: its zeros in
`ℂ` are precisely the zeros of `riemannZeta` in the open critical strip `0 < Re s < 1`, and it
vanishes nowhere on the real line.

The identity with `riemannZetaData.entireCompletion` connects this formula and its reflection
symmetry to the general pole-clearing construction.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §12.
-/

public section

open Complex Polynomial
open scoped ComplexOrder

namespace TauCeti.LFunctions

/-- Twice Riemann's ξ-function, with its removable values at `0` and `1` filled in. -/
noncomputable def zetaEntireCompletion (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

theorem zetaEntireCompletion_def (s : ℂ) :
    zetaEntireCompletion s = s * (s - 1) * completedRiemannZeta₀ s + 1 := (rfl)

/-- The explicit entire completion is entire. -/
theorem differentiable_zetaEntireCompletion : Differentiable ℂ zetaEntireCompletion := by
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

@[simp]
theorem zetaEntireCompletion_zero : zetaEntireCompletion 0 = 1 := by
  simp [zetaEntireCompletion_def]

@[simp]
theorem zetaEntireCompletion_one : zetaEntireCompletion 1 = 1 := by
  simp [zetaEntireCompletion_def]

/-- The entire completion retains the reflection symmetry about the critical line. -/
theorem zetaEntireCompletion_one_sub (s : ℂ) :
    zetaEntireCompletion (1 - s) = zetaEntireCompletion s := by
  simp only [zetaEntireCompletion_def, completedRiemannZeta₀_one_sub]
  ring

/-- Away from the poles the explicit completion is the usual pole-cleared product. -/
theorem zetaEntireCompletion_eq_mul {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    zetaEntireCompletion s = s * (s - 1) * completedRiemannZeta s := by
  rw [zetaEntireCompletion_def, completedRiemannZeta_eq]
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- The Riemann zeta record clears precisely the simple poles at `0` and `1`. -/
@[simp]
theorem riemannZetaData_polarPolynomial :
    riemannZetaData.polarPolynomial = X * (X - 1) := by
  simp [AnalyticLFunctionData.polarPolynomial_def, Finsupp.prod_add_index', pow_add]

/-- The general removable extension recovers the explicit entire completion of zeta. -/
@[simp]
theorem riemannZetaData_entireCompletion :
    riemannZetaData.entireCompletion = zetaEntireCompletion := by
  symm
  apply riemannZetaData_hasMeromorphicContinuation.entireCompletion_unique
    differentiable_zetaEntireCompletion.continuous
  intro s hs
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  simpa using zetaEntireCompletion_eq_mul hs0 hs1

/-- The entire completion has a zero of positive multiplicity exactly where
`completedRiemannZeta` has one: clearing the poles at `0` and `1` creates no zeros. -/
theorem zero_lt_divisor_zetaEntireCompletion_iff {s : ℂ} :
    0 < MeromorphicOn.divisor zetaEntireCompletion Set.univ s ↔
      0 < MeromorphicOn.divisor completedRiemannZeta Set.univ s := by
  have h := riemannZetaData_hasMeromorphicContinuation.toNat_divisor_entireCompletion s
  rw [riemannZetaData_entireCompletion, riemannZetaData_completed] at h
  omega

/-- Every analytic order of `zetaEntireCompletion` is finite. -/
theorem analyticOrderAt_zetaEntireCompletion_ne_top (s : ℂ) :
    analyticOrderAt zetaEntireCompletion s ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ zetaEntireCompletion Set.univ :=
    fun z _ ↦ differentiable_zetaEntireCompletion.analyticAt z
  refine ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 0) (Set.mem_univ 0) (Set.mem_univ s) ?_
  rw [(ha 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr (by simp)]
  simp

/-- The zeros of `zetaEntireCompletion` in `ℂ` are precisely the zeros of `riemannZeta` in the
open critical strip `0 < Re s < 1`. -/
theorem zetaEntireCompletion_eq_zero_iff {s : ℂ} :
    zetaEntireCompletion s = 0 ↔ riemannZeta s = 0 ∧ s.re ∈ Set.Ioo 0 1 := by
  have ha := differentiable_zetaEntireCompletion.analyticAt s
  have hmer : MeromorphicOn zetaEntireCompletion Set.univ :=
    fun z _ ↦ (differentiable_zetaEntireCompletion.analyticAt z).meromorphicAt
  have htop : meromorphicOrderAt zetaEntireCompletion s ≠ ⊤ := by
    rw [ha.meromorphicOrderAt_eq]
    simpa using analyticOrderAt_zetaEntireCompletion_ne_top s
  rw [← hmer.zero_lt_divisor_iff_of_analyticAt ha (Set.mem_univ s) htop,
    zero_lt_divisor_zetaEntireCompletion_iff, zero_lt_divisor_completedRiemannZeta_iff_mem_Ioo]

/-- `zetaEntireCompletion` vanishes nowhere on the real axis. -/
theorem zetaEntireCompletion_ofReal_ne_zero (σ : ℝ) : zetaEntireCompletion σ ≠ 0 := by
  intro h
  obtain ⟨hζ, h0, h1⟩ := zetaEntireCompletion_eq_zero_iff.mp h
  simp only [ofReal_re] at h0 h1
  exact (TauCeti.riemannZeta_lt_zero h0 h1).ne hζ

end TauCeti.LFunctions
