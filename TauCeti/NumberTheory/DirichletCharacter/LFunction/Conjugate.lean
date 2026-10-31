/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Conjugate
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Reflection of continued Dirichlet L-functions

Complex conjugation interchanges the continued L-functions of a Dirichlet character and its
inverse. We extend the Dirichlet-series identity to the punctured plane by analytic uniqueness,
and across `1` for nonprincipal characters. Thus the result applies to the continued function,
not the totalized Dirichlet series outside its convergence half-plane.

For quadratic characters this gives reflection of zeros across the real axis and reality at
real arguments away from the possible principal-character pole at `1`, including the interval
to its left used in real-zero estimates. We also give the reflection identity for derivatives
and their real-axis specialization.

The continuation is Mathlib's `DirichletCharacter.LFunction`; coefficientwise reflection uses
`TauCeti.LSeries.LSeries_star`.
-/

public section

open Complex Filter
open scoped Topology ComplexConjugate

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

private theorem LFunction_inv_conj_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    χ⁻¹.LFunction (conj s) = conj (χ.LFunction s) := by
  have hseries {z : ℂ} (hz : 1 < z.re) :
      χ⁻¹.LFunction z = conj (χ.LFunction (conj z)) := by
    rw [LFunction_eq_LSeries _ hz, LFunction_eq_LSeries _ (by simpa using hz)]
    have hcoeff : (fun n : ℕ ↦ χ⁻¹ n) = star (fun n : ℕ ↦ χ n) := by
      ext n
      exact (MulChar.star_apply' χ n).symm
    rw [hcoeff]
    simpa only [Complex.star_def, conj_conj] using
      TauCeti.LSeries.LSeries_star (fun n : ℕ ↦ χ n) (conj z)
  have hleft : AnalyticOnNhd ℂ χ⁻¹.LFunction ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz ↦ (differentiableAt_LFunction _ _ (.inl hz)).differentiableWithinAt)
      isOpen_compl_singleton
  have hright : AnalyticOnNhd ℂ (conj ∘ χ.LFunction ∘ conj) ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro z hz
    have hz' : conj z ≠ 1 := fun h ↦ hz (by simpa using congrArg conj h)
    simpa using (differentiableAt_LFunction χ (conj z) (.inl hz')).conj_conj.differentiableWithinAt
  have heq := hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (isConnected_compl_singleton_of_one_lt_rank
      (rank_real_complex ▸ Nat.one_lt_ofNat) 1).isPreconnected (by simp : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
    (eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : 1 < (2 : ℂ).re))
      (fun z hz ↦ hseries hz))
  have hs' : conj s ∈ ({1}ᶜ : Set ℂ) := fun h ↦ hs (by simpa using congrArg conj h)
  simpa using heq hs'

/-- Reflection interchanges a character and its inverse. At the possible pole `1` we require
that the character be nonprincipal. -/
theorem LFunction_inv_conj {s : ℂ} (hs : s ≠ 1 ∨ χ ≠ 1) :
    χ⁻¹.LFunction (conj s) = conj (χ.LFunction s) := by
  rcases hs with hs | hχ
  · exact LFunction_inv_conj_of_ne_one χ hs
  · have hleft : Continuous (fun z ↦ χ⁻¹.LFunction (conj z)) :=
      (differentiable_LFunction (inv_ne_one.mpr hχ)).continuous.comp continuous_conj
    have hright : Continuous (fun z ↦ conj (χ.LFunction z)) :=
      continuous_conj.comp (differentiable_LFunction hχ).continuous
    exact congrFun (hleft.ext_on (dense_compl_singleton 1) hright
      (fun z hz ↦ LFunction_inv_conj_of_ne_one χ hz)) s

/-- Reflection interchanges the zeros of the continued L-functions of inverse characters. -/
@[simp]
theorem LFunction_inv_conj_eq_zero_iff (s : ℂ) :
    χ⁻¹.LFunction (conj s) = 0 ↔ χ.LFunction s = 0 := by
  by_cases h : s = 1 ∧ χ = 1
  · rcases h with ⟨rfl, rfl⟩
    simp
  · rw [LFunction_inv_conj χ (not_and_or.mp h), map_eq_zero]

/-- The derivatives of the continued L-functions of inverse characters satisfy the same
reflection identity wherever the L-functions are holomorphic. -/
theorem deriv_LFunction_inv_conj {s : ℂ} (hs : s ≠ 1 ∨ χ ≠ 1) :
    deriv χ⁻¹.LFunction (conj s) = conj (deriv χ.LFunction s) := by
  have hloc : χ⁻¹.LFunction =ᶠ[𝓝 (conj s)] conj ∘ χ.LFunction ∘ conj := by
    rcases hs with hs | hχ
    · have hs' : conj s ≠ 1 := fun h ↦ hs (by simpa using congrArg conj h)
      filter_upwards [isOpen_compl_singleton.mem_nhds hs'] with z hz
      have hz' : conj z ≠ 1 := fun h ↦ hz (by simpa using congrArg conj h)
      simpa using LFunction_inv_conj χ (s := conj z) (.inl hz')
    · filter_upwards [] with z
      simpa using LFunction_inv_conj χ (s := conj z) (.inr hχ)
  rw [hloc.deriv_eq, deriv_conj_conj]
  simp

variable {χ}

/-- A quadratic character's continued L-function commutes with conjugation away from its
possible pole at `1`. -/
@[simp]
theorem LFunction_conj_of_isQuadratic (hχ : χ.IsQuadratic) {s : ℂ}
    (hs : s ≠ 1 ∨ χ ≠ 1) : χ.LFunction (conj s) = conj (χ.LFunction s) := by
  simpa only [hχ.inv] using LFunction_inv_conj χ hs

/-- The derivative of a quadratic character's continued L-function commutes with conjugation
wherever the L-function is holomorphic. -/
@[simp]
theorem deriv_LFunction_conj_of_isQuadratic (hχ : χ.IsQuadratic) {s : ℂ}
    (hs : s ≠ 1 ∨ χ ≠ 1) : deriv χ.LFunction (conj s) = conj (deriv χ.LFunction s) := by
  simpa only [hχ.inv] using deriv_LFunction_inv_conj χ hs

/-- The continued L-function of a quadratic character is real at real arguments away from its
possible pole at `1`, not only in the half-plane of convergence. -/
@[simp]
theorem LFunction_im_eq_zero_of_isQuadratic (hχ : χ.IsQuadratic) (x : ℝ)
    (hx : x ≠ 1 ∨ χ ≠ 1) : (χ.LFunction x).im = 0 := by
  have h := LFunction_conj_of_isQuadratic hχ (s := x) (by simpa using hx)
  rw [conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

/-- The derivative of a quadratic character's continued L-function is real at real arguments
wherever the L-function is holomorphic. -/
@[simp]
theorem deriv_LFunction_im_eq_zero_of_isQuadratic (hχ : χ.IsQuadratic) (x : ℝ)
    (hx : x ≠ 1 ∨ χ ≠ 1) : (deriv χ.LFunction x).im = 0 := by
  have h := deriv_LFunction_conj_of_isQuadratic hχ (s := x) (by simpa using hx)
  rw [conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

/-- The zeros of a quadratic L-function are invariant under reflection across the real axis. -/
@[simp]
theorem LFunction_conj_eq_zero_iff_of_isQuadratic (hχ : χ.IsQuadratic) (s : ℂ) :
    χ.LFunction (conj s) = 0 ↔ χ.LFunction s = 0 := by
  simpa only [hχ.inv] using LFunction_inv_conj_eq_zero_iff χ s

end DirichletCharacter
