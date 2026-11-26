/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
public import TauCeti.NumberTheory.LSeries.Conjugate
public import TauCeti.Analysis.Meromorphic.ZeroFree
import TauCeti.Analysis.Meromorphic.Conj
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
to its left used in real-zero estimates. We also give the reflection identity for derivatives and
their real-axis specialization.
The order form `meromorphicOrderAt_LFunction_inv_conj` holds at every point, the pole included,
and `zeroFreeRightOf_LFunction_inv_iff` transfers zero-free half-planes between `χ` and `χ⁻¹`.

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

/-- The conjugation identity solved for the inverse character: away from the possible pole `1`,
`χ⁻¹.LFunction s` is `conj (χ.LFunction (conj s))`. -/
private theorem LFunction_inv_eq_conj_LFunction_conj {s : ℂ} (hs : s ≠ 1 ∨ χ ≠ 1) :
    χ⁻¹.LFunction s = conj (χ.LFunction (conj s)) := by
  simpa only [conj_conj] using χ.LFunction_inv_conj (s := conj s)
    (hs.imp_left (map_ne_one_iff _ (starRingEnd ℂ).injective).mpr)

/-- Reflection interchanges the zeros of the continued L-functions of inverse characters. -/
@[simp]
theorem LFunction_inv_conj_eq_zero_iff (s : ℂ) :
    χ⁻¹.LFunction (conj s) = 0 ↔ χ.LFunction s = 0 := by
  by_cases h : s = 1 ∧ χ = 1
  · rcases h with ⟨rfl, rfl⟩
    simp
  · rw [LFunction_inv_conj χ (not_and_or.mp h), map_eq_zero]

/-- The derivatives of the continued L-functions of inverse characters satisfy the same
reflection identity. At the pole `1` of the principal character both sides are `0`, as the
L-function is not differentiable there. -/
theorem deriv_LFunction_inv_conj (s : ℂ) :
    deriv χ⁻¹.LFunction (conj s) = conj (deriv χ.LFunction s) := by
  by_cases hs : s = 1 ∧ χ = 1
  · obtain ⟨rfl, rfl⟩ := hs
    simp [deriv_zero_of_not_differentiableAt TauCeti.not_differentiableAt_LFunctionTrivChar_one]
  have hs := not_and_or.mp hs
  have hloc : χ⁻¹.LFunction =ᶠ[𝓝 (conj s)] conj ∘ χ.LFunction ∘ conj := by
    rcases hs with hs | hχ
    · have hs' : conj s ≠ 1 := fun h ↦ hs (by simpa using congrArg conj h)
      filter_upwards [isOpen_compl_singleton.mem_nhds hs'] with z hz
      simpa only [Function.comp_apply] using χ.LFunction_inv_eq_conj_LFunction_conj (.inl hz)
    · filter_upwards [] with z
      simpa only [Function.comp_apply] using χ.LFunction_inv_eq_conj_LFunction_conj (.inr hχ)
  rw [hloc.deriv_eq, deriv_conj_conj]
  simp

/-- Inverting the character and conjugating the argument conjugates the logarithmic derivative.
At the principal-character pole at `1`, both sides are `0` by totalization. -/
theorem logDeriv_LFunction_inv_conj (s : ℂ) :
    logDeriv χ⁻¹.LFunction (conj s) = conj (logDeriv χ.LFunction s) := by
  by_cases hs : s = 1 ∧ χ = 1
  · obtain ⟨rfl, rfl⟩ := hs
    simp [logDeriv_apply,
      deriv_zero_of_not_differentiableAt TauCeti.not_differentiableAt_LFunctionTrivChar_one]
  · rw [logDeriv_apply, logDeriv_apply, χ.deriv_LFunction_inv_conj,
      χ.LFunction_inv_conj (not_and_or.mp hs), map_div₀]

/-- On a punctured neighbourhood of every point, `χ⁻¹.LFunction` is
`conj ∘ χ.LFunction ∘ conj`. -/
private theorem LFunction_inv_eventuallyEq_nhdsNE (s : ℂ) :
    χ⁻¹.LFunction =ᶠ[𝓝[≠] s] conj ∘ χ.LFunction ∘ conj := by
  filter_upwards [(eventually_cofinite_ne 1).filter_mono (nhdsNE_le_cofinite _)] with z hz
  simpa only [Function.comp_apply] using χ.LFunction_inv_eq_conj_LFunction_conj (.inl hz)

/-- The order of `χ⁻¹.LFunction` at `conj s` is the order of `χ.LFunction` at `s`, for every `s`,
including the pole `1` of the principal character. This is the order form of
`DirichletCharacter.LFunction_inv_conj`. -/
@[simp]
theorem meromorphicOrderAt_LFunction_inv_conj (s : ℂ) :
    meromorphicOrderAt χ⁻¹.LFunction (conj s) = meromorphicOrderAt χ.LFunction s := by
  rw [meromorphicOrderAt_congr (χ.LFunction_inv_eventuallyEq_nhdsNE (conj s)),
    TauCeti.meromorphicOrderAt_conj_conj, conj_conj]

/-- For every real `σ`, `χ⁻¹.LFunction` is zero-free right of `σ` exactly when `χ.LFunction` is:
the two functions are conjugate off the possible pole `1`, and `TauCeti.ZeroFreeRightOf` depends
only on punctured germs and is invariant under `f ↦ conj ∘ f ∘ conj`. -/
@[simp]
theorem zeroFreeRightOf_LFunction_inv_iff {σ : ℝ} :
    TauCeti.ZeroFreeRightOf σ χ⁻¹.LFunction ↔ TauCeti.ZeroFreeRightOf σ χ.LFunction :=
  (TauCeti.zeroFreeRightOf_congr fun s _ ↦ χ.LFunction_inv_eventuallyEq_nhdsNE s).trans
    TauCeti.zeroFreeRightOf_conj_conj_iff

variable {χ}

/-- A quadratic character's continued L-function commutes with conjugation away from its
possible pole at `1`. -/
@[simp]
theorem LFunction_conj_of_isQuadratic (hχ : χ.IsQuadratic) {s : ℂ}
    (hs : s ≠ 1 ∨ χ ≠ 1) : χ.LFunction (conj s) = conj (χ.LFunction s) := by
  simpa only [hχ.inv] using LFunction_inv_conj χ hs

/-- The derivative of a quadratic character's continued L-function commutes with conjugation. -/
@[simp]
theorem deriv_LFunction_conj_of_isQuadratic (hχ : χ.IsQuadratic) (s : ℂ) :
    deriv χ.LFunction (conj s) = conj (deriv χ.LFunction s) := by
  simpa only [hχ.inv] using deriv_LFunction_inv_conj χ s

/-- The continued L-function of a quadratic character is real at real arguments away from its
possible pole at `1`, not only in the half-plane of convergence. -/
@[simp]
theorem LFunction_im_eq_zero_of_isQuadratic (hχ : χ.IsQuadratic) (x : ℝ)
    (hx : x ≠ 1 ∨ χ ≠ 1) : (χ.LFunction x).im = 0 := by
  have h := LFunction_conj_of_isQuadratic hχ (s := x) (by simpa using hx)
  rw [conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

/-- The derivative of a quadratic character's continued L-function is real at real arguments. -/
@[simp]
theorem deriv_LFunction_im_eq_zero_of_isQuadratic (hχ : χ.IsQuadratic) (x : ℝ) :
    (deriv χ.LFunction x).im = 0 := by
  have h := deriv_LFunction_conj_of_isQuadratic hχ (s := x)
  rw [conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

/-- The zeros of a quadratic L-function are invariant under reflection across the real axis. -/
@[simp]
theorem LFunction_conj_eq_zero_iff_of_isQuadratic (hχ : χ.IsQuadratic) (s : ℂ) :
    χ.LFunction (conj s) = 0 ↔ χ.LFunction s = 0 := by
  simpa only [hχ.inv] using LFunction_inv_conj_eq_zero_iff χ s

end DirichletCharacter
