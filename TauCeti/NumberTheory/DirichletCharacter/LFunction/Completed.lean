/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.GaussSum
public import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.Analysis.Meromorphic.Conj
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate

/-!
# Completed primitive Dirichlet L-functions

These results supplement Mathlib's continued Dirichlet functions with meromorphy, conjugation,
and the unit norm of the Gauss-sum root number. The functions themselves are Mathlib's, without
any change of representative. The conjugation comparison is asserted only away from the possible
poles at zero and one.

The analytic input is David Loeffler and Michael Stoll's development in
`Mathlib.NumberTheory.LSeries.DirichletContinuation`; the Gauss-sum norm uses the primitive
Gauss-sum product identity in `TauCeti.NumberTheory.DirichletCharacter.GaussSum`.
-/

public section

open Complex ComplexConjugate
open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- On the half-plane of absolute convergence, the completed Dirichlet function is its
archimedean gamma factor times its Dirichlet series. -/
theorem completedLFunction_eq_gammaFactor_mul_LSeries {s : ℂ} (hs : 1 < s.re) :
    χ.completedLFunction s = χ.gammaFactor s * LSeries (χ ·) s := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hΓ : χ.gammaFactor s ≠ 0 := by
    rcases χ.even_or_odd with h | h
    · rw [h.gammaFactor_def]
      exact Gammaℝ_ne_zero_of_re_pos (by linarith)
    · rw [h.gammaFactor_def]
      exact Gammaℝ_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith)
  rw [← χ.LFunction_eq_LSeries hs, χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0)]
  exact (mul_div_cancel₀ _ hΓ).symm

/-- A primitive character has a meromorphic completed L-function on the whole plane. -/
theorem IsPrimitive.meromorphic_completedLFunction {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : Meromorphic χ.completedLFunction := by
  by_cases h : χ = 1
  · have hN : N = 1 := by simpa [IsPrimitive, h, conductor_one] using hχ.symm
    subst N
    rw [completedLFunction_modOne_eq]
    exact TauCeti.meromorphic_completedRiemannZeta
  · exact fun z ↦ ((differentiable_completedLFunction h).analyticAt z).meromorphicAt

/-- The completed L-function is analytic except possibly at zero at level one, and at one
for the principal character. No primitivity assumption is needed. -/
theorem analyticAt_completedLFunction {s : ℂ} (h0 : s ≠ 0 ∨ N ≠ 1)
    (h1 : s ≠ 1 ∨ χ ≠ 1) : AnalyticAt ℂ χ.completedLFunction s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have he0 : ∀ᶠ z in 𝓝 s, z ≠ 0 ∨ N ≠ 1 := by
    rcases h0 with h0 | h0
    · filter_upwards [eventually_ne_nhds h0] with z hz using Or.inl hz
    · exact Filter.Eventually.of_forall fun _ ↦ Or.inr h0
  have he1 : ∀ᶠ z in 𝓝 s, z ≠ 1 ∨ χ ≠ 1 := by
    rcases h1 with h1 | h1
    · filter_upwards [eventually_ne_nhds h1] with z hz using Or.inl hz
    · exact Filter.Eventually.of_forall fun _ ↦ Or.inr h1
  filter_upwards [he0, he1] with z hz0 hz1
  exact χ.differentiableAt_completedLFunction z hz0 hz1

omit [NeZero N] in
/-- The parity of an inverse character is unchanged. -/
@[simp]
theorem even_inv_iff : χ⁻¹.Even ↔ χ.Even := by
  simp [Even, MulChar.inv_apply_eq_inv']

omit [NeZero N] in
/-- Conjugation exchanges the gamma factors of a character and its inverse. -/
theorem gammaFactor_inv (s : ℂ) :
    χ⁻¹.gammaFactor s = conj (χ.gammaFactor (conj s)) := by
  classical
  simp only [gammaFactor, even_inv_iff]
  split_ifs <;> simp [← Complex.Gammaℝ_conj]

/-- Conjugating the completed function gives the inverse character, away from its possible
poles. This compares the actual continued functions, not raw series outside convergence. -/
theorem IsPrimitive.completedLFunction_inv {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {s : ℂ} (h0 : s ≠ 0 ∨ N ≠ 1) (h1 : s ≠ 1 ∨ χ ≠ 1) :
    χ⁻¹.completedLFunction s = conj (χ.completedLFunction (conj s)) := by
  have hi : χ⁻¹.IsPrimitive := by rwa [isPrimitive_def, conductor_inv]
  apply TauCeti.eq_of_meromorphic_of_eqOn_halfPlane
    hi.meromorphic_completedLFunction hχ.meromorphic_completedLFunction.conj_conj
    (σ := 1) _ (χ⁻¹.analyticAt_completedLFunction h0 (h1.imp_right inv_ne_one.mpr))
    (TauCeti.analyticAt_conj_conj_iff.mpr <|
      χ.analyticAt_completedLFunction
        (h0.imp_left fun h he ↦ h <| (starRingEnd ℂ).injective
          (he.trans (map_zero _).symm))
        (h1.imp_left fun h he ↦ h <| (starRingEnd ℂ).injective
          (he.trans (map_one _).symm)))
  intro z hz
  have hzc : 1 < (conj z).re := hz
  have hL : LSeries (χ⁻¹ ·) z = conj (LSeries (χ ·) (conj z)) := by
    rw [← χ⁻¹.LFunction_eq_LSeries hz, ← χ.LFunction_eq_LSeries hzc]
    simpa only [Complex.conj_conj] using χ.LFunction_inv_conj (s := conj z)
      (.inl fun he ↦ by simp [he] at hzc)
  simp only [Function.comp_apply]
  rw [completedLFunction_eq_gammaFactor_mul_LSeries _ hz,
    completedLFunction_eq_gammaFactor_mul_LSeries _ hzc, map_mul, gammaFactor_inv, hL]

/-- The root number of a primitive Dirichlet character has absolute value one. -/
theorem IsPrimitive.norm_rootNumber {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : ‖χ.rootNumber‖ = 1 := by
  classical
  have hg := gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar N)
  rw [← star_gaussSum_eq, ZMod.card] at hg
  have hn : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (N : ℝ) := by
    have := congrArg Complex.re hg
    simpa [Complex.star_def, Complex.mul_conj, Complex.sq_norm] using this
  have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hnorm : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N := by
    nlinarith [Real.sq_sqrt hpos.le, norm_nonneg (gaussSum χ ZMod.stdAddChar),
      Real.sqrt_nonneg (N : ℝ)]
  rw [rootNumber, norm_div, norm_div, norm_pow, norm_I, one_pow, div_one, hnorm]
  have hp : (N : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt N : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hpos.le]
    norm_num
  rw [hp, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_self (Real.sqrt_pos.mpr hpos).ne'

end DirichletCharacter
