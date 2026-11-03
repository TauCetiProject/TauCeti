/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.GaussSum
public import TauCeti.NumberTheory.DirichletCharacter.Even
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.Analysis.Meromorphic.Conj
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate

/-!
# Completed Dirichlet L-functions

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

/-- Every Dirichlet character has a meromorphic completed L-function on the whole plane. -/
theorem meromorphic_completedLFunction : Meromorphic χ.completedLFunction := by
  intro z
  have h₀ := (ZMod.differentiable_completedLFunction₀ (χ ·)).analyticAt z
  have hpow := (differentiable_id.neg.const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))).analyticAt z
  unfold completedLFunction
  rw [funext (ZMod.completedLFunction_eq (χ ·))]
  fun_prop

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
/-- Conjugation exchanges the gamma factors of a character and its inverse. -/
theorem gammaFactor_inv_conj (s : ℂ) :
    χ⁻¹.gammaFactor s = conj (χ.gammaFactor (conj s)) := by
  classical
  simp only [gammaFactor, even_inv_iff]
  split_ifs <;> simp [← Complex.Gammaℝ_conj]

/-- Conjugating the completed function gives the inverse character, away from its possible
poles. This compares the actual continued functions, not raw series outside convergence. -/
theorem completedLFunction_inv_conj {s : ℂ}
    (h0 : s ≠ 0 ∨ N ≠ 1) (h1 : s ≠ 1 ∨ χ ≠ 1) :
    χ⁻¹.completedLFunction s = conj (χ.completedLFunction (conj s)) := by
  apply TauCeti.eq_of_meromorphic_of_eqOn_halfPlane
    χ⁻¹.meromorphic_completedLFunction χ.meromorphic_completedLFunction.conj_conj
    (σ := 1) _ (χ⁻¹.analyticAt_completedLFunction h0 (h1.imp_right inv_ne_one.mpr))
    (TauCeti.analyticAt_conj_conj_iff.mpr <|
      χ.analyticAt_completedLFunction
        (h0.imp_left (by simpa using ·))
        (h1.imp_left (map_ne_one_iff _ (starRingEnd ℂ).injective).mpr))
  intro z hz
  have hzc : 1 < (conj z).re := by simpa using hz
  have hL : LSeries (χ⁻¹ ·) z = conj (LSeries (χ ·) (conj z)) := by
    rw [← χ⁻¹.LFunction_eq_LSeries hz, ← χ.LFunction_eq_LSeries hzc]
    simpa only [Complex.conj_conj] using χ.LFunction_inv_conj (s := conj z)
      (.inl fun he ↦ by simp [he] at hzc)
  simp only [Function.comp_apply]
  rw [completedLFunction_eq_gammaFactor_mul_LSeries _ hz,
    completedLFunction_eq_gammaFactor_mul_LSeries _ hzc, map_mul, gammaFactor_inv_conj, hL]

/-- Conjugating the root number gives the root number of the inverse character. -/
theorem rootNumber_inv : χ⁻¹.rootNumber = conj χ.rootNumber := by
  classical
  have hg : conj (gaussSum χ ZMod.stdAddChar) =
      χ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar := by
    rw [starRingEnd_apply, star_gaussSum_eq, AddChar.inv_mulShift,
      ← Units.coe_neg_one, gaussSum_mulShift_eq, inv_inv]
  have hp : conj ((N : ℂ) ^ (1 / 2 : ℂ)) = (N : ℂ) ^ (1 / 2 : ℂ) := by
    simpa only [map_div₀, map_one, map_ofNat, Complex.ofReal_natCast] using
      (TauCeti.ofReal_cpow_conj (Nat.cast_nonneg N) (1 / 2 : ℂ)).symm
  rw [rootNumber, rootNumber, map_div₀, map_div₀, hg, hp, map_pow, conj_I]
  rcases χ.even_or_odd with he | ho
  · have hneg : χ (-1) = 1 := by simpa only [map_one] using Even.eval_neg χ 1 he
    simp [even_inv_iff, he, hneg]
  · have hneg : χ (-1) = -1 := by simpa only [map_one] using Odd.eval_neg χ 1 ho
    simp [even_inv_iff, ho.not_even, hneg]

/-- The root number of a primitive Dirichlet character has absolute value one. -/
theorem IsPrimitive.norm_rootNumber {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : ‖χ.rootNumber‖ = 1 := by
  classical
  rw [rootNumber, norm_div, norm_div, norm_pow, norm_I, one_pow, div_one,
    hχ.norm_gaussSum (ZMod.isPrimitive_stdAddChar N),
    Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
  have hre : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
  rw [hre, ← Real.sqrt_eq_rpow]
  exact div_self (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))).ne'

end DirichletCharacter
