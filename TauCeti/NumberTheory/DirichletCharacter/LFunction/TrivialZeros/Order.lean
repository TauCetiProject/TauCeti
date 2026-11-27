/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.TrivialZeros.Basic
import TauCeti.NumberTheory.LFunctions.Continued.Dirichlet

/-!
# Simplicity of the negative trivial zeros of Dirichlet L-functions

The functional equation makes the primitive completion nonzero at every point of the open left
half-plane. The simple poles of the archimedean factor then give simple zeros of the uncompleted
function. The deleted Euler factors are units there, so raising the level preserves this order.
-/

public section

open Complex Filter TauCeti Topology

namespace DirichletCharacter

/-- At a zero of the gamma factor of a Dirichlet character, the gamma factor has a simple pole:
its meromorphic order is `-1`. -/
theorem meromorphicOrderAt_gammaFactor_eq_neg_one_of_eq_zero {N : ℕ}
    (χ : DirichletCharacter ℂ N) {s : ℂ} (h : χ.gammaFactor s = 0) :
    meromorphicOrderAt χ.gammaFactor s = -1 := by
  rcases χ.even_or_odd with heven | hodd
  · rw [funext heven.gammaFactor_def]
    exact (meromorphicOrderAt_Gammaℝ_eq_neg_one_iff s).mpr
      ((gammaFactor_eq_zero_iff_of_even heven).mp h)
  · have hΓ : χ.gammaFactor = Gammaℝ ∘ fun z : ℂ ↦ z + 1 := funext hodd.gammaFactor_def
    obtain ⟨n, hn⟩ := (gammaFactor_eq_zero_iff_of_odd hodd).mp h
    rw [hΓ, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    exact (meromorphicOrderAt_Gammaℝ_eq_neg_one_iff (s + 1)).mpr ⟨n, by linear_combination hn⟩

open scoped Classical in
/-- In the open left half-plane the meromorphic order of a Dirichlet L-function is `1` at a
trivial zero and `0` elsewhere, even for an imprimitive or principal character. -/
theorem meromorphicOrderAt_LFunction_of_re_neg {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s.re < 0) :
    meromorphicOrderAt χ.LFunction s = if χ.LFunction s = 0 then 1 else 0 := by
  classical
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  by_cases hz : χ.LFunction s = 0
  · rw [ite_eq_left hz]
    have hs0 : s ≠ 0 := by intro h; simp [h] at hs
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    let ψ := χ.primitiveCharacter
    have hψ : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
    rw [← χ.changeLevel_primitiveCharacter, meromorphicOrderAt_LFunction_changeLevel _ _ hs.ne]
    have hψz : ψ.LFunction s = 0 :=
      (LFunction_changeLevel_eq_zero_iff ψ χ.conductor_dvd_level hs.ne (.inr hs1)).mp
        (by simpa only [ψ, χ.changeLevel_primitiveCharacter] using hz)
    have hΓz := (ψ.LFunction_eq_zero_iff_of_re_neg hs).mp hψz
    have hψc : ψ.completedLFunction s ≠ 0 := by
      rw [← sub_sub_cancel (1 : ℂ) s, hψ.completedLFunction_one_sub]
      refine mul_ne_zero (mul_ne_zero (by simp [NeZero.ne χ.conductor]) (rootNumber_ne_zero hψ))
        (ψ⁻¹.completedLFunction_ne_zero_of_one_le_re (.inr (by simpa using hs0)) ?_)
      simp only [sub_re, one_re]
      linarith
    -- the order of `L = completed / gammaFactor` is `0 - (-1)`
    have hN : ((χ.conductor : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr χ.conductor_ne_zero
    have hca : AnalyticAt ℂ
        (fun z ↦ ((χ.conductor : ℕ) : ℂ) ^ (z / 2) * ψ.completedLFunction z) s :=
      (((differentiable_id.div_const 2).const_cpow (.inl hN)).analyticAt s).mul
        (ψ.analyticAt_completedLFunction (.inl hs0) (.inl hs1))
    rw [← LFunctions.dirichletData_continuedL ψ hψ,
      (LFunctions.dirichletData ψ hψ).meromorphicOrderAt_continuedL
        (LFunctions.dirichletData_hasMeromorphicContinuation ψ hψ).meromorphic,
      funext (LFunctions.dirichletData_completed ψ hψ),
      funext (LFunctions.dirichletData_gammaFactor ψ hψ),
      hca.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (mul_ne_zero (cpow_ne_zero_iff.mpr (.inl hN)) hψc),
      ψ.meromorphicOrderAt_gammaFactor_eq_neg_one_of_eq_zero hΓz]
    simp
  · rw [ite_eq_right hz]
    exact (χ.analyticAt_LFunction (.inl hs1)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hz

end DirichletCharacter
