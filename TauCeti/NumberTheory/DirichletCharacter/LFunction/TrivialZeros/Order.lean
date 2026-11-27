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

/-!
# Simplicity of the negative trivial zeros of Dirichlet L-functions

The functional equation makes the primitive completion nonzero at every point of the open left
half-plane. The simple poles of the archimedean factor then give simple zeros of the uncompleted
function. The deleted Euler factors are units there, so raising the level preserves this order.
-/

public section

open Complex Filter TauCeti Topology

namespace DirichletCharacter

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
    have ha := ψ.analyticAt_completedLFunction (.inl hs0) (.inl hs1)
    have he : ψ.LFunction =ᶠ[𝓝[≠] s] ψ.completedLFunction / ψ.gammaFactor := by
      filter_upwards [(eventually_ne_nhds hs0).filter_mono nhdsWithin_le_nhds] with z hz0
      exact ψ.LFunction_eq_completed_div_gammaFactor z (.inl hz0)
    rw [meromorphicOrderAt_congr he]
    rcases ψ.even_or_odd with heven | hodd
    · rw [funext heven.gammaFactor_def, meromorphicOrderAt_div ha.meromorphicAt
        (meromorphic_Gammaℝ s), ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hψc,
        (meromorphicOrderAt_Gammaℝ_eq_neg_one_iff s).mpr
          ((gammaFactor_eq_zero_iff_of_even heven).mp hΓz)]
      simp
    · have hΓ : ψ.gammaFactor = Gammaℝ ∘ fun z : ℂ ↦ z + 1 := funext hodd.gammaFactor_def
      rw [hΓ, meromorphicOrderAt_div ha.meromorphicAt
        ((meromorphic_Gammaℝ (s + 1)).comp_analyticAt
          (g := fun z : ℂ ↦ z + 1) (by fun_prop)),
        meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt,
        ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hψc]
      have hp := (gammaFactor_eq_zero_iff_of_odd hodd).mp hΓz
      rw [(meromorphicOrderAt_Gammaℝ_eq_neg_one_iff (s + 1)).mpr (by
        obtain ⟨n, hn⟩ := hp
        exact ⟨n, by linear_combination hn⟩)]
      simp
  · rw [ite_eq_right hz]
    exact (χ.analyticAt_LFunction (.inl hs1)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hz

end DirichletCharacter
