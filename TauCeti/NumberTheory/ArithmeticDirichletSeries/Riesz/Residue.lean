/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.RemainderMellin
public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Origin

/-!
# Residues of the first Riesz Mellin expression

For an explicit formula, the Mellin expression is multiplied by `y ^ s`. Away from the
kernel poles, an analytic multiplier simply scales the residue by its value. At zero the
kernel pole also contributes, so the residue includes a logarithm with coefficient the
order of the original meromorphic function.
-/

public section

open Complex Filter Set Topology TauCeti.Contour

namespace TauCeti

/-- Away from `0` and `1`, the residue against an analytic multiplier is the order of `L`
divided by `z * (1 - z)`, times the multiplier at `z`. This includes points of order zero.
At `1` the compensated expression is analytic, and the right-hand side is zero by convention. -/
theorem _root_.Meromorphic.residue_rieszRemainderMellin_mul {L g : ℂ → ℂ}
    (hL : Meromorphic L) {z : ℂ} (h₀ : z ≠ 0) {m : ℤ}
    (hm : meromorphicOrderAt L z = m) (hg : AnalyticAt ℂ g z) :
    residue (fun s ↦ rieszRemainderMellin L s * g s) z = (m : ℂ) * g z / (z * (1 - z)) := by
  by_cases h₁ : z = 1
  · subst z
    simpa using residue_eq_zero_of_analyticAt (hL.analyticAt_rieszRemainderMellin_one.fun_mul hg)
  obtain ⟨H, hH, hval, heq⟩ := hL.exists_analyticAt_mul_rieszRemainderMellin h₀ h₁
  rw [hm, WithTop.untop₀_coe] at hval
  rw [residue_eq_of_eventuallyEq_div_sub (hH.mul hg) (φ := H * g) ?_, Pi.mul_apply, hval,
    div_mul_eq_mul_div]
  filter_upwards [heq, self_mem_nhdsWithin] with s hs hsz
  rw [Pi.mul_apply, ← hs, mul_assoc, mul_comm (s - z),
    mul_div_cancel_right₀ _ (sub_ne_zero.mpr hsz)]

/-- The residue at zero in the first Riesz explicit formula is the finite part of `L′/L` at
zero plus the order of `L` at zero times `1 + log y`. The compensation at `1` contributes
nothing to this residue. -/
theorem _root_.Meromorphic.residue_rieszRemainderMellin_mul_cpow_zero {L : ℂ → ℂ}
    (hL : Meromorphic L) {m : ℤ} (hm : meromorphicOrderAt L 0 = m) {y : ℂ} (hy : y ≠ 0) :
    residue (fun s ↦ rieszRemainderMellin L s * y ^ s) 0 =
      logDerivFinitePart L 0 + (m : ℂ) * (1 + log y) := by
  let c : ℂ := (meromorphicOrderAt L 1).untop₀
  let h (s : ℂ) := c * (s - 1) - c / (s - 1) - s * logDerivFinitePart L 1
  have ha : AnalyticAt ℂ h 0 := by
    have h₁ : (0 : ℂ) - 1 ≠ 0 := by simp
    dsimp only [h]
    fun_prop (disch := exact h₁)
  have heq : (fun s ↦ rieszRemainderMellin L s * y ^ s) =ᶠ[𝓝[≠] 0]
      fun s ↦ (logDeriv L s + h s) * y ^ s / (s * (1 - s)) := by
    filter_upwards [hL.rieszRemainderMellin_eventuallyEq 0] with s hs
    rw [hs, div_mul_eq_mul_div, ← neg_sub s 1, mul_neg, div_neg, ← neg_div]
    congr 1
    simp only [h, c]
    ring
  rw [residue_congr_nhdsNE heq, residue_rieszKernel_mul_logDeriv (hL 0) hm ha hy]
  obtain ⟨g, hg, hreg⟩ := (hL 0).exists_analyticAt_logDeriv_sub_order_div
  rw [hg.logDerivFinitePart_eq hreg]
  have hval := (toMeromorphicNFAt_eventuallyEq_nhds_congr hreg).eq_of_nhds
  simp only [hm, WithTop.untop₀_coe, sub_zero,
    toMeromorphicNFAt_eq_self.mpr hg.meromorphicNFAt] at hval
  rw [hval]
  simp [h, div_neg]

end TauCeti
