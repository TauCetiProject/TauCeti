/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Vanishing order along the real coordinates of `ℂ`

A statement about maps on `ℝ × ℝ` is often proved by reading the domain as `ℂ` through
`Complex.equivRealProdCLM`. Vanishing to order `n` at `z₀`, measured by `‖z - z₀‖ⁿ`, is then
vanishing to order `n` at the corresponding point in the complex coordinate
(`TauCeti.isBigO_comp_equivRealProdCLM`).
-/

public section

open Asymptotics Filter Function Set Topology

namespace TauCeti

/-- Vanishing to order `n` at `z₀` is vanishing to order `n` in the complex coordinate
`Complex.equivRealProdCLM`. -/
theorem isBigO_comp_equivRealProdCLM {E : Type*} [Norm E] {ξ : ℝ × ℝ → E} {z₀ : ℝ × ℝ} {n : ℕ}
    (h₀ : ξ =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ n) :
    (ξ ∘ Complex.equivRealProdCLM) =O[𝓝 (Complex.equivRealProdCLM.symm z₀)]
      fun w ↦ (w - Complex.equivRealProdCLM.symm z₀) ^ n := by
  set e := Complex.equivRealProdCLM
  -- In the complex coordinate the vanishing order is measured by `‖e w - e w₀‖ ≤ ‖e‖ ‖w - w₀‖`.
  have h := h₀.comp_tendsto
    ((e.continuous.tendsto (e.symm z₀)).trans_eq (by rw [e.apply_symm_apply]))
  refine h.trans (IsBigO.of_bound (‖(e : ℂ →L[ℝ] ℝ × ℝ)‖ ^ n) (Eventually.of_forall fun w ↦ ?_))
  have hw : e w - z₀ = e (w - e.symm z₀) := by simp
  simp only [comp_apply, hw, norm_pow, norm_norm, ← mul_pow]
  gcongr
  exact (e : ℂ →L[ℝ] ℝ × ℝ).le_opNorm _

end TauCeti
