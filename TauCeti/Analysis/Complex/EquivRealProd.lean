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
(`TauCeti.isBigO_comp_equivRealProdCLM`). The discs `‖w‖ ≤ r`, read in the real coordinates, are
compact (`TauCeti.isCompact_setOf_norm_equivRealProdCLM_symm_le`). The Euclidean norm
`‖w‖` of the point `w` with real coordinates `z` has `‖w‖² = z.1² + z.2²`
(`TauCeti.sq_norm_equivRealProdCLM_symm`) and lies between the sup norm `‖z‖`
(`TauCeti.norm_le_norm_equivRealProdCLM_symm`) and twice it
(`TauCeti.norm_equivRealProdCLM_symm_le_two_mul`), so it is `2`-Lipschitz in `z`
(`TauCeti.lipschitzWith_two_norm_equivRealProdCLM_symm`) and the disc `‖w‖ ≤ r` lies in the square
`‖z‖ ≤ r` (`TauCeti.setOf_norm_equivRealProdCLM_symm_le_subset_closedBall`).
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

/-- The discs `‖w‖ ≤ r` of the plane, read in the real coordinates `ℝ × ℝ`, are compact. -/
theorem isCompact_setOf_norm_equivRealProdCLM_symm_le (r : ℝ) :
    IsCompact {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ r} := by
  simpa [Metric.closedBall] using (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage).2
    (isCompact_closedBall (0 : ℂ) r)

/-- The square of the Euclidean norm of the point of `ℂ` with real coordinates `z` is the sum
of the squares of the coordinates. -/
theorem sq_norm_equivRealProdCLM_symm (z : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm z‖ ^ 2 = z.1 ^ 2 + z.2 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [sq]

/-- The sup norm of the real coordinates `z` is at most the Euclidean norm of the corresponding
point of `ℂ`. -/
theorem norm_le_norm_equivRealProdCLM_symm (z : ℝ × ℝ) :
    ‖z‖ ≤ ‖Complex.equivRealProdCLM.symm z‖ := by
  simpa using Complex.equivRealProd_apply_le (Complex.equivRealProdCLM.symm z)

/-- The Euclidean norm of the point of `ℂ` with real coordinates `z` is at most twice the sup
norm of `z`. -/
theorem norm_equivRealProdCLM_symm_le_two_mul (z : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm z‖ ≤ 2 * ‖z‖ := by
  have hre : ‖Complex.equivRealProdCLM.symm z‖ ≤ |z.1| + |z.2| := by
    simpa using Complex.norm_le_abs_re_add_abs_im (Complex.equivRealProdCLM.symm z)
  have h₁ := norm_fst_le z
  have h₂ := norm_snd_le z
  rw [Real.norm_eq_abs] at h₁ h₂
  linarith

/-- The Euclidean norm `‖w‖` of the point of `ℂ` with real coordinates `z` is `2`-Lipschitz in the
sup norm of `z`. -/
theorem lipschitzWith_two_norm_equivRealProdCLM_symm :
    LipschitzWith 2 fun z : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z‖ :=
  LipschitzWith.of_dist_le_mul fun a b ↦ by
    rw [Real.dist_eq, dist_eq_norm]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← map_sub]
    simpa using norm_equivRealProdCLM_symm_le_two_mul (a - b)

/-- The disc `‖w‖ ≤ r` of the plane, read in the real coordinates, lies in the square
`‖z‖ ≤ r` of the sup norm. -/
theorem setOf_norm_equivRealProdCLM_symm_le_subset_closedBall (r : ℝ) :
    {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ r} ⊆ Metric.closedBall 0 r :=
  fun z (hz : _ ≤ r) ↦ mem_closedBall_zero_iff.2 ((norm_le_norm_equivRealProdCLM_symm z).trans hz)

end TauCeti
