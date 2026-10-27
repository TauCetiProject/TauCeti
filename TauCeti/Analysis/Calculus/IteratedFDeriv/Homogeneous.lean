/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv

/-!
# Iterated derivatives of homogeneous maps of degree zero

Let `m` be a map on a proper (for instance finite-dimensional) real normed space that is `C^N`
away from the origin and homogeneous of degree `0`, that is `m (t • ξ) = m ξ` for every `t > 0`.
Then its iterated derivatives decay like `‖D^k m ξ‖ ≤ A / ‖ξ‖ ^ k` for `k ≤ N`
(`TauCeti.exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq`). The derivatives are bounded on the
compact unit sphere, and rescaling `ξ` to the sphere gives the factor `‖ξ‖⁻¹ ^ k`.

This is Mihlin's condition for a Fourier multiplier symbol, so every symbol that is smooth away
from the origin and homogeneous of degree `0` is an `Lᵖ` multiplier for `1 < p < ∞`.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV, §3.
-/

public section

open scoped NNReal
open Metric

namespace TauCeti

/-- **Homogeneous maps of degree zero satisfy Mihlin's condition.** Let `m` be a map on a proper
(for instance finite-dimensional) real normed space that is `C^N` away from the origin and
homogeneous of degree `0`, that is `m (t • ξ) = m ξ` for every `t > 0`. Then there is a constant
`A` with `‖D^k m ξ‖ ≤ A / ‖ξ‖ ^ k` for every `k ≤ N` and every `ξ ≠ 0`. -/
theorem exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq {W G : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [ProperSpace W] [NormedAddCommGroup G] [NormedSpace ℝ G] {m : W → G}
    {N : ℕ} (hm : ContDiffOn ℝ N m {0}ᶜ) (hhom : ∀ t : ℝ, 0 < t → ∀ ξ, m (t • ξ) = m ξ) :
    ∃ A : ℝ≥0, ∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ A / ‖ξ‖ ^ k := by
  -- Each iterated derivative is bounded on the unit sphere, which is compact.
  have hbd : ∀ k ≤ N, ∃ C : ℝ, ∀ ξ ∈ sphere (0 : W) 1, ‖iteratedFDeriv ℝ k m ξ‖ ≤ C := by
    intro k hk
    have hc : ContinuousOn (iteratedFDeriv ℝ k m) {0}ᶜ :=
      (hm.continuousOn_iteratedFDerivWithin (mod_cast hk)
        isOpen_compl_singleton.uniqueDiffOn).congr
        (iteratedFDerivWithin_of_isOpen k isOpen_compl_singleton).symm
    exact (isCompact_sphere 0 1).exists_bound_of_continuousOn
      (hc.mono fun ξ hξ ↦ ne_zero_of_mem_unit_sphere ⟨ξ, hξ⟩)
  choose! C hC using hbd
  refine ⟨∑ k ∈ Finset.range (N + 1), (C k).toNNReal, fun k hk ξ hξ ↦ ?_⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  -- By homogeneity `m = m ∘ g` for `g = ‖ξ‖⁻¹ • ·`, and `g ξ` lies on the unit sphere.
  set g : W ≃L[ℝ] W := ContinuousLinearEquiv.smulLeft (Units.mk0 ‖ξ‖⁻¹ (inv_ne_zero hn.ne'))
  have hg : ∀ x, g x = ‖ξ‖⁻¹ • x := fun x ↦ by
    rw [ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def, Units.val_mk0]
  have hmg : m ∘ g = m := funext fun x ↦ by simp [hg, hhom _ (inv_pos.2 hn)]
  have hgξ : g ξ ∈ sphere (0 : W) 1 := by simp [hg, norm_smul, hn.ne']
  have hgn : ‖(g : W →L[ℝ] W)‖ ≤ ‖ξ‖⁻¹ :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ by simp [hg, norm_smul]
  have hCk : C k ≤ ∑ k ∈ Finset.range (N + 1), ((C k).toNNReal : ℝ) :=
    (Real.le_coe_toNNReal _).trans (Finset.single_le_sum (f := fun k ↦ ((C k).toNNReal : ℝ))
      (fun _ _ ↦ NNReal.coe_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
  rw [NNReal.coe_sum, le_div_iff₀ (by positivity)]
  calc ‖iteratedFDeriv ℝ k m ξ‖ * ‖ξ‖ ^ k
      ≤ ‖(g : W →L[ℝ] W)‖ ^ k * ‖iteratedFDeriv ℝ k m (g ξ)‖ * ‖ξ‖ ^ k := by
        gcongr
        simpa only [hmg] using g.norm_iteratedFDeriv_comp_right_le m ξ k
    _ ≤ ‖ξ‖⁻¹ ^ k * C k * ‖ξ‖ ^ k := by
        gcongr
        exact hC k hk _ hgξ
    _ = C k := by rw [mul_right_comm, ← mul_pow, inv_mul_cancel₀ hn.ne', one_pow, one_mul]
    _ ≤ _ := hCk

end TauCeti
