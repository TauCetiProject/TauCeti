/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv

/-!
# Iterated derivatives of homogeneous maps

Let `m` be a map on a proper (for instance finite-dimensional) real normed space that is `C^N`
away from the origin and positively homogeneous of degree `d ∈ ℤ` there, that is
`m (t • ξ) = t ^ d • m ξ` for every `t > 0` and `ξ ≠ 0`. Then its iterated derivatives satisfy
`‖D^k m ξ‖ ≤ A ‖ξ‖ ^ (d - k)` for `k ≤ N`
(`TauCeti.exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq`).
The derivatives are bounded on the compact unit sphere, and rescaling `ξ` to the sphere gives the
factor `‖ξ‖ ^ d ‖ξ‖⁻¹ ^ k`.

For `d = 0` this is Mihlin's condition for a Fourier multiplier symbol
(`TauCeti.exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq`), so every symbol that is smooth away
from the origin and homogeneous of degree `0` is an `Lᵖ` multiplier for `1 < p < ∞`.

For `d ≤ 0` the derivatives are bounded away from any ball around the origin. Hence a `C^N` map
that agrees with such a homogeneous map near every point outside a ball has bounded derivatives
through order `N` on the whole space (`TauCeti.exists_norm_iteratedFDeriv_le_of_eventuallyEq`).
This applies to smooth fields whose ends are the angular forms and phases of polar coordinates.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV, §3.
-/

public section

open scoped NNReal Topology
open Metric

namespace TauCeti

variable {W G : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Iterated derivatives of homogeneous maps.** Let `m` be a map on a proper (for instance
finite-dimensional) real normed space that is `C^N` away from the origin and homogeneous of degree
`d ∈ ℤ` there, that is `m (t • ξ) = t ^ d • m ξ` for every `t > 0` and `ξ ≠ 0`. Then there is a
constant `A` with `‖D^k m ξ‖ ≤ A ‖ξ‖ ^ (d - k)` for every `k ≤ N` and every `ξ ≠ 0`. -/
theorem exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq {m : W → G} {N : ℕ} {d : ℤ}
    (hm : ContDiffOn ℝ N m {0}ᶜ) (hhom : ∀ t : ℝ, 0 < t → ∀ ξ ≠ 0, m (t • ξ) = t ^ d • m ξ) :
    ∃ A : ℝ≥0, ∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ A * ‖ξ‖ ^ (d - k) := by
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
  -- Near `ξ`, homogeneity gives `m = ‖ξ‖ ^ d • m ∘ g` for `g = ‖ξ‖⁻¹ • ·`, and `g ξ` lies on the
  -- unit sphere.
  set g : W ≃L[ℝ] W := ContinuousLinearEquiv.smulLeft (Units.mk0 ‖ξ‖⁻¹ (inv_ne_zero hn.ne'))
  have hg : ∀ x, g x = ‖ξ‖⁻¹ • x := fun x ↦ by
    rw [ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def, Units.val_mk0]
  have hmg : m =ᶠ[𝓝 ξ] fun x ↦ ‖ξ‖ ^ d • (m ∘ g) x := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hξ] with x hx
    have hgx : g x ≠ 0 := by
      rw [hg]
      exact smul_ne_zero (inv_ne_zero hn.ne') hx
    rw [Function.comp_apply, ← hhom _ hn _ hgx, hg, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hgξ : g ξ ∈ sphere (0 : W) 1 := by simp [hg, norm_smul, hn.ne']
  have hgn : ‖(g : W →L[ℝ] W)‖ ≤ ‖ξ‖⁻¹ :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ by simp [hg, norm_smul]
  have hmgc : ContDiffAt ℝ k (m ∘ g) ξ :=
    ((hm.contDiffAt (isOpen_compl_singleton.mem_nhds
      (ne_zero_of_mem_unit_sphere ⟨_, hgξ⟩))).comp ξ g.contDiff.contDiffAt).of_le (mod_cast hk)
  have hCk : C k ≤ ∑ k ∈ Finset.range (N + 1), ((C k).toNNReal : ℝ) :=
    (Real.le_coe_toNNReal _).trans (Finset.single_le_sum (f := fun k ↦ ((C k).toNNReal : ℝ))
      (fun _ _ ↦ NNReal.coe_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
  rw [(hmg.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_const_smul_apply' hmgc, norm_smul,
    Real.norm_of_nonneg (zpow_nonneg hn.le d), NNReal.coe_sum]
  calc ‖ξ‖ ^ d * ‖iteratedFDeriv ℝ k (m ∘ g) ξ‖
      ≤ ‖ξ‖ ^ d * (‖(g : W →L[ℝ] W)‖ ^ k * ‖iteratedFDeriv ℝ k m (g ξ)‖) := by
        gcongr
        exact g.norm_iteratedFDeriv_comp_right_le m ξ k
    _ ≤ ‖ξ‖ ^ d * (‖ξ‖⁻¹ ^ k * C k) := by
        gcongr
        exact hC k hk _ hgξ
    _ = C k * ‖ξ‖ ^ (d - k) := by
        rw [zpow_sub₀ hn.ne', zpow_natCast, inv_pow, div_eq_mul_inv]
        ring
    _ ≤ _ := by gcongr

/-- **Homogeneous maps of degree zero satisfy Mihlin's condition.** Let `m` be a map on a proper
(for instance finite-dimensional) real normed space that is `C^N` away from the origin and
homogeneous of degree `0` there, that is `m (t • ξ) = m ξ` for every `t > 0` and `ξ ≠ 0`. Then
there is a constant `A` with `‖D^k m ξ‖ ≤ A / ‖ξ‖ ^ k` for every `k ≤ N` and every `ξ ≠ 0`. -/
theorem exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq {m : W → G} {N : ℕ}
    (hm : ContDiffOn ℝ N m {0}ᶜ) (hhom : ∀ t : ℝ, 0 < t → ∀ ξ ≠ 0, m (t • ξ) = m ξ) :
    ∃ A : ℝ≥0, ∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ A / ‖ξ‖ ^ k := by
  obtain ⟨A, hA⟩ := exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq (d := 0) hm
    fun t ht ξ hξ ↦ by rw [zpow_zero, one_smul, hhom t ht ξ hξ]
  refine ⟨A, fun k hk ξ hξ ↦ (hA k hk ξ hξ).trans_eq ?_⟩
  rw [zero_sub, zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- **Bounded derivatives from a homogeneous end.** Let `F` be a `C^N` map on a proper real normed
space which, near every point outside the ball of radius `R`, agrees with a map `m` that is `C^N`
away from the origin and homogeneous of degree `d ≤ 0` there. Then the iterated derivatives of `F`
through order `N` are bounded on the whole space. -/
theorem exists_norm_iteratedFDeriv_le_of_eventuallyEq {F m : W → G} {N : ℕ} {d : ℤ} (hd : d ≤ 0)
    (hF : ContDiff ℝ N F) (hm : ContDiffOn ℝ N m {0}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ ξ ≠ 0, m (t • ξ) = t ^ d • m ξ) {R : ℝ}
    (hFm : ∀ ξ, R < ‖ξ‖ → F =ᶠ[𝓝 ξ] m) :
    ∃ M : ℝ≥0, ∀ k ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ k F ξ‖ ≤ M := by
  obtain ⟨A, hA⟩ := exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq hm hhom
  -- On a closed ball the derivatives are continuous, hence bounded.
  have hbd : ∀ k ≤ N, ∃ C : ℝ, ∀ ξ ∈ closedBall (0 : W) (max R 1),
      ‖iteratedFDeriv ℝ k F ξ‖ ≤ C := fun k hk ↦
    (isCompact_closedBall 0 (max R 1)).exists_bound_of_continuousOn
      (hF.continuous_iteratedFDeriv (mod_cast hk)).continuousOn
  choose! C hC using hbd
  refine ⟨A + ∑ k ∈ Finset.range (N + 1), (C k).toNNReal, fun k hk ξ ↦ ?_⟩
  have hCk : C k ≤ ∑ k ∈ Finset.range (N + 1), ((C k).toNNReal : ℝ) :=
    (Real.le_coe_toNNReal _).trans (Finset.single_le_sum (f := fun k ↦ ((C k).toNNReal : ℝ))
      (fun _ _ ↦ NNReal.coe_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
  push_cast
  by_cases hξ : ‖ξ‖ ≤ max R 1
  · exact (hC k hk ξ (mem_closedBall_zero_iff.2 hξ)).trans (hCk.trans (le_add_of_nonneg_left
      A.coe_nonneg))
  -- Outside the ball `F` agrees with `m` near `ξ`, and `‖ξ‖ ^ (d - k) ≤ 1` since `‖ξ‖ ≥ 1`.
  rw [not_le, max_lt_iff] at hξ
  have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans hξ.2)
  rw [((hFm ξ hξ.1).iteratedFDeriv ℝ k).eq_of_nhds]
  calc ‖iteratedFDeriv ℝ k m ξ‖ ≤ A * ‖ξ‖ ^ (d - k) := hA k hk ξ hξ0
    _ ≤ A * 1 := by
        gcongr
        exact zpow_le_one_of_nonpos₀ hξ.2.le (by omega)
    _ ≤ _ := by
        rw [mul_one]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _)

end TauCeti
