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
away from the origin and homogeneous of degree `d ∈ ℤ` there, that is `m (t • ξ) = t ^ d • m ξ`
for every `t > 0` and `ξ ≠ 0`. Then its iterated derivatives satisfy
`‖D^k m ξ‖ ≤ A ‖ξ‖ ^ (d - k)` for `k ≤ N`
(`TauCeti.exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq`).
The derivatives are bounded on the compact unit sphere, and rescaling `ξ` to the sphere gives the
factor `‖ξ‖ ^ (d - k)`.

In degree `0` this is `‖D^k m ξ‖ ≤ A / ‖ξ‖ ^ k`
(`TauCeti.exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq`), Mihlin's condition for a Fourier
multiplier symbol, so every symbol that is smooth away from the origin and homogeneous of degree
`0` is an `Lᵖ` multiplier for `1 < p < ∞`.

In degree `d ≤ 0` the derivatives are bounded away from the origin. Hence a globally `C^N` map that
agrees with such a homogeneous map outside a ball has bounded derivatives of every order up to `N`
(`TauCeti.exists_norm_iteratedFDeriv_le_of_eq_of_smul_eq`). Examples are the winding phases
`(z / |z|) ^ m` and the angular form `dθ` on the plane, after a cutoff near the origin.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV, §3.
-/

public section

open scoped NNReal Topology
open Metric

namespace TauCeti

/-- **Derivative bounds for homogeneous maps.** Let `m` be a map on a proper (for instance
finite-dimensional) real normed space that is `C^N` away from the origin and homogeneous of degree
`d` there, that is `m (t • ξ) = t ^ d • m ξ` for every `t > 0` and `ξ ≠ 0`. Then there is a
constant `A` with `‖D^k m ξ‖ ≤ A * ‖ξ‖ ^ (d - k)` for every `k ≤ N` and every `ξ ≠ 0`. -/
theorem exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq {W G : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [ProperSpace W] [NormedAddCommGroup G] [NormedSpace ℝ G] {m : W → G}
    {N : ℕ} {d : ℤ} (hm : ContDiffOn ℝ N m {0}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ ξ ≠ 0, m (t • ξ) = t ^ d • m ξ) :
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
  -- By homogeneity `m ∘ g = ‖ξ‖ ^ (-d) • m` near `ξ` for `g = ‖ξ‖⁻¹ • ·`, and `g ξ` lies on the
  -- unit sphere.
  set g : W ≃L[ℝ] W := ContinuousLinearEquiv.smulLeft (Units.mk0 ‖ξ‖⁻¹ (inv_ne_zero hn.ne'))
  have hg : ∀ x, g x = ‖ξ‖⁻¹ • x := fun x ↦ by
    rw [ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def, Units.val_mk0]
  have hmg : m ∘ g =ᶠ[𝓝 ξ] fun x ↦ ‖ξ‖⁻¹ ^ d • m x := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hξ] with x hx
    simp [hg, hhom _ (inv_pos.2 hn) x hx]
  have hgξ : g ξ ∈ sphere (0 : W) 1 := by simp [hg, norm_smul, hn.ne']
  have hgn : ‖(g : W →L[ℝ] W)‖ ≤ ‖ξ‖⁻¹ :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ by simp [hg, norm_smul]
  have hCk : C k ≤ ∑ k ∈ Finset.range (N + 1), ((C k).toNNReal : ℝ) :=
    (Real.le_coe_toNNReal _).trans (Finset.single_le_sum (f := fun k ↦ ((C k).toNNReal : ℝ))
      (fun _ _ ↦ NNReal.coe_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
  have hmξ : ContDiffAt ℝ k m ξ :=
    (hm.contDiffAt (isOpen_compl_singleton.mem_nhds hξ)).of_le (mod_cast hk)
  have hD : ‖ξ‖ ^ (-d) * ‖iteratedFDeriv ℝ k m ξ‖ = ‖iteratedFDeriv ℝ k (m ∘ g) ξ‖ := by
    rw [hmg.iteratedFDeriv ℝ k |>.eq_of_nhds, iteratedFDeriv_const_smul_apply' hmξ, norm_smul,
      inv_zpow', Real.norm_of_nonneg (by positivity)]
  calc ‖iteratedFDeriv ℝ k m ξ‖ = ‖ξ‖ ^ d * (‖ξ‖ ^ (-d) * ‖iteratedFDeriv ℝ k m ξ‖) := by
        rw [← mul_assoc, ← zpow_add₀ hn.ne', add_neg_cancel, zpow_zero, one_mul]
    _ ≤ ‖ξ‖ ^ d * (‖ξ‖⁻¹ ^ k * C k) := by
        rw [hD]
        gcongr
        calc ‖iteratedFDeriv ℝ k (m ∘ g) ξ‖
            ≤ ‖(g : W →L[ℝ] W)‖ ^ k * ‖iteratedFDeriv ℝ k m (g ξ)‖ :=
              g.norm_iteratedFDeriv_comp_right_le m ξ k
          _ ≤ ‖ξ‖⁻¹ ^ k * C k := by
              gcongr
              exact hC k hk _ hgξ
    _ = C k * ‖ξ‖ ^ (d - k) := by
        rw [zpow_sub₀ hn.ne', zpow_natCast, inv_pow, div_eq_mul_inv]
        ring
    _ ≤ _ := by
        rw [NNReal.coe_sum]
        gcongr

/-- **Homogeneous maps of degree zero satisfy Mihlin's condition.** Let `m` be a map on a proper
(for instance finite-dimensional) real normed space that is `C^N` away from the origin and
homogeneous of degree `0`, that is `m (t • ξ) = m ξ` for every `t > 0`. Then there is a constant
`A` with `‖D^k m ξ‖ ≤ A / ‖ξ‖ ^ k` for every `k ≤ N` and every `ξ ≠ 0`. -/
theorem exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq {W G : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [ProperSpace W] [NormedAddCommGroup G] [NormedSpace ℝ G] {m : W → G}
    {N : ℕ} (hm : ContDiffOn ℝ N m {0}ᶜ) (hhom : ∀ t : ℝ, 0 < t → ∀ ξ, m (t • ξ) = m ξ) :
    ∃ A : ℝ≥0, ∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ A / ‖ξ‖ ^ k := by
  obtain ⟨A, hA⟩ := exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq (d := 0) hm
    fun t ht ξ _ ↦ by rw [zpow_zero, one_smul, hhom t ht ξ]
  exact ⟨A, fun k hk ξ hξ ↦ (hA k hk ξ hξ).trans_eq (by rw [zero_sub, zpow_neg, zpow_natCast,
    div_eq_mul_inv])⟩

/-- **Bounded derivatives from homogeneity at infinity.** A `C^N` map `f` on a proper real normed
space that agrees outside a ball with a map `m` which is `C^N` away from the origin and homogeneous
of degree `d ≤ 0` there has bounded derivatives of every order `k ≤ N`. -/
theorem exists_norm_iteratedFDeriv_le_of_eq_of_smul_eq {W G : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [ProperSpace W] [NormedAddCommGroup G] [NormedSpace ℝ G] {f m : W → G}
    {N : ℕ} {d : ℤ} (hd : d ≤ 0) (hf : ContDiff ℝ N f) (hm : ContDiffOn ℝ N m {0}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ ξ ≠ 0, m (t • ξ) = t ^ d • m ξ) {R : ℝ}
    (hfm : ∀ ξ, R < ‖ξ‖ → f ξ = m ξ) :
    ∀ k ≤ N, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k f ξ‖ ≤ C := by
  obtain ⟨A, hA⟩ := exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq hm hhom
  intro k hk
  -- On the compact ball of radius `max R 1` the derivative is continuous, hence bounded.
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : W) (max R 1)).exists_bound_of_continuousOn
    ((hf.continuous_iteratedFDeriv (mod_cast hk)).continuousOn (s := closedBall 0 (max R 1)))
  refine ⟨max C A, fun ξ ↦ ?_⟩
  by_cases hξ : ‖ξ‖ ≤ max R 1
  · exact (hC ξ (mem_closedBall_zero_iff.2 hξ)).trans (le_max_left _ _)
  -- Outside it `f = m` near `ξ`, and `‖ξ‖ ^ (d - k) ≤ 1` because `‖ξ‖ ≥ 1`.
  rw [not_le] at hξ
  have hfm' : f =ᶠ[𝓝 ξ] m := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
      ((le_max_left R 1).trans_lt hξ)] with x hx using hfm x hx
  have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans ((le_max_right R 1).trans_lt hξ))
  rw [hfm'.iteratedFDeriv ℝ k |>.eq_of_nhds]
  refine (hA k hk ξ hξ0).trans ((mul_le_of_le_one_right A.2 ?_).trans (le_max_right _ _))
  exact zpow_le_one_of_nonpos₀ ((le_max_right R 1).trans hξ.le) (by omega)

end TauCeti
