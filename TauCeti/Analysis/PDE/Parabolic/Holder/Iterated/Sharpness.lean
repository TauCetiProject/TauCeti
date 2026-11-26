/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.HeatEquation
import Mathlib.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Holder.Localization
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Holder
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Regularity

/-!
# The initial datum `|x|^{3+β}`: the data space of the Cauchy problem is sharp

For every order `k` and `0 < α < 1`, the heat equation, and more generally every uniformly
parabolic equation with coefficients in `C_{par,b}^{k+α}`, has an isomorphism
`u ↦ (∂ₜu - Δu, u(·, 0))` from `C_{par,b}^{k+2+α}` onto `C_{par,b}^{k+α} × C_b^{k+2,α}`
(`TauCeti.ParabolicCkHolderSpace.heatInitialDataCLE`). This file shows on the line, at order
`k = 1`, that the initial datum cannot be taken in a larger space than `C_b^{3,α}`.

Let `0 < β < α` and let `χ` be a `C⁴` cutoff with compact support. The datum
`u₀(x) = χ(x) |x|^{3+β}` has third derivative `(3 + β)(2 + β)(1 + β) sign(x) |x|^β` near the
origin wherever `χ = 1` there, which is `β`-Hölder but not `α`-Hölder at `0`. So

* `u₀ ∈ C_b^{3,β}` for `β ≤ 1` (`TauCeti.exists_ckHolderSpace_coe_eq_mul_abs_rpow`);
* no element of `C_b^{3,α}` agrees with `|x|^{3+β}` near `0`
  (`TauCeti.not_exists_ckHolderSpace_coe_eq_of_eventuallyEq_abs_rpow`);
* hence no map in `C_{par,b}^{3+α}` has such a time slice
  (`TauCeti.not_exists_parabolicCkHolderSpace_slabMk_eq_of_eventuallyEq_abs_rpow`), since the
  slices of a map of order `3 + α` lie in `C_b^{3,α}`;
* the solution of the heat equation with datum `u₀` lies in `C_{par,b}^{3+β}` but not in
  `C_{par,b}^{3+α}`
  (`TauCeti.exists_heatInitialDataL_fst_eq_zero_and_not_exists_parabolicCkHolderSpace_coe_eq`).

Thus the solution is no more regular than its datum, and the order-one isomorphism at exponent
`α` does not extend to data in `C_b^{3,β}`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (the heat equation in parabolic Hölder spaces).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section

namespace TauCeti

open Filter Metric Set Topology ParabolicSpaceTime
open scoped NNReal

/-! ### The power `|x|^{3+β}` on the line -/

section Line

/-- The first three derivatives of `|x|^{3+β}`, for `β > 0`; the third is
`(3 + β)(2 + β)(1 + β) |x|^{β-1} x`. -/
private theorem iteratedDeriv_abs_rpow_three_add {β : ℝ} (hβ : 0 < β) :
    iteratedDeriv 1 (fun x : ℝ ↦ |x| ^ (3 + β)) = (fun x ↦ (3 + β) * (|x| ^ (1 + β) * x)) ∧
    iteratedDeriv 2 (fun x : ℝ ↦ |x| ^ (3 + β)) =
      (fun x ↦ (3 + β) * (2 + β) * |x| ^ (1 + β)) ∧
    iteratedDeriv 3 (fun x : ℝ ↦ |x| ^ (3 + β)) =
      (fun x ↦ (3 + β) * (2 + β) * (1 + β) * (|x| ^ (β - 1) * x)) := by
  have h1 : iteratedDeriv 1 (fun x : ℝ ↦ |x| ^ (3 + β)) =
      (fun x ↦ (3 + β) * (|x| ^ (1 + β) * x)) := by
    funext x
    rw [iteratedDeriv_one, (hasDerivAt_abs_rpow x (p := 3 + β) (by linarith)).deriv,
      show 3 + β - 2 = 1 + β by ring, mul_assoc]
  have h2 : iteratedDeriv 2 (fun x : ℝ ↦ |x| ^ (3 + β)) =
      (fun x ↦ (3 + β) * (2 + β) * |x| ^ (1 + β)) := by
    funext x
    rw [iteratedDeriv_succ, h1,
      (((hasDerivAt_abs_rpow_mul_self (p := 1 + β) (by linarith) x)).const_mul (3 + β)).deriv]
    ring
  refine ⟨h1, h2, ?_⟩
  funext x
  rw [iteratedDeriv_succ, h2,
    ((hasDerivAt_abs_rpow x (p := 1 + β) (by linarith)).const_mul ((3 + β) * (2 + β))).deriv,
    show 1 + β - 2 = β - 1 by ring]
  ring

/-- `|x|^{3+β}` is `C³`, for `0 < β ≤ 1`. -/
private theorem contDiff_abs_rpow_three_add {β : ℝ≥0} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    ContDiff ℝ 3 (fun x : ℝ ↦ |x| ^ (3 + (β : ℝ))) := by
  have hβ' : (0 : ℝ) < β := hβ₀
  obtain ⟨h1, h2, h3⟩ := iteratedDeriv_abs_rpow_three_add hβ'
  have hd1 : Differentiable ℝ (fun x : ℝ ↦ (3 + (β : ℝ)) * (|x| ^ (1 + (β : ℝ)) * x)) :=
    fun x ↦ ((hasDerivAt_abs_rpow_mul_self (by linarith) x).const_mul _).differentiableAt
  have hd2 : Differentiable ℝ (fun x : ℝ ↦ (3 + (β : ℝ)) * (2 + β) * |x| ^ (1 + (β : ℝ))) :=
    fun x ↦ ((hasDerivAt_abs_rpow x (by linarith)).const_mul _).differentiableAt
  have hd0 : Differentiable ℝ (fun x : ℝ ↦ |x| ^ (3 + (β : ℝ))) :=
    fun x ↦ (hasDerivAt_abs_rpow x (by linarith)).differentiableAt
  have hc3 : Continuous (fun x : ℝ ↦
      (3 + (β : ℝ)) * (2 + β) * (1 + β) * (|x| ^ ((β : ℝ) - 1) * x)) :=
    continuous_const.mul ((Real.holderWith_abs_rpow_sub_one_mul_self hβ₀ hβ₁).continuous hβ₀)
  refine contDiff_nat_iff_iteratedDeriv.2 ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩
  · interval_cases m
    · simpa using hd0.continuous
    · simpa [h1] using hd1.continuous
    · simpa [h2] using hd2.continuous
    · simpa [h3] using hc3
  · interval_cases m
    · simpa using hd0
    · simpa [h1] using hd1
    · simpa [h2] using hd2

/-- The third derivative of `|x|^{3+β}` is globally `β`-Hölder, for `0 < β ≤ 1`. -/
private theorem memHolder_iteratedFDeriv_abs_rpow_three_add {β : ℝ≥0} (hβ₀ : 0 < β)
    (hβ₁ : β ≤ 1) : MemHolder β (iteratedFDeriv ℝ 3 (fun x : ℝ ↦ |x| ^ (3 + (β : ℝ)))) := by
  rw [iteratedFDeriv_eq_equiv_comp, (iteratedDeriv_abs_rpow_three_add (β := β) hβ₀).2.2]
  exact ⟨_, (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin 3) ℝ).isometry.comp_holderWith
    ((Real.holderWith_abs_rpow_sub_one_mul_self hβ₀ hβ₁).smul
      ((3 + (β : ℝ)) * (2 + β) * (1 + β)))⟩

/-- **`χ |x|^{3+β}` lies in `C_b^{3,β}`.** For `0 < β ≤ 1` and a compactly supported `C⁴`
function `χ` on the line, the map `x ↦ χ(x) |x|^{3+β}` lies in `C_b^{3,β}(ℝ)`. -/
theorem exists_ckHolderSpace_coe_eq_mul_abs_rpow {β : ℝ≥0} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 4 χ) (hχc : HasCompactSupport χ) :
    ∃ g : CkHolderSpace 3 β ℝ ℝ, ⇑g = fun x ↦ χ x * |x| ^ (3 + (β : ℝ)) := by
  obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.subset_ball (0 : ℝ)
  have hf := contDiff_abs_rpow_three_add hβ₀ hβ₁
  obtain ⟨M, -, hM⟩ := hf.contDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen
    isOpen_univ (isCompact_closedBall (0 : ℝ) R) (subset_univ _)
  obtain ⟨N, -, hN⟩ := hχc.exists_bound_iteratedFDeriv_of_contDiff (n := 4) hχ
  obtain ⟨H, hH⟩ := memHolder_iteratedFDeriv_abs_rpow_three_add hβ₀ hβ₁
  refine ⟨CkHolderSpace.cutoff (M := M.toNNReal) (N := N.toNNReal) hf.contDiffOn
    (hχ.of_le (by norm_num)) isOpen_ball (convex_ball 0 R) hR hβ₁
    (fun i hi x hx ↦ (hM i hi x (ball_subset_closedBall hx)).trans (Real.le_coe_toNNReal M))
    (fun i hi x ↦ (hN i hi x).trans (Real.le_coe_toNNReal N)) (hH.holderOnWith _), ?_⟩
  rw [CkHolderSpace.coe_cutoff]
  simp only [smul_eq_mul]

/-- **`|x|^{3+β}` is not `C^{3,α}` at `0` for `α > β`.** For `0 < β < α`, no element of
`C_b^{3,α}(ℝ)` agrees with `|x|^{3+β}` near `0`: its third derivative
`(3 + β)(2 + β)(1 + β) sign(x) |x|^β` is not `α`-Hölder at the origin. -/
theorem not_exists_ckHolderSpace_coe_eq_of_eventuallyEq_abs_rpow {β α : ℝ≥0} (hβ : 0 < β)
    (hβα : β < α) {g : ℝ → ℝ} (hg : g =ᶠ[𝓝 0] fun x ↦ |x| ^ (3 + (β : ℝ))) :
    ¬ ∃ G : CkHolderSpace 3 α ℝ ℝ, ⇑G = g := by
  rintro ⟨G, rfl⟩
  obtain ⟨C, hC⟩ := G.memHolder_iteratedFDeriv
  have hβ' : (0 : ℝ) < β := hβ
  have hαβ : (0 : ℝ) < α - β := sub_pos.2 (by exact_mod_cast hβα)
  have hc : (0 : ℝ) < (3 + β) * (2 + β) * (1 + β) := by positivity
  have hD := hg.iteratedFDeriv ℝ 3
  obtain ⟨t, ⟨hCt, ht⟩, htD⟩ := (((eventually_mul_rpow_lt_nhdsGT_zero hαβ C hc).and
    eventually_mem_nhdsWithin).and (hD.filter_mono nhdsWithin_le_nhds)).exists
  have ht : 0 < t := ht
  -- The Hölder bound of the third derivative between `t` and `0` reads
  -- `(3 + β)(2 + β)(1 + β) t ^ β ≤ C t ^ α`.
  have h1 := hC.dist_le t 0
  rw [htD, hD.self_of_nhds, iteratedFDeriv_eq_equiv_comp, Function.comp_apply,
    Function.comp_apply, LinearIsometryEquiv.dist_map,
    (iteratedDeriv_abs_rpow_three_add hβ').2.2] at h1
  beta_reduce at h1
  rw [abs_of_pos ht, ← Real.rpow_eq_rpow_sub_one_mul ht.le hβ'.ne', mul_zero, mul_zero,
    Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, abs_of_pos ht, abs_of_pos (by positivity)]
    at h1
  have hsplit : t ^ (α : ℝ) = t ^ ((α : ℝ) - β) * t ^ (β : ℝ) := by
    rw [← Real.rpow_add ht, sub_add_cancel]
  rw [hsplit, ← mul_assoc] at h1
  linarith [mul_lt_mul_of_pos_right hCt (Real.rpow_pos_of_pos ht (β : ℝ))]

end Line

/-! ### Parabolic Hölder maps and the heat equation -/

/-- **No map of order `3 + α` has a slice `|x|^{3+β}`.** For `0 < β < α`, no map in
`C_{par,b}^{3+α}(ℝ × [a, b])` has, at any time `t`, a spatial slice that agrees with
`|x|^{3+β}` near `0`, since every slice lies in `C_b^{3,α}`. -/
theorem not_exists_parabolicCkHolderSpace_slabMk_eq_of_eventuallyEq_abs_rpow {β α : ℝ≥0}
    (hβ : 0 < β) (hβα : β < α) {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : g =ᶠ[𝓝 0] fun x ↦ |x| ^ (3 + (β : ℝ))) (t : Icc a b) :
    ¬ ∃ v : ParabolicCkHolderSpace 3 α ℝ ℝ hab, ∀ x, v (slabMk x t) = g x := by
  rintro ⟨v, hv⟩
  exact not_exists_ckHolderSpace_coe_eq_of_eventuallyEq_abs_rpow hβ hβα hg
    ⟨v.spatialTrace t, funext fun x ↦ by rw [ParabolicCkHolderSpace.spatialTrace_apply, hv]⟩

/-- **The data space of the order-one Cauchy problem is sharp.** Let `0 < β < 1`, `β < α`,
`T > 0`, and let `χ` be a compactly supported `C⁴` function on the line equal to `1` near `0`.
The heat equation `∂ₜu - u'' = 0` on `ℝ × [0, T]` with initial datum `χ(x) |x|^{3+β}`, which
lies in `C_b^{3,β}` but not in `C_b^{3,α}`, has a solution `u` in `C_{par,b}^{3+β}`, and no map in
`C_{par,b}^{3+α}` has the values of `u`. -/
theorem exists_heatInitialDataL_fst_eq_zero_and_not_exists_parabolicCkHolderSpace_coe_eq
    {β α T : ℝ≥0} (hβ₀ : 0 < β) (hβ₁ : β < 1) (hβα : β < α) (hT : (0 : ℝ) < T)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 4 χ) (hχc : HasCompactSupport χ) (hχ₁ : χ =ᶠ[𝓝 0] 1) :
    ∃ u : ParabolicCkHolderSpace 3 β ℝ ℝ hT,
      (ParabolicCkHolderSpace.heatInitialDataL 1 hβ₁.le hT u).1 = 0 ∧
      (∀ x, u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) = χ x * |x| ^ (3 + (β : ℝ))) ∧
      ¬ ∃ v : ParabolicCkHolderSpace 3 α ℝ ℝ hT, ⇑v = ⇑u := by
  obtain ⟨g, hg⟩ := exists_ckHolderSpace_coe_eq_mul_abs_rpow hβ₀ hβ₁.le hχ hχc
  have hu := ParabolicCkHolderSpace.heatInitialDataL_heatSolutionL (k := 1) (hT := hT) hβ₀ hβ₁
    (0, g)
  set u := ParabolicCkHolderSpace.heatSolutionL 1 hβ₀ hβ₁ hT (0, g)
  have htrace (x : ℝ) : u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) = χ x * |x| ^ (3 + (β : ℝ)) := by
    have h := congrArg (fun d ↦ d.2 x) hu
    simp only [ParabolicCkHolderSpace.heatInitialDataL_snd,
      ParabolicCkHolderSpace.spatialTrace_apply] at h
    rw [h, hg]
  refine ⟨u, by rw [hu], htrace, fun ⟨v, hv⟩ ↦ ?_⟩
  refine not_exists_parabolicCkHolderSpace_slabMk_eq_of_eventuallyEq_abs_rpow hβ₀ hβα hT
    (g := fun x ↦ χ x * |x| ^ (3 + (β : ℝ))) ?_ ⟨0, left_mem_Icc.2 hT.le⟩
    ⟨v, fun x ↦ by rw [hv, htrace]⟩
  filter_upwards [hχ₁] with x hx
  simp [hx]

end TauCeti
