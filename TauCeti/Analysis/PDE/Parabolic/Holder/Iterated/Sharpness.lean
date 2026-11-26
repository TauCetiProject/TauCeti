/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.HeatEquation
import TauCeti.Analysis.Holder.Examples

/-!
# The initial datum `|x|^{3+β}`: the data space of the Cauchy problem is sharp

For every order `k` and `0 < α < 1`, the heat equation has an isomorphism
`u ↦ (∂ₜu - Δu, u(·, 0))` from `C_{par,b}^{k+2+α}` onto `C_{par,b}^{k+α} × C_b^{k+2,α}`
(`TauCeti.ParabolicCkHolderSpace.heatInitialDataCLE`), and so does every uniformly parabolic
equation with coefficients in `C_{par,b}^{k+α}`
(`TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE`). This file shows on the line, at order
`k = 1`, that the initial datum cannot be taken in a larger space than `C_b^{3,α}`.

Let `0 < β < α` and let `χ` be a `C⁴` cutoff with compact support. The datum
`u₀(x) = χ(x) |x|^{3+β}` has third derivative `(3 + β)(2 + β)(1 + β) sign(x) |x|^β` near the
origin wherever `χ = 1` there, which is `β`-Hölder but not `α`-Hölder at `0`. So

* `u₀ ∈ C_b^{3,β}` for `β ≤ 1` (`TauCeti.exists_ckHolderSpace_coe_eq_mul_abs_rpow`, in
  `Holder/Examples.lean`);
* no element of `C_b^{3,α}` agrees with `|x|^{3+β}` near `0`
  (`TauCeti.not_exists_ckHolderSpace_coe_eq_of_eventuallyEq_abs_rpow`, ibid.);
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
