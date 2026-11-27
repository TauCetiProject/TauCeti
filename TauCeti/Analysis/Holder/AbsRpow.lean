/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.CompLinear
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Holder.Localization
import TauCeti.Analysis.SpecialFunctions.Pow.Regularity

/-!
# The power `|x|^(k + β)` in the bounded Hölder spaces

For `k : ℕ` and `0 < β ≤ 1`, the function `|x|^(k + β)` on `ℝ` is `C^k`, and its `k`-th derivative
is `c · sgn(x)^k |x|^β` with `c = (k + β)(k + β - 1) ⋯ (β + 1)`. This file shows that it sits
exactly in the bounded Hölder space `C_b^{k,β}` near the origin and in no smaller one:

* **Membership** (`TauCeti.exists_ckHolderSpace_coe_eq_mul_abs_rpow`). For a compactly supported
  `C^{k+1}` cutoff `χ`, the function `χ(x) |x|^(k + β)` lies in `C_b^{k,β}(ℝ)`. Taking for `χ` a
  bump equal to one on `[-1, 1]` gives a compactly supported element of `C_b^{k,β}(ℝ)` equal to
  `|x|^(k + β)` on `(-1, 1)` (`TauCeti.exists_ckHolderSpace_eqOn_abs_rpow`).
* **Sharpness** (`TauCeti.not_exists_ckHolderSpace_coe_eq_of_eventuallyEq_abs_rpow`). For `α > β`
  no element of `C_b^{k,α}(ℝ)` agrees with `|x|^(k + β)` near the origin: its `k`-th derivative
  would be `α`-Hölder near `0`, while that of `|x|^(k + β)` is not
  (`TauCeti.not_holderOnWith_iteratedFDeriv_abs_rpow`).

Both transfer along a nonzero continuous linear functional `ℓ` on a normed space `E`, by
precomposition (`TauCeti.CkHolderSpace.compLinearL`): `|ℓ x|^(k + β)` agrees near the hyperplane
`ℓ = 0` with an element of `C_b^{k,β}(E)` (`TauCeti.exists_ckHolderSpace_eq_abs_rpow_comp`) and
with no element of `C_b^{k,α}(E)` for `α > β` (`TauCeti.not_exists_ckHolderSpace_eq_abs_rpow_comp`).
These are the data that show the data spaces of the parabolic Cauchy problem to be sharp.

The `k`-th derivative and its Hölder bound are `TauCeti.iteratedDeriv_abs_rpow` and
`TauCeti.holderWith_iteratedFDeriv_abs_rpow`, in `TauCeti.Analysis.SpecialFunctions.Pow.Regularity`.
-/

public section

open Filter Metric Set
open scoped NNReal Topology

namespace TauCeti

/-! ### `|x|^(k + β)` in `C_b^{k,β}` and not in `C_b^{k,α}` -/

/-- **`χ |x|^(k + β)` lies in `C_b^{k,β}`.** For `0 < β ≤ 1` and a compactly supported `C^{k+1}`
function `χ` on the line, the map `x ↦ χ(x) |x|^(k + β)` lies in `C_b^{k,β}(ℝ)`. -/
theorem exists_ckHolderSpace_coe_eq_mul_abs_rpow (k : ℕ) {β : ℝ≥0} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (k + 1) χ) (hχc : HasCompactSupport χ) :
    ∃ g : CkHolderSpace k β ℝ ℝ, ⇑g = fun x ↦ χ x * |x| ^ ((k : ℝ) + β) := by
  obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.subset_ball (0 : ℝ)
  have hkp : (k : ℝ) < k + β := lt_add_of_pos_right _ hβ₀
  have hf : ContDiff ℝ k fun x : ℝ ↦ |x| ^ ((k : ℝ) + β) := by
    simpa only [Real.norm_eq_abs] using contDiff_norm_rpow_of_lt (E := ℝ) hkp
  obtain ⟨M, -, hM⟩ := hf.contDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen
    isOpen_univ (isCompact_closedBall (0 : ℝ) R) (subset_univ _)
  obtain ⟨N, -, hN⟩ := hχc.exists_bound_iteratedFDeriv_of_contDiff (n := k + 1)
    (by exact_mod_cast hχ)
  refine ⟨CkHolderSpace.cutoff (M := M.toNNReal) (N := N.toNNReal) hf.contDiffOn
    hχ isOpen_ball (convex_ball 0 R) hR hβ₁
    (fun i hi x hx ↦ (hM i hi x (ball_subset_closedBall hx)).trans (Real.le_coe_toNNReal M))
    (fun i hi x ↦ (hN i hi x).trans (Real.le_coe_toNNReal N))
    ((holderWith_iteratedFDeriv_abs_rpow k hβ₀ hβ₁).holderOnWith _), ?_⟩
  rw [CkHolderSpace.coe_cutoff]
  simp only [smul_eq_mul]

/-- **`|x|^(k + β)` is `C^{k,β}` near the origin.** For `0 < β ≤ 1`, some compactly supported
element of `C_b^{k,β}(ℝ)` equals `|x|^(k + β)` on `(-1, 1)`: the power multiplied by a smooth
bump equal to one there. -/
theorem exists_ckHolderSpace_eqOn_abs_rpow (k : ℕ) {β : ℝ≥0} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∃ f : CkHolderSpace k β ℝ ℝ, HasCompactSupport f ∧
      ∀ x ∈ Ioo (-1 : ℝ) 1, f x = |x| ^ ((k : ℝ) + β) := by
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 3 / 2, one_pos, by norm_num⟩
  obtain ⟨f, hf⟩ := exists_ckHolderSpace_coe_eq_mul_abs_rpow k hβ0 hβ1 χ.contDiff
    χ.hasCompactSupport
  refine ⟨f, hf ▸ χ.hasCompactSupport.mul_right, fun x hx ↦ ?_⟩
  have hx1 : x ∈ closedBall (0 : ℝ) χ.rIn := by
    rw [mem_closedBall, Real.dist_0_eq_abs]
    exact (abs_lt.2 hx).le
  rw [congrFun hf x, χ.one_of_mem_closedBall hx1, one_mul]

/-- **`|x|^(k + β)` is not `C^{k,α}` at `0` for `α > β`.** For `0 < β < α`, no element of
`C_b^{k,α}(ℝ)` agrees with `|x|^(k + β)` near `0`: its `k`-th derivative would be `α`-Hölder near
the origin, while the `k`-th derivative of `|x|^(k + β)` is a nonzero multiple of
`sgn(x)^k |x|^β`. -/
theorem not_exists_ckHolderSpace_coe_eq_of_eventuallyEq_abs_rpow (k : ℕ) {β α : ℝ≥0}
    (hβ : 0 < β) (hβα : β < α) {g : ℝ → ℝ} (hg : g =ᶠ[𝓝 0] fun x ↦ |x| ^ ((k : ℝ) + β)) :
    ¬ ∃ G : CkHolderSpace k α ℝ ℝ, ⇑G = g := by
  rintro ⟨G, rfl⟩
  obtain ⟨C, hC⟩ := G.memHolder_iteratedFDeriv
  have hkp : (k : ℝ) < k + β := lt_add_of_pos_right _ hβ
  refine not_holderOnWith_iteratedFDeriv_abs_rpow hkp (C := C)
    (γ := α) (by rw [add_sub_cancel_left]; exact_mod_cast hβα) (hg.iteratedFDeriv ℝ k)
    fun x hx y hy ↦ ?_
  rw [← (hx : _ = _), ← (hy : _ = _)]
  exact hC x y

/-! ### Along a linear functional -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For `0 < β ≤ 1` and a continuous linear functional `ℓ`, some element of `C_b^{k,β}(E)` equals
`|ℓ x|^(k + β)` wherever `|ℓ x| < 1`. -/
theorem exists_ckHolderSpace_eq_abs_rpow_comp (k : ℕ) {β : ℝ≥0} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (ℓ : E →L[ℝ] ℝ) :
    ∃ f : CkHolderSpace k β E ℝ, ∀ x, |ℓ x| < 1 → f x = |ℓ x| ^ ((k : ℝ) + β) := by
  obtain ⟨g, -, hg⟩ := exists_ckHolderSpace_eqOn_abs_rpow k hβ0 hβ1
  exact ⟨CkHolderSpace.compLinearL ℓ g, fun x hx ↦ by
    rw [CkHolderSpace.compLinearL_apply]
    exact hg _ (abs_lt.1 hx)⟩

/-- For `0 < β ≤ 1` and `α ≤ 1`, some element of `C_b^{k+1,β}(E)` equals `|ℓ x|^(k + 1 + β)`
wherever `|ℓ x| < 1` and, as a function, also lies in `C_b^{k,α}(E)`, whatever the order of `α` and
`β`: the element of `TauCeti.exists_ckHolderSpace_eq_abs_rpow_comp` has bounded `k`-th derivative
with bounded derivative, which is therefore `α`-Hölder. -/
theorem exists_ckHolderSpace_eq_abs_rpow_comp_succ (k : ℕ) {α β : ℝ≥0} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hα1 : α ≤ 1) (ℓ : E →L[ℝ] ℝ) :
    ∃ (f : CkHolderSpace (k + 1) β E ℝ) (g : CkHolderSpace k α E ℝ), ⇑g = ⇑f ∧
      ∀ x, |ℓ x| < 1 → f x = |ℓ x| ^ (((k + 1 : ℕ) : ℝ) + β) := by
  obtain ⟨f, hf⟩ := exists_ckHolderSpace_eq_abs_rpow_comp (k + 1) hβ0 hβ1 ℓ
  refine ⟨f, CkHolderSpace.ofContDiff f (f.contDiff.of_le (by exact_mod_cast k.le_succ))
    (fun i hi ↦ ⟨‖f‖, f.norm_iteratedFDeriv_apply_le (by omega)⟩) ?_,
    CkHolderSpace.coe_ofContDiff _ _ _ _, hf⟩
  exact ⟨_, f.contDiff.holderWith_iteratedFDeriv_of_le (N := ‖f‖₊) le_rfl hα1
    fun i hi x ↦ f.norm_iteratedFDeriv_apply_le hi x⟩

/-- For `0 < β < α` and a nonzero continuous linear functional `ℓ`, no element of `C_b^{k,α}(E)`
equals `|ℓ x|^(k + β)` wherever `|ℓ x| < 1`: restricted to a line on which `ℓ` is a coordinate, it
would give an element of `C_b^{k,α}(ℝ)` equal to `|t|^(k + β)` on `(-1, 1)`. -/
theorem not_exists_ckHolderSpace_eq_abs_rpow_comp (k : ℕ) {α β : ℝ≥0} (hβ0 : 0 < β)
    (hβα : β < α) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ¬ ∃ f : CkHolderSpace k α E ℝ, ∀ x, |ℓ x| < 1 → f x = |ℓ x| ^ ((k : ℝ) + β) := by
  rintro ⟨f, hf⟩
  -- A continuous linear right inverse `e` of `ℓ`, which is onto `ℝ` since it is nonzero.
  obtain ⟨e, hcomp⟩ := ℓ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2
    (LinearMap.surjective_iff_ne_zero.2 fun h ↦ hℓ (ContinuousLinearMap.coe_injective h)))
  have he : ∀ t, ℓ (e t) = t := fun t ↦ congr($hcomp t)
  refine not_exists_ckHolderSpace_coe_eq_of_eventuallyEq_abs_rpow k hβ0 hβα
    (g := CkHolderSpace.compLinearL e f) ?_ ⟨_, rfl⟩
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 one_pos) one_pos] with t ht
  rw [CkHolderSpace.compLinearL_apply, hf _ (by rw [he]; exact abs_lt.2 ht), he]

end TauCeti
