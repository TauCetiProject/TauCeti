/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Connected.Clopen

/-!
# The method of continuity

Let `E` be a Banach space and `F` a normed space. The **method of continuity** transports
invertibility of a bounded linear operator `T s : E →L[𝕜] F` along a continuous family of
operators, provided the family satisfies a *uniform a priori estimate*

`‖x‖ ≤ C * ‖T s x‖` for every parameter `s` and every `x : E`,

with one constant `C`. If the parameters range over a preconnected set and one member of the
family is invertible, then every member is invertible, and the inverses depend continuously on
the parameter and have operator norm at most `C`. The classical form (Gilbarg–Trudinger,
Theorem 5.2) joins two operators `T₀` and `T₁` by the segment `(1 - t) • T₀ + t • T₁`,
`t ∈ [0, 1]`: under the uniform estimate along the segment, `T₁` is invertible if and only if
`T₀` is.

This is how a priori estimates become existence theorems in elliptic and parabolic PDE: one
deforms the operator of interest into a model operator (the Laplacian or the heat operator)
whose solvability is known, through operators satisfying one Schauder estimate. In such
applications the estimate is the hard analytic input, and this file supplies the functional
analysis around it.

The proof has three ingredients:

* an a priori estimate bounds the inverse, `‖T.inverse‖ ≤ C`, and turns surjectivity into
  invertibility (`ContinuousLinearMap.isInvertible_iff_surjective_of_forall_norm_le`);
* an invertible `T` stays invertible under perturbations `S` with `‖T.inverse‖ * ‖S - T‖ < 1`,
  by the Neumann series for `1 + T.inverse ∘ (S - T)` in the Banach algebra `E →L[𝕜] E`;
* hence nearby parameters are invertible together, with a radius depending only on `C`, and
  the relation "invertible together" spreads over a preconnected set
  (`IsPreconnected.induction₂'`).

## Main declarations

* `ContinuousLinearMap.norm_inverse_le_of_forall_norm_le`: the a priori estimate bounds the
  totalized inverse.
* `ContinuousLinearMap.isInvertible_iff_surjective_of_forall_norm_le`: under an a priori
  estimate, invertibility is surjectivity.
* `ContinuousLinearMap.IsInvertible.of_norm_inverse_mul_norm_sub_lt_one`: quantitative
  stability of invertibility under perturbation.
* `IsPreconnected.isInvertible_of_forall_norm_le`: the method of continuity over a
  preconnected parameter set.
* `IsPreconnected.continuousOn_inverse_of_forall_norm_le`: the inverses then depend
  continuously on the parameter.
* `ContinuousLinearMap.isInvertible_iff_of_forall_norm_le_segment`: the segment form of
  Gilbarg–Trudinger, Theorem 5.2.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2, and its use in the proof of Theorem 6.8.
* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004,
  Chapter 4 (the method of continuity for parabolic Schauder theory).
-/

public section

open Function Set Filter
open scoped Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An a priori estimate `‖x‖ ≤ C * ‖T x‖` bounds the norm of the (totalized) inverse of `T` by
`C`. No invertibility of `T` is assumed: if `T` is not invertible its inverse is `0`. -/
theorem norm_inverse_le_of_forall_norm_le {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖x‖ ≤ C * ‖T x‖) : ‖T.inverse‖ ≤ C := by
  by_cases hT : T.IsInvertible
  · refine opNorm_le_bound _ hC fun y ↦ ?_
    simpa only [hT.self_apply_inverse] using h (T.inverse y)
  · simpa only [inverse_of_not_isInvertible hT, norm_zero] using hC

/-- Under an a priori estimate `‖x‖ ≤ C * ‖T x‖`, a continuous linear map is invertible exactly
when it is surjective: the estimate makes `T` injective and its inverse bounded. No completeness
is needed. -/
theorem isInvertible_iff_surjective_of_forall_norm_le {T : E →L[𝕜] F} {C : ℝ}
    (h : ∀ x, ‖x‖ ≤ C * ‖T x‖) : T.IsInvertible ↔ Surjective T := by
  refine ⟨IsInvertible.surjective, fun hs ↦ ?_⟩
  have hinj : Injective T := (injective_iff_map_eq_zero T).2 fun x hx ↦ by
    simpa [hx] using h x
  let e : E ≃ₗ[𝕜] F := LinearEquiv.ofBijective T.toLinearMap ⟨hinj, hs⟩
  have he (y : F) : T (e.symm y) = y := e.apply_symm_apply y
  refine ⟨e.toContinuousLinearEquivOfBounds ‖T‖ (max C 0) T.le_opNorm fun y ↦ ?_, rfl⟩
  calc ‖e.symm y‖ ≤ C * ‖T (e.symm y)‖ := h _
    _ ≤ max C 0 * ‖y‖ := by
      rw [he]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- **Quantitative stability of invertibility.** If `T : E →L[𝕜] F` is invertible, `E` is
complete and `‖T.inverse‖ * ‖S - T‖ < 1`, then `S` is invertible: `S = T ∘ (1 + T⁻¹ ∘ (S - T))`,
and the second factor is invertible by the Neumann series. -/
theorem IsInvertible.of_norm_inverse_mul_norm_sub_lt_one [CompleteSpace E] {T S : E →L[𝕜] F}
    (hT : T.IsInvertible) (h : ‖T.inverse‖ * ‖S - T‖ < 1) : S.IsInvertible := by
  let A : E →L[𝕜] E := T.inverse ∘L (S - T)
  have hA : ‖-A‖ < 1 := by
    rw [norm_neg]
    exact (opNorm_comp_le _ _).trans_lt h
  let u : (E →L[𝕜] E)ˣ := Units.oneSub (-A) hA
  have hu : (u : E →L[𝕜] E).IsInvertible :=
    ⟨ContinuousLinearEquiv.unitsEquiv 𝕜 E u,
      ext fun x ↦ ContinuousLinearEquiv.unitsEquiv_apply 𝕜 E u x⟩
  have hS : S = T ∘L (u : E →L[𝕜] E) := by
    ext x
    simp [u, A, hT.self_apply_inverse]
  rw [hS]
  exact hT.comp hu

end ContinuousLinearMap

open ContinuousLinearMap

section MethodOfContinuity

variable {𝕜 E F X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace X]

/-- Under a uniform a priori estimate with constant `C`, two members of the family that are closer
than `1 / (max C 0 + 1)` in operator norm are invertible together. This is the local step of the
method of continuity; the radius depends only on `C`. -/
private theorem isInvertible_of_norm_sub_lt {T S : E →L[𝕜] F} {C : ℝ}
    (hTC : ∀ x, ‖x‖ ≤ C * ‖T x‖) (hT : T.IsInvertible) (h : ‖S - T‖ < 1 / (max C 0 + 1)) :
    S.IsInvertible := by
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hT' (x : E) : ‖x‖ ≤ max C 0 * ‖T x‖ :=
    (hTC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  refine hT.of_norm_inverse_mul_norm_sub_lt_one ?_
  calc ‖T.inverse‖ * ‖S - T‖ ≤ max C 0 * ‖S - T‖ :=
        mul_le_mul_of_nonneg_right (norm_inverse_le_of_forall_norm_le hC hT') (norm_nonneg _)
    _ ≤ max C 0 * (1 / (max C 0 + 1)) := mul_le_mul_of_nonneg_left h.le hC
    _ < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith

/-- **The method of continuity.** Let `T` be a family of continuous linear maps from a Banach
space `E` to a normed space `F`, continuous on a preconnected set `S` of parameters, and
satisfying the uniform a priori estimate `‖x‖ ≤ C * ‖T s x‖` for all `s ∈ S`. If `T t₀` is
invertible for one `t₀ ∈ S`, then `T t` is invertible for every `t ∈ S`. -/
theorem IsPreconnected.isInvertible_of_forall_norm_le {S : Set X} (hS : IsPreconnected S)
    {T : X → E →L[𝕜] F} (hT : ContinuousOn T S) {C : ℝ}
    (hC : ∀ s ∈ S, ∀ x, ‖x‖ ≤ C * ‖T s x‖) {t₀ t : X} (ht₀ : t₀ ∈ S)
    (h₀ : (T t₀).IsInvertible) (ht : t ∈ S) : (T t).IsInvertible := by
  refine hS.induction₂' (fun a b ↦ (T a).IsInvertible → (T b).IsInvertible) (fun s hs ↦ ?_)
    (fun _ _ _ _ _ _ hab hbc h ↦ hbc (hab h)) ht₀ ht h₀
  have hδ : (0 : ℝ) < 1 / (max C 0 + 1) := by positivity
  filter_upwards [(hT s hs).eventually (Metric.ball_mem_nhds _ hδ), self_mem_nhdsWithin]
    with r hr hrS
  rw [dist_eq_norm] at hr
  exact ⟨fun h ↦ isInvertible_of_norm_sub_lt (hC s hs) h hr,
    fun h ↦ isInvertible_of_norm_sub_lt (hC r hrS) h (by rwa [norm_sub_rev])⟩

/-- In the method of continuity the inverses depend continuously on the parameter: under the
hypotheses of `IsPreconnected.isInvertible_of_forall_norm_le`, the map `t ↦ (T t).inverse` is
continuous on `S` in the operator norm. Their norms are at most `C` by
`ContinuousLinearMap.norm_inverse_le_of_forall_norm_le`. -/
theorem IsPreconnected.continuousOn_inverse_of_forall_norm_le {S : Set X} (hS : IsPreconnected S)
    {T : X → E →L[𝕜] F} (hT : ContinuousOn T S) {C : ℝ}
    (hC : ∀ s ∈ S, ∀ x, ‖x‖ ≤ C * ‖T s x‖) {t₀ : X} (ht₀ : t₀ ∈ S)
    (h₀ : (T t₀).IsInvertible) : ContinuousOn (fun t ↦ (T t).inverse) S := fun t ht ↦
  ((hS.isInvertible_of_forall_norm_le hT hC ht₀ h₀ ht).contDiffAt_map_inverse
    (n := 0)).continuousAt.comp_continuousWithinAt (hT t ht)

end MethodOfContinuity

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The method of continuity along a segment** (Gilbarg–Trudinger, Theorem 5.2). Let `T₀` and
`T₁` be continuous linear maps from a Banach space `E` to a normed space `F`, and suppose the
operators `(1 - t) • T₀ + t • T₁`, `t ∈ [0, 1]`, satisfy one a priori estimate
`‖x‖ ≤ C * ‖((1 - t) • T₀ + t • T₁) x‖`. Then `T₁` is invertible if and only if `T₀` is. Under
the estimate, invertibility is the same as surjectivity
(`ContinuousLinearMap.isInvertible_iff_surjective_of_forall_norm_le`). -/
theorem isInvertible_iff_of_forall_norm_le_segment {T₀ T₁ : E →L[𝕜] F} {C : ℝ}
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ ≤ C * ‖((1 - (t : 𝕜)) • T₀ + (t : 𝕜) • T₁) x‖) :
    T₁.IsInvertible ↔ T₀.IsInvertible := by
  let T : ℝ → E →L[𝕜] F := fun t ↦ (1 - (t : 𝕜)) • T₀ + (t : 𝕜) • T₁
  have hT : Continuous T := by fun_prop
  have hT₀ : T 0 = T₀ := by simp [T]
  have hT₁ : T 1 = T₁ := by simp [T]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  constructor
  · intro h
    rw [← hT₀]
    exact isPreconnected_Icc.isInvertible_of_forall_norm_le hT.continuousOn hC h1
      (hT₁ ▸ h) h0
  · intro h
    rw [← hT₁]
    exact isPreconnected_Icc.isInvertible_of_forall_norm_le hT.continuousOn hC h0
      (hT₀ ▸ h) h1

end ContinuousLinearMap
