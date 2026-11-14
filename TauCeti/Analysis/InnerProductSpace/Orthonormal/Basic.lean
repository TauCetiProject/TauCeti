/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Topology.Bases

/-!
# Pairwise distance and countability for orthonormal families

Two distinct vectors of an orthonormal family in an inner product space sit at squared distance `2`,
hence at distance `√2` (`Orthonormal.norm_sub_sq`, `Orthonormal.norm_sub_eq_sqrt_two`,
`Orthonormal.dist_eq_sqrt_two`). Consequently the open balls of radius `√2 / 2` around the members
of an orthonormal family are pairwise disjoint, so in a separable inner product space every
orthonormal family is countable (`Orthonormal.countable_of_separableSpace`).

Independently of separability, Bessel's inequality `Orthonormal.inner_products_summable` implies
that any vector pairs nontrivially with at most countably many members of an orthonormal family
(`Orthonormal.countable_support_inner_left`, `Orthonormal.countable_support_inner_right`).

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Chapter I, §4.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, §II.2.
-/

public section

open scoped InnerProductSpace

namespace Orthonormal

variable {𝕜 : Type*} {E : Type*} {ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] {v : ι → E}

/-- Two distinct vectors of an orthonormal family have `‖v i - v j‖ ^ 2 = 2`. -/
theorem norm_sub_sq (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i - v j‖ ^ 2 = 2 := by
  rw [@_root_.norm_sub_sq 𝕜, hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij]
  norm_num

/-- Two distinct vectors of an orthonormal family satisfy `‖v i - v j‖ = √2`. -/
theorem norm_sub_eq_sqrt_two (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i - v j‖ = √2 := by
  rw [← Real.sqrt_sq (norm_nonneg _), hv.norm_sub_sq hij]

/-- Two distinct vectors of an orthonormal family sit at distance `√2`. -/
theorem dist_eq_sqrt_two (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    dist (v i) (v j) = √2 := by
  rw [dist_eq_norm, hv.norm_sub_eq_sqrt_two hij]

/-- **Countable Fourier support.** Every vector has nonzero inner product with at most countably
many members of an orthonormal family. -/
theorem countable_support_inner_left (hv : Orthonormal 𝕜 v) (x : E) :
    (Function.support fun i ↦ ⟪v i, x⟫_𝕜).Countable := by
  refine (hv.inner_products_summable x).countable_support.mono fun i hi ↦ ?_
  exact pow_ne_zero 2 (norm_ne_zero_iff.2 hi)

/-- Right-hand inner-product form of `Orthonormal.countable_support_inner_left`. -/
theorem countable_support_inner_right (hv : Orthonormal 𝕜 v) (x : E) :
    (Function.support fun i ↦ ⟪x, v i⟫_𝕜).Countable := by
  refine (hv.countable_support_inner_left x).mono fun i (hi : ⟪x, v i⟫_𝕜 ≠ 0) ↦ ?_
  intro (h0 : ⟪v i, x⟫_𝕜 = 0)
  apply hi
  rw [← inner_conj_symm, h0, map_zero]

/-- Every orthonormal family in a separable inner product space is countable. -/
theorem countable_of_separableSpace (hv : Orthonormal 𝕜 v)
    [TopologicalSpace.SeparableSpace E] : Countable ι := by
  have hr : 0 < √2 / 2 := by positivity
  have hd : Pairwise (Function.onFun Disjoint fun i ↦ Metric.ball (v i) (√2 / 2)) := fun i j hij ↦
    Metric.ball_disjoint_ball (by rw [add_halves, hv.dist_eq_sqrt_two hij])
  exact hd.countable_of_isOpen_disjoint (fun _ ↦ Metric.isOpen_ball)
    (fun i ↦ ⟨v i, Metric.mem_ball_self hr⟩)

end Orthonormal
