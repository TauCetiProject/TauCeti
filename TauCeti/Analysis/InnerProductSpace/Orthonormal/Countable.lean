/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Metric separation and countability of orthonormal families

Any two distinct vectors in an orthonormal family `v : ι → E` are orthogonal unit vectors, so by
the Pythagorean theorem they sit at norm distance `√2` (`Orthonormal.norm_sub_eq_sqrt_two_of_ne`,
`Orthonormal.dist_eq_sqrt_two_of_ne`). Consequently:

* the range of `v` carries the discrete subspace topology (`Orthonormal.discreteTopology_range`);
* open balls of radius `√2 / 2` centered at `v i` are pairwise disjoint, so in a separable
  inner-product space every orthonormal family has a countable index type
  (`Orthonormal.countable_of_separableSpace`).

All statements hold over any `RCLike` scalar field in a seminormed inner-product space.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Proposition I.4.12.
* P. R. Halmos, *A Hilbert Space Problem Book*, 2nd ed., Problem 7.
-/

public section

open scoped InnerProductSpace

namespace Orthonormal

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {v : ι → E}

/-- Distinct vectors in an orthonormal family satisfy `‖v i - v j‖ = √2`. -/
theorem norm_sub_eq_sqrt_two_of_ne (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i - v j‖ = √2 := by
  rw [norm_sub_eq_norm_add (hv.inner_eq_zero hij.symm)]
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v i) (v j)
    (hv.inner_eq_zero hij)
  rw [hv.norm_eq_one, hv.norm_eq_one] at hsq
  rw [← Real.sqrt_sq (norm_nonneg _), sq, hsq]
  norm_num

/-- Distinct vectors in an orthonormal family sit at distance `√2`. -/
theorem dist_eq_sqrt_two_of_ne (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    dist (v i) (v j) = √2 := by
  rw [dist_eq_norm, hv.norm_sub_eq_sqrt_two_of_ne hij]

/-- The range of an orthonormal family carries the discrete topology. -/
theorem discreteTopology_range (hv : Orthonormal 𝕜 v) : DiscreteTopology (Set.range v) :=
  DiscreteTopology.of_forall_le_dist (Real.sqrt_pos.2 zero_lt_two)
    fun ⟨_, i, hi⟩ ⟨_, j, hj⟩ hne ↦ by
      subst hi hj
      exact (hv.dist_eq_sqrt_two_of_ne fun hij ↦ hne (Subtype.ext (congrArg v hij))).symm.le

/-- **Countability of orthonormal families in separable spaces.** Every orthonormal family in a
separable inner-product space has a countable index type: the open balls of radius `√2 / 2` around
its members are pairwise disjoint. -/
theorem countable_of_separableSpace [TopologicalSpace.SeparableSpace E]
    (hv : Orthonormal 𝕜 v) : Countable ι := by
  let B : ι → Set E := fun i ↦ Metric.ball (v i) (√2 / 2)
  have hdisj : Pairwise (Function.onFun Disjoint B) := fun i j hij ↦
    Metric.ball_disjoint_ball <| by rw [add_halves, hv.dist_eq_sqrt_two_of_ne hij]
  exact hdisj.countable_of_isOpen_disjoint (fun _ ↦ Metric.isOpen_ball)
    fun i ↦ ⟨v i, Metric.mem_ball_self (by positivity)⟩

end Orthonormal
