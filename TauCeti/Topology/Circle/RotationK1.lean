/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.RotationLoop
public import TauCeti.Topology.Circle.CoordinateRing

/-!
# The rotation matrix over the real circle is not stably elementary

Let `A = TauCeti.CircleRing ℝ = ℝ[x, y] ⧸ (x² + y² - 1)` be the coordinate ring of the real
circle. The rotation matrix `M = !![x, -y; y, x]` (`TauCeti.CircleRing.rotation`) has
determinant one. This file proves that no identity stabilization `M ⊕ 1` of it is a product of
elementary matrices. Equivalently, its class in algebraic `K₁(A)` is nontrivial, and since its
determinant is one, `SK₁(A)` is nontrivial.

The argument is topological. Evaluating the entries on the unit circle of `ℂ`
(`TauCeti.CircleRing.evalGL`), the stabilization `M ⊕ 1` of size `k ≥ 2` becomes the loop
`z ↦ diag (!![Re z, -Im z; Im z, Re z], 1)` of rotations in `GL (Fin k) ℝ`, which is the identity
at the base point `1`. The loop of an elementary matrix that is the identity at `1` is
nullhomotopic relative to `1`. The rotation loop is not: its lift through the Spin double cover
runs from `1` to `-1` (`TauCeti.not_homotopicRel_circleRotationLoop_const`).

## Main results

* `TauCeti.CircleRing.evalGL_stabilizeGL_rotation`: the loop of `M ⊕ 1` is the rotation loop.
* `TauCeti.CircleRing.stabilizeGL_rotation_notMem_elementarySubgroup`: no identity
  stabilization of `M` is elementary.
* `TauCeti.CircleRing.mk_rotation_ne_one`: the class of `M` in `K₁(A)` is nontrivial.
* `TauCeti.CircleRing.specialAlgebraicK1_ne_bot`: `SK₁(A)` is nontrivial.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Example 1.5.4.
-/

public section

open Matrix

namespace TauCeti.CircleRing

/-- **The loop of the stabilized rotation matrix is the rotation loop.** Evaluated on the unit
circle, the identity stabilization `!![x, -y; y, x] ⊕ 1` of size `k ≥ 2` is the loop
`z ↦ diag (!![Re z, -Im z; Im z, Re z], 1)`. -/
theorem evalGL_stabilizeGL_rotation {k : ℕ} (hk : 2 ≤ k) :
    evalGL (stabilizeGL (CircleRing ℝ) hk (SpecialLinearGroup.toGL rotation)) =
      circleRotationLoop hk := by
  ext z i j
  rw [coe_evalGL_apply, coe_stabilizeGL_apply, coe_circleRotationLoop_apply]
  split_ifs with h
  · obtain ⟨hi, hj⟩ := h
    obtain ⟨_ | _ | i, hi'⟩ := i <;> obtain ⟨_ | _ | j, hj'⟩ := j <;>
      first | omega | simp
  · by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- **The stabilized rotation matrix is not elementary.** For every `k ≥ 2`, the identity
stabilization `!![x, -y; y, x] ⊕ 1` of size `k` over the real circle is not a product of
elementary matrices: its loop on the unit circle is the rotation loop, which is not
nullhomotopic relative to the base point, while the loop of an elementary matrix is. -/
theorem stabilizeGL_rotation_notMem_elementarySubgroup {k : ℕ} (hk : 2 ≤ k) :
    stabilizeGL (CircleRing ℝ) hk (SpecialLinearGroup.toGL rotation) ∉
      elementarySubgroup (Fin k) (CircleRing ℝ) := by
  intro h
  have h₁ := evalGL_homotopicRel_one_of_mem_elementarySubgroup h
    (by rw [evalGL_stabilizeGL_rotation, circleRotationLoop_one])
  rw [evalGL_stabilizeGL_rotation] at h₁
  exact not_homotopicRel_circleRotationLoop_const hk h₁

/-- **The rotation matrix has nontrivial class in `K₁`.** The class of `!![x, -y; y, x]` in
algebraic `K₁` of the real circle is not `1`: no identity stabilization of it is elementary. -/
theorem mk_rotation_ne_one :
    AlgebraicK1.mk (CircleRing ℝ) 2 (SpecialLinearGroup.toGL rotation) ≠ 1 := by
  rw [Ne, AlgebraicK1.mk_eq_one_iff]
  rintro ⟨k, hk, h⟩
  exact stabilizeGL_rotation_notMem_elementarySubgroup hk h

/-- **`SK₁` of the real circle is nontrivial.** The class of the determinant-one rotation matrix
`!![x, -y; y, x]` is a nontrivial element of `SK₁` of the coordinate ring of the real circle. -/
theorem specialAlgebraicK1_ne_bot : specialAlgebraicK1 (CircleRing ℝ) ≠ ⊥ :=
  (Subgroup.ne_bot_iff_exists_ne_one).2
    ⟨⟨_, AlgebraicK1.mk_mem_specialAlgebraicK1_iff.2 (by ext; simp)⟩,
      fun h ↦ mk_rotation_ne_one (congrArg Subtype.val h)⟩

end TauCeti.CircleRing
