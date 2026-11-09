/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Unit vectors in a right-angle cone

Let `B` be a basis, indexed by `Fin 2`, of a real inner product space whose two vectors are
orthogonal. The vectors with nonnegative coordinates in `B` form the closed right-angle cone
spanned by `B 0` and `B 1`. A unit vector `v` of this cone with `⟪B 0, v⟫ ≤ 0` is the unit vector
`‖B 1‖⁻¹ • B 1` along the second side
(`Module.Basis.eq_inv_norm_smul_of_repr_nonneg_of_inner_nonpos`): the pairing with `B 0` is the
first coordinate of `v` times `‖B 0‖ ^ 2`, so this coordinate vanishes.

At a corner of a domain where two boundary curves meet at a right angle, with `B 0` and `B 1`
their directions at the corner, the cone is the set of directions into the domain, and the
statement says that a unit direction into the domain making a non-acute angle with the first curve
is the direction of the second curve.
-/

public section

open scoped InnerProductSpace

namespace Module.Basis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- If `B 0 ⊥ B 1`, a unit vector with nonnegative coordinates in the basis `B` and nonpositive
inner product with `B 0` is the unit vector `‖B 1‖⁻¹ • B 1`. -/
theorem eq_inv_norm_smul_of_repr_nonneg_of_inner_nonpos (B : Basis (Fin 2) ℝ V) {v : V}
    (horth : ⟪B 0, B 1⟫_ℝ = 0) (hnorm : ‖v‖ = 1) (hcoord : ∀ i, 0 ≤ B.repr v i)
    (hinner : ⟪B 0, v⟫_ℝ ≤ 0) :
    v = ‖B 1‖⁻¹ • B 1 := by
  have hexp : B.repr v 0 • B 0 + B.repr v 1 • B 1 = v := by
    simpa only [Fin.sum_univ_two] using B.sum_repr v
  have hzero : B.repr v 0 = 0 := by
    rw [← hexp, inner_add_right, real_inner_smul_right, real_inner_smul_right, horth, mul_zero,
      add_zero] at hinner
    exact le_antisymm (nonpos_of_mul_nonpos_left hinner (real_inner_self_pos.2 (B.ne_zero 0)))
      (hcoord 0)
  rw [hzero, zero_smul, zero_add] at hexp
  have hlength := congrArg norm hexp
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hcoord 1), hnorm] at hlength
  rw [← hexp, eq_inv_of_mul_eq_one_left hlength]

end Module.Basis
