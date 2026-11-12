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

Let `u` and `w` be orthogonal vectors of a real inner product space. The vectors
`a • u + b • w` with `0 ≤ a` and `0 ≤ b` form the closed right-angle cone spanned by `u` and `w`.
A unit vector `v` of this cone with `⟪u, v⟫ ≤ 0` is the unit vector `‖w‖⁻¹ • w` along the second
side (`TauCeti.eq_inv_norm_smul_of_eq_smul_add_smul_of_inner_nonpos`): the pairing with `u` is
`a * ‖u‖ ^ 2`, so `a • u` vanishes. The ambient space may have any dimension.

When `B` is a basis indexed by `Fin 2` with `B 0 ⊥ B 1`, the cone consists of the vectors with
nonnegative coordinates in `B`, and the statement reads
`Module.Basis.eq_inv_norm_smul_of_repr_nonneg_of_inner_nonpos`.

At a corner of a domain where two boundary curves meet at a right angle, with `B 0` and `B 1`
their directions at the corner, the cone is the set of directions into the domain, and the
statement says that a unit direction into the domain making a non-acute angle with the first curve
is the direction of the second curve.
-/

public section

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace TauCeti

/-- If `u ⊥ w`, a unit vector `v = a • u + b • w` with `0 ≤ a`, `0 ≤ b` and
nonpositive inner product with `u` is the unit vector `‖w‖⁻¹ • w`. -/
theorem eq_inv_norm_smul_of_eq_smul_add_smul_of_inner_nonpos {u w v : V} {a b : ℝ}
    (horth : ⟪u, w⟫_ℝ = 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hv : v = a • u + b • w)
    (hnorm : ‖v‖ = 1) (hinner : ⟪u, v⟫_ℝ ≤ 0) :
    v = ‖w‖⁻¹ • w := by
  have hzero : a • u = 0 := by
    rcases eq_or_ne u 0 with rfl | hu
    · exact smul_zero a
    rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, horth, mul_zero,
      add_zero] at hinner
    rw [le_antisymm (nonpos_of_mul_nonpos_left hinner (real_inner_self_pos.2 hu)) ha, zero_smul]
  rw [hzero, zero_add] at hv
  have hlength := congrArg norm hv.symm
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, hnorm] at hlength
  rw [hv, eq_inv_of_mul_eq_one_left hlength]

end TauCeti

namespace Module.Basis

/-- If `B 0 ⊥ B 1`, a unit vector with nonnegative coordinates in the basis `B` and nonpositive
inner product with `B 0` is the unit vector `‖B 1‖⁻¹ • B 1`. -/
theorem eq_inv_norm_smul_of_repr_nonneg_of_inner_nonpos (B : Basis (Fin 2) ℝ V) {v : V}
    (horth : ⟪B 0, B 1⟫_ℝ = 0) (hnorm : ‖v‖ = 1) (hcoord : ∀ i, 0 ≤ B.repr v i)
    (hinner : ⟪B 0, v⟫_ℝ ≤ 0) :
    v = ‖B 1‖⁻¹ • B 1 :=
  TauCeti.eq_inv_norm_smul_of_eq_smul_add_smul_of_inner_nonpos horth (hcoord 0) (hcoord 1)
    (by simpa only [Fin.sum_univ_two] using (B.sum_repr v).symm) hnorm hinner

end Module.Basis
