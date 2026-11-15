/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Coordinate bounds in a basis over a linearly ordered ring

If a positive scalar multiple `c • z` of a vector `z` is a linear combination `∑ a ∈ s, r a • a`
with coefficients satisfying `|r a| ≤ c`, then every coordinate of `z` in a basis `b` is bounded in
absolute value by the sum `∑ a ∈ s, |b.repr a i|` of the corresponding coordinates of the vectors
in `s`. Specializing to natural-number multiples bounds the coordinates of vectors in the
fundamental parallelepiped of a finite generating set.

## Main results

* `Module.Basis.abs_repr_le_sum_abs_of_smul_eq`: coordinate bound for `z` satisfying
  `c • z = ∑ a ∈ s, r a • a` with `0 < c` and `|r a| ≤ c`.
* `Module.Basis.abs_repr_le_sum_abs_of_nsmul_eq`: natural-multiple specialization for
  `n • z = ∑ a ∈ s, r a • a` with `0 < n` and `r a ≤ n`.
-/

public section

namespace Module.Basis

variable {ι R M : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommMonoid M] [Module R M]

/-- If `c • z = ∑ a ∈ s, r a • a` with `0 < c` and `|r a| ≤ c` for all `a ∈ s`, then each
coordinate of `z` in a basis `b` satisfies `|b.repr z i| ≤ ∑ a ∈ s, |b.repr a i|`. -/
theorem abs_repr_le_sum_abs_of_smul_eq (b : Module.Basis ι R M) {s : Finset M} {c : R}
    (hc : 0 < c) {r : M → R} (hr : ∀ a ∈ s, |r a| ≤ c) {z : M}
    (hz : c • z = ∑ a ∈ s, r a • a) (i : ι) :
    |b.repr z i| ≤ ∑ a ∈ s, |b.repr a i| := by
  refine le_of_mul_le_mul_left ?_ hc
  calc
    c * |b.repr z i|
        = |c * b.repr z i| := by rw [abs_mul, abs_of_pos hc]
    _ = |∑ a ∈ s, r a * b.repr a i| := by
        congr 1
        simpa [map_smul, map_sum] using congrArg (fun f ↦ f i) (congrArg b.repr hz)
    _ ≤ ∑ a ∈ s, |r a * b.repr a i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ s, |r a| * |b.repr a i| :=
        Finset.sum_congr rfl fun _ _ ↦ abs_mul _ _
    _ ≤ ∑ a ∈ s, c * |b.repr a i| :=
        Finset.sum_le_sum fun a ha ↦ mul_le_mul_of_nonneg_right (hr a ha) (abs_nonneg _)
    _ = c * ∑ a ∈ s, |b.repr a i| := (Finset.mul_sum _ _ _).symm

/-- If `n • z = ∑ a ∈ s, r a • a` with `0 < n` and `r a ≤ n` for all `a ∈ s`, then each coordinate
of `z` in a basis `b` satisfies `|b.repr z i| ≤ ∑ a ∈ s, |b.repr a i|`. -/
theorem abs_repr_le_sum_abs_of_nsmul_eq (b : Module.Basis ι R M) {s : Finset M} {n : ℕ}
    (hn : 0 < n) {r : M → ℕ} (hr : ∀ a ∈ s, r a ≤ n) {z : M}
    (hz : n • z = ∑ a ∈ s, r a • a) (i : ι) :
    |b.repr z i| ≤ ∑ a ∈ s, |b.repr a i| := by
  refine b.abs_repr_le_sum_abs_of_smul_eq (c := (n : R)) (r := fun a ↦ (r a : R))
    (Nat.cast_pos.mpr hn) (fun a ha ↦ ?_) ?_ i
  · rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact Nat.cast_le.mpr (hr a ha)
  · simpa only [Nat.cast_smul_eq_nsmul] using hz

end Module.Basis
