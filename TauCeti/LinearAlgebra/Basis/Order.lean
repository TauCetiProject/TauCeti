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
# Coordinate bounds in a basis over an ordered ring

Over a strictly ordered ring `R`, if a positive scalar multiple `c • z` of a vector `z` is an
`R`-linear combination `∑ j ∈ s, r j • a j` with coefficients bounded in absolute value by `c`,
then each coordinate of `z` in a basis `b` has absolute value at most the sum of the absolute
values of the corresponding coordinates of the generators `a j`. Specializing to natural multiples
`n • z = ∑ j ∈ s, r j • a j` with `0 < n` and `r j ≤ n` bounds representatives of remainder vectors
inside a fundamental coordinate box.

## Main results

* `Module.Basis.abs_repr_le_of_smul_eq_sum`: coordinate bound for `c • z = ∑ j ∈ s, r j • a j`
  when `0 < c` and `|r j| ≤ c`.
* `Module.Basis.abs_repr_le_of_nsmul_eq_sum`: specialization to natural multiples
  `n • z = ∑ j ∈ s, r j • a j` with `0 < n` and `r j ≤ n`.
-/

public section

namespace Module.Basis

variable {ι κ R M : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M]

/-- If `c • z = ∑ j ∈ s, r j • a j` with `0 < c` and `|r j| ≤ c` for every `j ∈ s`, then each
`b`-coordinate of `z` has absolute value at most `∑ j ∈ s, |b.repr (a j) i|`. -/
theorem abs_repr_le_of_smul_eq_sum (b : Basis ι R M) {s : Finset κ} {c : R} (hc : 0 < c)
    {a : κ → M} {r : κ → R} (hr : ∀ j ∈ s, |r j| ≤ c) {z : M}
    (hz : c • z = ∑ j ∈ s, r j • a j) (i : ι) :
    |b.repr z i| ≤ ∑ j ∈ s, |b.repr (a j) i| := by
  have hle : c * |b.repr z i| ≤ c * ∑ j ∈ s, |b.repr (a j) i| := calc
    c * |b.repr z i|
      = |c * b.repr z i| := by rw [abs_mul, abs_of_pos hc]
    _ = |b.repr (c • z) i| := by simp
    _ = |∑ j ∈ s, r j * b.repr (a j) i| := by simp [hz, Finsupp.finsetSum_apply]
    _ ≤ ∑ j ∈ s, |r j * b.repr (a j) i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ s, |r j| * |b.repr (a j) i| := Finset.sum_congr rfl fun _ _ => abs_mul _ _
    _ ≤ ∑ j ∈ s, c * |b.repr (a j) i| := Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (hr j hj) (abs_nonneg _)
    _ = c * ∑ j ∈ s, |b.repr (a j) i| := (Finset.mul_sum _ _ _).symm
  exact le_of_mul_le_mul_left hle hc

/-- If `n • z = ∑ j ∈ s, r j • a j` with `0 < n` and `r j ≤ n` for every `j ∈ s`, then each
`b`-coordinate of `z` has absolute value at most `∑ j ∈ s, |b.repr (a j) i|`. -/
theorem abs_repr_le_of_nsmul_eq_sum (b : Basis ι R M) {s : Finset κ} {n : ℕ} (hn : 0 < n)
    {a : κ → M} {r : κ → ℕ} (hr : ∀ j ∈ s, r j ≤ n) {z : M}
    (hz : n • z = ∑ j ∈ s, r j • a j) (i : ι) :
    |b.repr z i| ≤ ∑ j ∈ s, |b.repr (a j) i| := by
  refine b.abs_repr_le_of_smul_eq_sum (c := (n : R)) (r := fun j => (r j : R))
    (Nat.cast_pos.mpr hn) (fun j hj => by rw [Nat.abs_cast]; exact_mod_cast hr j hj) ?_ i
  simpa only [Nat.cast_smul_eq_nsmul] using hz

end Module.Basis
