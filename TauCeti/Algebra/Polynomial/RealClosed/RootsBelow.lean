/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsRealClosed.Basic

/-! # Counting the roots below a point by a square substitution

Over an ordered real closed field, the roots of `p.comp (C t - X ^ 2)` are the square roots of
`t - r` for the roots `r ≤ t` of `p`. A root `r < t` contributes the two roots `±√(t - r)`, a root
at `t` contributes the single root `0`, and roots above `t` contribute nothing. So, for nonzero
`p`, the number of distinct roots of `p` below `t` is determined by the number of distinct roots
of `p.comp (C t - X ^ 2)` and whether `t` is a root of `p`. The underlying count of the square
roots of a single element `a`, namely two, one or none as `a` is positive, zero or negative, is
`Polynomial.card_nthRootsFinset_two`.

Since the coefficients of `p.comp (C t - X ^ 2)` are polynomials in `t` and in the coefficients
of `p`, this reduces counting the roots of `p` in `(-∞, t)` to counting all distinct roots of
another polynomial. It is used to describe the roots of a polynomial family below a moving point
by polynomial sign conditions.
-/

public section

namespace Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Over an ordered real closed field, `a` has two square roots `±√a` when `0 < a`, the single
square root `0` when `a = 0`, and none when `a < 0`. -/
theorem card_nthRootsFinset_two (a : R) :
    (nthRootsFinset 2 a).card = if 0 < a then 2 else if a = 0 then 1 else 0 := by
  rcases lt_trichotomy 0 a with h | rfl | h
  · obtain ⟨s, rfl⟩ := IsRealClosed.nonneg_iff_isSquare.mp h.le
    have : nthRootsFinset 2 (s * s) = {s, -s} := by
      ext y
      simp [mem_nthRootsFinset two_pos, sq, mul_self_eq_mul_self_iff]
    rw [this, Finset.card_pair (by grind)]
    simp [h]
  · classical simp [nthRootsFinset_def]
  · have : nthRootsFinset 2 a = ∅ := Finset.eq_empty_of_forall_notMem fun y hy => by
      nlinarith [(mem_nthRootsFinset two_pos a).1 hy, sq_nonneg y]
    simp [this, h.not_gt, h.ne]

/-- **Roots below a point by a square substitution.** For nonzero `p`, every root of `p` below
`t` gives two distinct roots `±√(t - r)` of `p.comp (C t - X ^ 2)`, a root at `t` gives the root
`0`, and these are all of its roots. -/
theorem card_roots_toFinset_comp_C_sub_X_sq {p : R[X]} (hp : p ≠ 0) (t : R) :
    (p.comp (C t - X ^ 2)).roots.toFinset.card =
      2 * {r ∈ p.roots.toFinset | r < t}.card + if p.IsRoot t then 1 else 0 := by
  have hq : p.comp (C t - X ^ 2) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    rintro (h | ⟨-, h⟩)
    · exact hp h
    · simpa using congrArg (coeff · 2) h
  have hmem (y : R) : y ∈ (p.comp (C t - X ^ 2)).roots.toFinset ↔ p.IsRoot (t - y ^ 2) := by
    simp [mem_roots hq]
  -- Group the roots of the substituted polynomial by the root `t - y ^ 2` of `p` they come from.
  rw [Finset.card_eq_sum_card_fiberwise (f := fun y => t - y ^ 2) (t := p.roots.toFinset)
    fun y hy => by simpa [mem_roots hp] using (hmem y).1 hy]
  -- The fiber over a root `r` consists of the square roots of `t - r`.
  have hfiber (r : R) (hr : r ∈ p.roots.toFinset) :
      {y ∈ (p.comp (C t - X ^ 2)).roots.toFinset | t - y ^ 2 = r}.card =
        (if r < t then 2 else 0) + if t = r then 1 else 0 := by
    have hr' : p.IsRoot r := by simpa [mem_roots hp] using hr
    have : {y ∈ (p.comp (C t - X ^ 2)).roots.toFinset | t - y ^ 2 = r} =
        nthRootsFinset 2 (t - r) := by
      ext y
      rw [Finset.mem_filter, hmem, mem_nthRootsFinset two_pos]
      grind
    rw [this, card_nthRootsFinset_two]
    grind
  rw [Finset.sum_congr rfl hfiber, Finset.sum_add_distrib, ← Finset.sum_filter,
    Finset.sum_ite_eq]
  simp [mem_roots hp, mul_comm]

end Polynomial
