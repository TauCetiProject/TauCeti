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
of `p.comp (C t - X ^ 2)` and whether `t` is a root of `p`.

Since the coefficients of `p.comp (C t - X ^ 2)` are polynomials in `t` and in the coefficients
of `p`, this reduces counting the roots of `p` in `(-∞, t)` to counting all distinct roots of
another polynomial. It is used to describe the roots of a polynomial family below a moving point
by polynomial sign conditions.
-/

public section

namespace Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Roots below a point by a square substitution.** For nonzero `p`, every root of `p` below
`t` gives two distinct roots `±√(t - r)` of `p.comp (C t - X ^ 2)`, a root at `t` gives the root
`0`, and these are all of its roots. -/
theorem card_roots_toFinset_comp_C_sub_X_sq {p : R[X]} (hp : p ≠ 0) (t : R) :
    (p.comp (C t - X ^ 2)).roots.toFinset.card =
      2 * {r ∈ p.roots.toFinset | r < t}.card + if p.IsRoot t then 1 else 0 := by
  classical
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
  have hfiber (r : R) (hr : r ∈ p.roots.toFinset) :
      {y ∈ (p.comp (C t - X ^ 2)).roots.toFinset | t - y ^ 2 = r}.card =
        (if r < t then 2 else 0) + if t = r then 1 else 0 := by
    have hr' : p.IsRoot r := by simpa [mem_roots hp] using hr
    have hfib (y : R) : y ∈ {y ∈ (p.comp (C t - X ^ 2)).roots.toFinset | t - y ^ 2 = r} ↔
        y ^ 2 = t - r := by
      rw [Finset.mem_filter, hmem]
      constructor
      · rintro ⟨-, h⟩
        rw [← h, sub_sub_cancel]
      · intro h
        have h' : t - y ^ 2 = r := by rw [h, sub_sub_cancel]
        exact ⟨h' ▸ hr', h'⟩
    rcases lt_trichotomy r t with h | h | h
    · obtain ⟨s, hs⟩ := IsRealClosed.nonneg_iff_isSquare.mp (sub_nonneg.mpr h.le)
      have hs0 : s ≠ -s := by
        intro hs'
        have hs_zero : s = 0 := by linarith
        have : t - r = 0 := by rw [hs, hs_zero, mul_zero]
        linarith
      have : {y ∈ (p.comp (C t - X ^ 2)).roots.toFinset | t - y ^ 2 = r} = {s, -s} := by
        ext y
        rw [hfib, hs, sq, mul_self_eq_mul_self_iff, Finset.mem_insert, Finset.mem_singleton]
      simp [this, Finset.card_pair hs0, h, h.ne']
    · have : {y ∈ (p.comp (C t - X ^ 2)).roots.toFinset | t - y ^ 2 = r} = {0} := by
        ext y
        rw [hfib, h, sub_self]
        simp
      rw [this, h]
      simp
    · have : {y ∈ (p.comp (C t - X ^ 2)).roots.toFinset | t - y ^ 2 = r} = ∅ := by
        ext y
        simp only [hfib, Finset.notMem_empty, iff_false]
        nlinarith [sq_nonneg y]
      simp [this, h.not_gt, h.ne]
  rw [Finset.sum_congr rfl hfiber, Finset.sum_add_distrib, ← Finset.sum_filter,
    Finset.sum_const, smul_eq_mul, mul_comm, Finset.sum_ite_eq]
  simp [mem_roots hp]

end Polynomial
