/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Hensel

/-!
# Roots in closed valuation balls

Over a Henselian discrete valuation ring, a polynomial whose derivative has order `d` at `x`
has exactly one root in the ball `v(z - x) ≥ r`, for `d < r`, if and only if
`v(F(x)) ≥ r + d`. This closed-ball version of the quantitative Hensel estimate is useful
for counting roots in residue classes.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §2.
-/

public section

open IsDiscreteValuationRing

namespace Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- A root in a ball of radius order `r ≥ d` forces the value at its center to have order
at least `r + d`, provided the derivative there has order at least `d`. No Henselian hypothesis
is needed, and infinite orders are allowed. -/
theorem le_addVal_eval_of_isRoot {F : A[X]} {x z : A} {d r : ℕ∞}
    (hd : d ≤ addVal A (F.derivative.eval x)) (hdr : d ≤ r)
    (hz : F.IsRoot z) (hball : r ≤ addVal A (z - x)) :
    r + d ≤ addVal A (F.eval x) := by
  obtain ⟨k, hk⟩ := exists_mul_sq_add_linear_part_eq_eval_add F x (z - x)
  rw [add_sub_cancel, hz.eq_zero] at hk
  have heq : F.eval x = -(k * (z - x) ^ 2 + F.derivative.eval x * (z - x)) := by
    linear_combination hk
  rw [heq, (addVal A).map_neg]
  refine (addVal A).map_le_add ?_ ?_
  · rw [addVal_mul, addVal_pow, two_nsmul]
    calc
      r + d ≤ addVal A (z - x) + addVal A (z - x) := add_le_add hball (hdr.trans hball)
      _ ≤ addVal A k + (addVal A (z - x) + addVal A (z - x)) := le_add_self
  · rw [addVal_mul, add_comm r]
    exact add_le_add hd hball

/-- A closed ball strictly smaller than the derivative scale contains exactly one root
precisely when evaluation at its center has the corresponding extra order. -/
theorem existsUnique_isRoot_le_addVal_iff [HenselianLocalRing A] (F : A[X]) (x : A)
    {d r : ℕ} (hd : addVal A (F.derivative.eval x) = d) (hdr : d < r) :
    (∃! z : A, F.IsRoot z ∧ (r : ℕ∞) ≤ addVal A (z - x)) ↔
      ((r + d : ℕ) : ℕ∞) ≤ addVal A (F.eval x) := by
  have hdr' : (d : ℕ∞) < r := by exact_mod_cast hdr
  constructor
  · rintro ⟨z, ⟨hz, hball⟩, -⟩
    simpa only [Nat.cast_add] using
      le_addVal_eval_of_isRoot hd.ge hdr'.le hz hball
  · intro hval
    have hlt : addVal A (F.derivative.eval x) + addVal A (F.derivative.eval x) <
        addVal A (F.eval x) := by
      rw [hd]
      have h : (d : ℕ∞) + d < (r + d : ℕ) := by exact_mod_cast Nat.add_lt_add_right hdr d
      exact h.trans_le hval
    obtain ⟨z, hz, hdist⟩ := F.exists_isRoot_addVal_eval_eq x hlt
    have hball : (r : ℕ∞) ≤ addVal A (z - x) := by
      rw [hdist, hd, Nat.cast_add, add_comm (r : ℕ∞)] at hval
      exact (ENat.add_le_add_iff_left (by simp)).1 hval
    refine ⟨z, ⟨hz, hball⟩, fun z' ⟨hz', hz'ball⟩ ↦ ?_⟩
    refine F.eq_of_isRoot_of_addVal_lt hz hz' ?_
    have hxlt : addVal A (F.derivative.eval x) < addVal A (z - x) := by
      rw [hd]
      exact hdr'.trans_le hball
    rw [F.addVal_derivative_eval_eq_of_lt hxlt, hd, ← sub_sub_sub_cancel_right z' z x]
    exact hdr'.trans_le
      ((le_min hz'ball hball).trans ((addVal A).map_sub _ _))

end Polynomial
