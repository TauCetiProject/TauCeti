/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Order.Bounds.Defs

/-!
# Bounded subgroups of Archimedean ordered groups

In an Archimedean linearly ordered commutative group, the powers of an element `a > 1` are
unbounded. A subgroup that is bounded above therefore contains no element other than `1`: it
would contain `a` or `a⁻¹` with `a > 1`, and with it all powers of that element.

## Main results

* `Subgroup.eq_bot_of_bddAbove` and `AddSubgroup.eq_bot_of_bddAbove`: a subgroup of an Archimedean
  linearly ordered commutative group that is bounded above is trivial.
-/

public section

namespace Subgroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G]

/-- **A bounded-above subgroup of an Archimedean ordered group is trivial**: it would otherwise
contain an element `a > 1`, whose powers are unbounded. -/
@[to_additive /-- **A bounded-above additive subgroup of an Archimedean ordered group is
trivial**: it would otherwise contain an element `a > 0`, whose multiples are unbounded. -/]
theorem eq_bot_of_bddAbove {H : Subgroup G} (hH : BddAbove (H : Set G)) : H = ⊥ := by
  obtain ⟨M, hM⟩ := hH
  refine (eq_bot_iff_forall H).mpr fun x hx ↦ ?_
  -- one of `x` and `x⁻¹` exceeds `1`, and its powers leave every bound
  have key {a : G} (ha : a ∈ H) : ¬ 1 < a := fun h ↦
    have ⟨n, hn⟩ := exists_lt_pow h M
    (hM (pow_mem ha n)).not_gt hn
  rcases lt_trichotomy x 1 with h | h | h
  · exact absurd (one_lt_inv'.mpr h) (key (inv_mem hx))
  · exact h
  · exact absurd h (key hx)

end Subgroup
