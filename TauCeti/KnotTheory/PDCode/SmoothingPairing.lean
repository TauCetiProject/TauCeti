/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Basic

/-!
# Four-endpoint closures of a smoothing

After resolving the exterior of a crossing, its four slots are paired by exterior arcs.
There are three possible perfect matchings: the two native smoothings and the opposite-slot
pairing. Closing either smoothing by an exterior pairing produces two circles when the
pairings agree and one otherwise. Circles entirely in the exterior do not enter these counts.

The two smoothing closures have equal circle counts exactly for the opposite-slot exterior
pairing. The other two cases give a merge or a split, with their directions determined here.
These are finite matching statements: no planar realization or exclusion of the opposite-slot
pairing is assumed or proved. To apply them to a diagram, one must construct its exterior
pairing and compare its circle sets with these four-endpoint closures.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, §2, for the local merge/split
  alternatives in the resolution cube.
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm

/-- A pairing of the four crossing slots is one of the two smoothings or the opposite-slot
pairing. This includes the exterior pairing that need not be realizable by disjoint planar arcs. -/
theorem isPerfectMatching_iff_eq_slotSmoothing_or_eq_oppositeCrossingSlot
    (p : Perm (Fin 4)) :
    IsPerfectMatching p ↔
      p = slotSmoothing false ∨ p = slotSmoothing true ∨ p = oppositeCrossingSlot := by
  rw [isPerfectMatching_fin_four_iff, slotSmoothing_false, slotSmoothing_true,
    oppositeCrossingSlot_eq_swap_mul_swap]
  tauto

/-- Closing a smoothing by a four-endpoint exterior pairing gives two circles if the pairings
agree, and one otherwise. The native orbit count counts both traversal directions. -/
@[simp] theorem orbitCount_slotSmoothing_mul_div_two (b : Bool) (p : Perm (Fin 4))
    (hp : IsPerfectMatching p) :
    orbitCount (slotSmoothing b * p) / 2 = if p = slotSmoothing b then 2 else 1 := by
  rw [(isPerfectMatching_slotSmoothing b).orbitCount_mul_fin_four hp]
  by_cases h : p = slotSmoothing b
  · rw [ite_eq_left h.symm, ite_eq_left h]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

/-- Changing smoothing `b` to its alternative merges two local circles precisely when the
exterior pairing is smoothing `b`. Reversing `b` gives the split criterion. -/
theorem orbitCount_slotSmoothing_not_mul_div_two_add_one_eq_iff (b : Bool) (p : Perm (Fin 4))
    (hp : IsPerfectMatching p) :
    orbitCount (slotSmoothing (!b) * p) / 2 + 1 =
      orbitCount (slotSmoothing b * p) / 2 ↔ p = slotSmoothing b := by
  rw [orbitCount_slotSmoothing_mul_div_two _ _ hp,
    orbitCount_slotSmoothing_mul_div_two _ _ hp]
  have hne := slotSmoothing_ne_slotSmoothing_not b
  split_ifs <;> simp_all

/-- The opposite-slot exterior pairing is exactly the one-to-one case: the two smoothing
closures have equal circle counts. -/
theorem orbitCount_slotSmoothing_not_mul_div_two_eq_iff (b : Bool) (p : Perm (Fin 4))
    (hp : IsPerfectMatching p) :
    orbitCount (slotSmoothing (!b) * p) / 2 =
      orbitCount (slotSmoothing b * p) / 2 ↔ p = oppositeCrossingSlot := by
  have hcases := (isPerfectMatching_iff_eq_slotSmoothing_or_eq_oppositeCrossingSlot p).mp hp
  have hne := slotSmoothing_ne_slotSmoothing_not false
  have hfalse := slotSmoothing_ne_oppositeCrossingSlot_perm false
  have htrue := slotSmoothing_ne_oppositeCrossingSlot_perm true
  simp only [Bool.not_false] at hne
  cases b <;>
    rw [orbitCount_slotSmoothing_mul_div_two _ _ hp,
      orbitCount_slotSmoothing_mul_div_two _ _ hp] <;>
    split_ifs <;> grind

end TauCeti.PDCode
