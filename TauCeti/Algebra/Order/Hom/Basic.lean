/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Preorder.Finite

/-!
# Positive values of additive homomorphisms

A nonzero additive homomorphism from a group to a linearly ordered additive group
has a positive value. This supplies positive-period exponents without imposing an
order on the source group.

If the target is moreover Archimedean, every upper set `{h | C ≤ N h}` of such a homomorphism
`N` is large: a second homomorphism with infinitely many values already takes infinitely many
values on it. This produces series of increasing period that meet infinitely many fibres of a
degree map.
-/

public section

/-- A nonzero homomorphism from an additive group to a linearly ordered additive group
has a positive value. -/
theorem AddMonoidHom.exists_pos_of_ne_zero {H G : Type*} [AddGroup H] [AddCommGroup G]
    [LinearOrder G] [IsOrderedAddMonoid G] (N : H →+ G) (hN : N ≠ 0) :
    ∃ g, 0 < N g := by
  obtain ⟨g, hg⟩ := DFunLike.ne_iff.1 hN
  simp only [AddMonoidHom.zero_apply] at hg
  rcases hg.lt_or_gt with hg | hg
  · exact ⟨-g, by simpa using hg⟩
  · exact ⟨g, hg⟩

/-- Let `N` be a nonzero homomorphism from an additive group to an Archimedean linearly ordered
additive group. If a homomorphism `δ` on the same group takes infinitely many values, it takes
infinitely many values on every upper set `{h | C ≤ N h}`. -/
theorem AddMonoidHom.infinite_image_setOf_le {H G ι : Type*} [AddGroup H] [AddCommGroup G]
    [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] [AddMonoid ι] {N : H →+ G}
    (hN : N ≠ 0) {δ : H →+ ι} (hδ : (Set.range δ).Infinite) (C : G) :
    (δ '' {h | C ≤ N h}).Infinite := by
  intro hfin
  obtain ⟨u, hu⟩ := N.exists_pos_of_ne_zero hN
  -- Far enough along the multiples of `u`, every translate of `h` has period at least `C`.
  have key : ∀ h, ∃ m : ℕ, ∀ n, m ≤ n → δ (h + n • u) ∈ δ '' {h | C ≤ N h} := by
    intro h
    obtain ⟨m, hm⟩ := Archimedean.arch (C - N h) hu
    refine ⟨m, fun n hn => Set.mem_image_of_mem _ ?_⟩
    rw [Set.mem_ofPred_eq, map_add, map_nsmul]
    exact sub_le_iff_le_add'.1 (hm.trans (nsmul_le_nsmul_left hu.le hn))
  -- The values of `δ` at these multiples repeat, so some positive multiple of `u` lies in the
  -- kernel of `δ`.
  obtain ⟨t, ht, hδt⟩ : ∃ t : ℕ, 0 < t ∧ δ (t • u) = 0 := by
    obtain ⟨m₀, hm₀⟩ := key 0
    obtain ⟨a, -, b, -, hlt, he⟩ := (Set.Ici_infinite m₀).exists_lt_map_eq_of_mapsTo
      (f := fun n : ℕ => δ (n • u)) (fun n hn => by simpa using hm₀ n hn) hfin
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    refine ⟨t + 1, t.succ_pos, ?_⟩
    have hsplit : (t + 1) • u = -(a • u) + (a + t + 1) • u := by
      simp [add_assoc, add_nsmul]
    rw [hsplit, map_add, ← he, ← map_add]
    simp
  -- Hence every value of `δ` is already a value on the upper set.
  refine hδ (hfin.subset ?_)
  rintro _ ⟨h, rfl⟩
  obtain ⟨m, hm⟩ := key h
  have hδtm : δ ((t * m) • u) = 0 := by simp [mul_nsmul, hδt]
  simpa only [map_add, hδtm, add_zero] using hm (t * m) (Nat.le_mul_of_pos_left m ht)
