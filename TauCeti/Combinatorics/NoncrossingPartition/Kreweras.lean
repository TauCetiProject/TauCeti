/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.UnorderedInterval
public import TauCeti.Combinatorics.NoncrossingPartition.Rotate
import Mathlib.Data.Finset.Max

/-!
# The Kreweras complement of a noncrossing partition

Let `s` be a finite set of positions `a₁ < a₂ < ⋯ < aₙ` in a linear order. Place a *bar* `āᵢ`
just after each position, giving the interlaced sequence `a₁ < ā₁ < a₂ < ā₂ < ⋯ < aₙ < āₙ`. We
label the bar after `x` by `x` itself, so that a partition of the bars is again a partition of
`s`. The bar after `x` lies strictly between two positions `a < b` exactly when `a ≤ x < b`.

A partition `P` of the positions and a partition `Q` of the bars are *complementary* when
together they form a noncrossing partition of the interlaced sequence. The positions strictly
between the bars after `x` and `y` are those of `Set.uIoc x y`, so a chord of `Q` joining these
two bars crosses no chord of `P` exactly when `Set.uIoc x y` contains both or neither of any two
positions in a common part of `P`. The *Kreweras complement* `K(P)` puts two bars in a common
part exactly under this condition. It is the largest partition of the bars no part of which
crosses a part of `P` (`Finpartition.le_kreweras_iff`), and it is noncrossing
(`Finpartition.isNoncrossing_kreweras`). So for noncrossing `P` it is the largest noncrossing
partition of the bars complementary to `P`
(`TauCeti.NoncrossingPartition.isGreatest_kreweras`). The complement reverses refinement and
exchanges the partition into singletons with the partition into one part, and a noncrossing
partition `P` of a nonempty set `s` and its complement have `#s + 1` parts in total.

On `NC(n)`, the noncrossing partitions of `Fin n`, the bars after the positions are themselves
positions of a rotated interlaced sequence `ā₁ < a₂ < ā₂ < ⋯ < āₙ < a₁`, and noncrossing is
invariant under rotation. Applying the complement twice therefore moves every part one step back
around the circle: `K(K(π))` is the inverse rotation of `π`. Hence `K` is a bijection of `NC(n)`,
indeed an order anti-automorphism, with inverse `σ ↦ rotate n (K(σ))`. It turns joins into
meets, so `π ⊔ σ = 1` for `σ ≤ K(π)` amounts to `K(π) ⊓ K(σ) = 0`. Writing `σ = K(ρ)` with
`π ≤ ρ`, the meet `K(π) ⊓ K(K(ρ))` is `0` exactly when `ρ = π`: no part of `K(π)` and of the inverse
rotation of `π` share two positions, while for `π < ρ` the bars before the first position of a
part `B` of `π` inside a part `C` of `ρ` and before the next position of `C` after `B` lie in a
common part of both. Hence `K(π)` is the only partition below `K(π)` that joins with `π` to `1`.

The Kreweras complement indexes the formulas for the free cumulants and the moments of products
of two free families in terms of the cumulants and moments of the two families.

## Main definitions

* `Finpartition.kreweras P` — the Kreweras complement of a finite partition `P` of `s`, as a
  partition of the bars after the positions of `s`.
* `TauCeti.NoncrossingPartition.kreweras π` — the Kreweras complement as a map `NC(s) → NC(s)`.
* `TauCeti.NoncrossingPartition.krewerasOrderIso n` — the Kreweras complement as an order
  isomorphism from `NC(n)` onto its order dual.

## Main results

* `Finpartition.mem_part_kreweras_iff` — the bars after `x` and `y` lie in a common part of
  `K(P)` exactly when `Set.uIoc x y ∩ s` is a union of parts of `P`.
* `Finpartition.le_kreweras_iff` — a partition `Q` of the bars is finer than `K(P)` exactly when
  no part of `Q` crosses a part of `P` in the interlaced order.
* `Finpartition.isNoncrossing_kreweras` — the Kreweras complement of any finite partition is
  noncrossing.
* `Finpartition.kreweras_antitone`, `Finpartition.kreweras_bot`, `Finpartition.kreweras_top` —
  the complement reverses refinement and exchanges the finest and the coarsest partitions.
* `Finpartition.IsNoncrossing.card_parts_add_card_parts_kreweras` — for a noncrossing partition
  `P` of a nonempty set `s`, `#P.parts + #(K(P)).parts = #s + 1`.
* `Finpartition.exists_mem_part_kreweras_notMem` — no nonempty interval of `s` other than `s` itself
  is a union of parts of both `P` and `K(P)`.
* `Finpartition.exists_lt_forall_mem_Ioc_of_lt_kreweras` — if a noncrossing `Q` lies strictly
  below `K(P)`, some interval `(c, c']` of `s` is a union of parts of both `P` and `Q`.
* `TauCeti.NoncrossingPartition.isGreatest_kreweras` — `K(π)` is the largest noncrossing partition
  of the bars complementary to `π`.
* `TauCeti.NoncrossingPartition.kreweras_kreweras` — on `NC(n)`, `K(K(π))` is the inverse rotation
  `(rotate n).symm π`.
* `TauCeti.NoncrossingPartition.kreweras_rotate` — the complement commutes with the rotation.
* `TauCeti.NoncrossingPartition.kreweras_bijective`,
  `TauCeti.NoncrossingPartition.kreweras_le_kreweras_iff` — on `NC(n)` the complement is a
  bijection and reverses refinement in both directions.
* `TauCeti.NoncrossingPartition.kreweras_sup`, `TauCeti.NoncrossingPartition.kreweras_inf` — on
  `NC(n)` the complement exchanges joins and meets.
* `TauCeti.NoncrossingPartition.sup_eq_top_iff_eq_kreweras`,
  `TauCeti.NoncrossingPartition.sup_kreweras_eq_top` — a noncrossing partition `σ ≤ K(π)` of
  `Fin n` joins with `π` to `1` exactly when `σ = K(π)`.

## References

* G. Kreweras, *Sur les partitions non croisées d'un cycle*, Discrete Math. 1 (1972), 333–350.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 9.
-/

public section

open Finset

namespace Finpartition

variable {α : Type*} [LinearOrder α] {s : Finset α} {P Q : Finpartition s}

/-- The relation on bars underlying the Kreweras complement: the bars after `x` and `y` are
related when `Set.uIoc x y` contains both or neither of any two positions in a common part of
`P`. -/
private def krewerasSetoid (P : Finpartition s) : Setoid α where
  r x y := ∀ a, ∀ b ∈ P.part a, a ∈ Set.uIoc x y → b ∈ Set.uIoc x y
  iseqv := by
    refine ⟨fun x a b _ ha => by simp_all, fun h a b hb ha => ?_,
      fun {x y z} hxy hyz a b hb ha => ?_⟩
    · rw [Set.uIoc_comm] at ha ⊢
      exact h a b hb ha
    · -- `Set.uIoc x z` is the symmetric difference of `Set.uIoc x y` and `Set.uIoc y z`, both of
      -- which contain `a` exactly when they contain `b`.
      have key c : c ∈ Set.uIoc x z ↔ (c ∈ Set.uIoc x y ↔ c ∉ Set.uIoc y z) := by
        simp only [Set.mem_uIoc]
        grind
      have hba := mem_part_comm.1 hb
      have hI : a ∈ Set.uIoc x y ↔ b ∈ Set.uIoc x y := ⟨hxy a b hb, hxy b a hba⟩
      have hJ : a ∈ Set.uIoc y z ↔ b ∈ Set.uIoc y z := ⟨hyz a b hb, hyz b a hba⟩
      rw [key] at ha ⊢
      rwa [← hI, ← hJ]

/-- The *Kreweras complement* `K(P)` of a finite partition `P` of a finite set `s` of positions in
a linear order. It is a partition of the bars just after the positions of `s`, each bar labelled
by the position before it: the bars after `x` and `y` lie in a common part when `Set.uIoc x y`
contains both or neither of any two positions in a common part of `P`. -/
noncomputable def kreweras (P : Finpartition s) : Finpartition s :=
  open Classical in ofSetSetoid (krewerasSetoid P) s

/-- The bars after positions `x` and `y` of `s` lie in a common part of the Kreweras complement of
`P` exactly when `Set.uIoc x y ∩ s` is a union of parts of `P`, that is, when `Set.uIoc x y`
contains both or neither of any two positions in a common part of `P`. -/
theorem mem_part_kreweras_iff {x y : α} :
    y ∈ P.kreweras.part x ↔
      x ∈ s ∧ y ∈ s ∧ ∀ a, ∀ b ∈ P.part a, a ∈ Set.uIoc x y → b ∈ Set.uIoc x y := by
  classical
  exact mem_part_ofSetSetoid_iff_rel s

/-- A partition `Q` of the bars is finer than the Kreweras complement of `P` exactly when no part
of `Q` crosses a part of `P` in the interlaced order of positions and bars: there are no positions
`a, b` in a common part of `P` and bars `x', y'` after `x, y` in a common part of `Q` with
`a < x' < b < y'` or `x' < a < y' < b`, that is, with `a ≤ x < b ≤ y` or `x < a ≤ y < b`. Together
with `isNoncrossing_kreweras`, this makes `K(P)` the largest noncrossing partition of the bars
complementary to `P` when `P` is noncrossing (`TauCeti.NoncrossingPartition.isGreatest_kreweras`).
-/
theorem le_kreweras_iff :
    Q ≤ P.kreweras ↔ ∀ x, ∀ y ∈ Q.part x, ∀ a, ∀ b ∈ P.part a,
      ¬(a ≤ x ∧ x < b ∧ b ≤ y) ∧ ¬(x < a ∧ a ≤ y ∧ y < b) := by
  rw [le_iff_forall_part_subset]
  refine ⟨fun h x y hy a b hb => ?_, fun h x y hy => ?_⟩
  · have hab := (mem_part_kreweras_iff.1 (h x hy)).2.2
    have hba := hab b a (mem_part_comm.1 hb)
    have hab := hab a b hb
    simp only [Set.mem_uIoc] at hab hba
    constructor <;> rintro ⟨h₁, h₂, h₃⟩
    · exact absurd (hba (Or.inl ⟨h₂, h₃⟩)) (by grind)
    · exact absurd (hab (Or.inl ⟨h₁, h₂⟩)) (by grind)
  · have hxs : x ∈ s := Q.part_nonempty.1 ⟨y, hy⟩
    have hys : y ∈ s := Q.part_subset x hy
    refine mem_part_kreweras_iff.2 ⟨hxs, hys, fun a b hb ha => ?_⟩
    -- A chord of `Q` that separated `a` from `b` would cross the part of `P` through them.
    have hyx := mem_part_comm.1 hy
    have hba := mem_part_comm.1 hb
    have h₁ := h x y hy a b hb
    have h₂ := h x y hy b a hba
    have h₃ := h y x hyx a b hb
    have h₄ := h y x hyx b a hba
    simp only [Set.mem_uIoc] at ha ⊢
    grind

/-- The Kreweras complement of any finite partition is noncrossing. -/
theorem isNoncrossing_kreweras (P : Finpartition s) : P.kreweras.IsNoncrossing := by
  refine isNoncrossing_iff_part.2 fun x hx y hy z hz w hw hxy hyz hzw => ?_
  refine ((P.kreweras.mem_part_iff_part_eq_part hy hx).1
    (mem_part_kreweras_iff.2 ⟨hx, hy, ?_⟩)).symm
  -- `Set.uIoc x y` is `Set.uIoc x z` minus `Set.uIoc y w`, and both contain `a` exactly when
  -- they contain `b`.
  intro a b hb ha
  have hxz := (mem_part_kreweras_iff.1 hz).2.2
  have hyw := (mem_part_kreweras_iff.1 hw).2.2
  have h₁ := hxz a b hb
  have h₂ := hyw b a (mem_part_comm.1 hb)
  simp only [Set.mem_uIoc] at ha h₁ h₂ ⊢
  grind

/-- The Kreweras complement reverses refinement. -/
theorem kreweras_antitone : Antitone (kreweras (s := s)) := by
  intro P Q hPQ
  rw [le_iff_forall_part_subset]
  intro x y hy
  obtain ⟨hx, hy, h⟩ := mem_part_kreweras_iff.1 hy
  exact mem_part_kreweras_iff.2 ⟨hx, hy, fun a b hb => h a b (part_mono hPQ a hb)⟩

/-- The Kreweras complement of the partition into singletons is the partition into one part. -/
@[simp]
theorem kreweras_bot : (⊥ : Finpartition s).kreweras = ⊤ := by
  refine top_le_iff.1 (le_kreweras_iff.2 fun x y _ a b hb => ?_)
  have hb : b = a := by
    rw [part_bot ((⊥ : Finpartition s).part_nonempty.1 ⟨b, hb⟩)] at hb
    exact mem_singleton.1 hb
  subst hb
  exact ⟨fun ⟨h₁, h₂, _⟩ => (h₁.trans_lt h₂).false, fun ⟨_, h₂, h₃⟩ => (h₂.trans_lt h₃).false⟩

/-- The Kreweras complement of the partition into one part is the partition into singletons. -/
@[simp]
theorem kreweras_top : (⊤ : Finpartition s).kreweras = ⊥ := by
  refine le_bot_iff.1 (le_iff_forall_part_subset.2 fun x y hy => ?_)
  obtain ⟨hx, hy, h⟩ := mem_part_kreweras_iff.1 hy
  rw [part_bot hx, mem_singleton]
  -- The later of `x` and `y` lies in `Set.uIoc x y`, the earlier does not.
  by_contra hyx
  rcases lt_or_gt_of_ne hyx with hyx | hxy
  · exact hyx.not_gt (Set.right_mem_uIoc.1
      (h x y (by rwa [part_top hx]) (Set.left_mem_uIoc.2 hyx)))
  · exact hxy.not_gt (Set.left_mem_uIoc.1
      (h y x (by rwa [part_top hy]) (Set.right_mem_uIoc.2 hxy)))

/-- If the bars after positions `y < x` lie in a common part of the Kreweras complement of `P`,
then the part of `P` through `x` lies in `(y, x]`. -/
private theorem lt_and_le_of_mem_part_kreweras {x y : α} (hyx : y < x)
    (h : x ∈ P.kreweras.part y) {b : α} (hb : b ∈ P.part x) : y < b ∧ b ≤ x := by
  have h := (mem_part_kreweras_iff.1 h).2.2 x b hb
  simpa [Set.uIoc_of_le hyx.le, hyx] using h

/-- Let `P` be noncrossing, let `x` be the last position of its part, and let that part miss the
first position `m` of `s`. Then the bar after `x` lies in a common part of the Kreweras complement
with the bar just before the first position of the part of `P` through `x`. -/
private theorem IsNoncrossing.exists_lt_mem_part_kreweras (hP : P.IsNoncrossing) {x m : α}
    (hx : x ∈ s) (hxmax : ∀ b ∈ P.part x, b ≤ x) (hm : m ∈ s) (hmmin : ∀ z ∈ s, m ≤ z)
    (hmx : m ∉ P.part x) : ∃ y ∈ s, y < x ∧ x ∈ P.kreweras.part y := by
  classical
  -- `a` is the first position of the part through `x`, and `y` is the position just before `a`.
  obtain ⟨a, haA, hamin⟩ := (P.part x).exists_min_image id ⟨x, P.mem_part_self.2 hx⟩
  have has : a ∈ s := P.part_subset x haA
  have hma : m < a := lt_of_le_of_ne (hmmin a has) fun h => hmx (h ▸ haA)
  obtain ⟨y, hy, hymax⟩ := ({z ∈ s | z < a}).exists_max_image id ⟨m, mem_filter.2 ⟨hm, hma⟩⟩
  obtain ⟨hys, hya⟩ := mem_filter.1 hy
  have hyx : y < x := hya.trans_le (hamin x (P.mem_part_self.2 hx))
  refine ⟨y, hys, hyx, mem_part_kreweras_iff.2 ⟨hys, hx, fun c d hd hc => ?_⟩⟩
  rw [Set.uIoc_of_le hyx.le, Set.mem_Ioc] at hc ⊢
  have hcs : c ∈ s := P.part_nonempty.1 ⟨d, hd⟩
  have hds : d ∈ s := P.part_subset c hd
  have hac : a ≤ c := not_lt.1 fun hca => hc.1.not_ge (hymax c (mem_filter.2 ⟨hcs, hca⟩))
  have hpa : P.part a = P.part x := P.part_eq_of_mem (P.part_mem.2 hx) haA
  have hdc : P.part d = P.part c := P.part_eq_of_mem (P.part_mem.2 hcs) hd
  by_cases hcx : P.part c = P.part x
  · have hdx : d ∈ P.part x := hcx ▸ hd
    exact ⟨hya.trans_le (hamin d hdx), hxmax d hdx⟩
  -- Otherwise `a < c < x`, and a position `d` of the part through `c` outside `(y, x]` would
  -- make that part cross the part through `a` and `x`.
  have hac : a < c := lt_of_le_of_ne hac fun h => hcx (h ▸ hpa)
  have hcx' : c < x := lt_of_le_of_ne hc.2 fun h => hcx (h ▸ rfl)
  refine ⟨lt_of_not_ge fun hdy => hcx ?_, le_of_not_gt fun hxd => hcx ?_⟩
  · exact hdc.symm.trans ((hP.part_eq_part hds has hdc hpa (hdy.trans_lt hya) hac hcx').trans hpa)
  · exact ((hP.part_eq_part has hcs hpa hdc.symm hac hcx' hxd).symm.trans hpa)

/-- For a noncrossing partition `P` of a nonempty finite set `s` in a linear order, `P` and its
Kreweras complement have `#s + 1` parts in total. -/
theorem IsNoncrossing.card_parts_add_card_parts_kreweras (hP : P.IsNoncrossing)
    (hs : s.Nonempty) : #P.parts + #P.kreweras.parts = #s + 1 := by
  classical
  obtain ⟨m, hm, hmmin⟩ := s.exists_min_image id hs
  -- The positions that are not first in their part of `K(P)` are exactly the last positions of the
  -- parts of `P` other than the part through `m`.
  have key : {x ∈ s | ¬∀ y ∈ P.kreweras.part x, x ≤ y} =
      {x ∈ s | (∀ y ∈ P.part x, y ≤ x) ∧ m ∉ P.part x} := by
    ext x
    simp only [mem_filter, not_forall, not_le, exists_prop]
    refine and_congr_right fun hx => ⟨fun ⟨y, hy, hyx⟩ => ?_, fun ⟨hxmax, hmx⟩ => ?_⟩
    · have h := fun {b} => lt_and_le_of_mem_part_kreweras (P := P) (b := b) hyx (mem_part_comm.1 hy)
      exact ⟨fun b hb => (h hb).2,
        fun hmx => (hmmin y (P.kreweras.part_subset x hy)).not_gt (h hmx).1⟩
    · obtain ⟨y, -, hyx, hy⟩ := hP.exists_lt_mem_part_kreweras hx hxmax hm hmmin hmx
      exact ⟨y, mem_part_comm.1 hy, hyx⟩
  -- Exactly one part of `P` contains `m`, and it has one last position.
  have hone : #{x ∈ s | (∀ y ∈ P.part x, y ≤ x) ∧ m ∈ P.part x} = 1 := by
    refine le_antisymm (card_le_one.2 fun x hx x' hx' => ?_) (card_pos.2 ?_)
    · obtain ⟨hxs, hxmax, hmx⟩ := mem_filter.1 hx
      obtain ⟨hxs', hxmax', hmx'⟩ := mem_filter.1 hx'
      have h : P.part x = P.part x' := ((P.part_eq_of_mem (P.part_mem.2 hxs) hmx).symm.trans
        (P.part_eq_of_mem (P.part_mem.2 hxs') hmx'))
      exact le_antisymm (hxmax' x (h ▸ P.mem_part_self.2 hxs))
        (hxmax x' (h ▸ P.mem_part_self.2 hxs'))
    · obtain ⟨x, hx, hxmax⟩ := (P.part m).exists_max_image id ⟨m, P.mem_part_self.2 hm⟩
      have hxm : P.part x = P.part m := P.part_eq_of_mem (P.part_mem.2 hm) hx
      exact ⟨x, mem_filter.2 ⟨P.part_subset m hx, fun y hy => hxmax y (hxm ▸ hy),
        hxm ▸ P.mem_part_self.2 hm⟩⟩
  have hK := card_filter_add_card_filter_not (s := s)
    (fun x => ∀ y ∈ P.kreweras.part x, x ≤ y)
  have hP' := card_filter_add_card_filter_not (s := {x ∈ s | ∀ y ∈ P.part x, y ≤ x})
    (fun x => m ∈ P.part x)
  rw [card_filter_forall_mem_part_ge, key] at hK
  rw [card_filter_forall_mem_part_le, filter_filter, filter_filter, hone] at hP'
  omega

/-- Let `T` be a nonempty union of parts of `P` that is an interval of `s` but not all of `s`. Then
`T` is not a union of parts of the Kreweras complement `K(P)`: the bar after the last position `v`
of `T` lies in a common part of `K(P)` with the bar just before `T`, or, if `T` contains the first
position of `s`, with the bar after the last position of `s`. -/
theorem exists_mem_part_kreweras_notMem {T : Finset α} (hTs : T ⊆ s)
    (hconv : ∀ x ∈ T, ∀ z ∈ T, ∀ y ∈ s, x ≤ y → y ≤ z → y ∈ T) (hT : T.Nonempty)
    (hsT : ∃ c ∈ s, c ∉ T) (hP : ∀ x ∈ T, P.part x ⊆ T) :
    ∃ x ∈ T, ∃ y ∈ P.kreweras.part x, y ∉ T := by
  have hu := T.min'_mem hT
  have hv := T.max'_mem hT
  have hPT a (b) (hb : b ∈ P.part a) : a ∈ T ↔ b ∈ T :=
    ⟨fun ha => hP a ha hb, fun hb' => hP b hb' (mem_part_comm.1 hb)⟩
  -- If the positions of `s` in `Set.uIoc v y` form `T` or its complement, the bars after `v` and
  -- `y` lie in a common part of `K(P)`.
  have hK {y : α} (hy : y ∈ s) (β : Prop)
      (hTy : ∀ z ∈ s, z ∈ Set.uIoc (T.max' hT) y ↔ (z ∈ T ↔ β)) :
      y ∈ P.kreweras.part (T.max' hT) := by
    refine mem_part_kreweras_iff.2 ⟨hTs hv, hy, fun a b hb ha => ?_⟩
    have has : a ∈ s := P.part_nonempty.1 ⟨b, hb⟩
    rw [hTy b (P.part_subset a hb), ← hPT a b hb, ← hTy a has]
    exact ha
  by_cases hw : ∃ w ∈ s, w < T.min' hT
  · -- The bar before `T` is the bar after the position `w` just before `T`.
    obtain ⟨w, hw, hwmax⟩ := {z ∈ s | z < T.min' hT}.exists_max_image id
      (let ⟨w, hws, hwu⟩ := hw; ⟨w, mem_filter.2 ⟨hws, hwu⟩⟩)
    obtain ⟨hws, hwu⟩ := mem_filter.1 hw
    refine ⟨_, hv, w, hK hws True fun z hz => ?_, fun hwT => hwu.not_ge (T.min'_le w hwT)⟩
    rw [Set.uIoc_comm, Set.uIoc_of_le (hwu.le.trans (T.min'_le _ hv)), Set.mem_Ioc, iff_true]
    refine ⟨fun ⟨hwz, hzv⟩ => hconv _ hu _ hv z hz
      (not_lt.1 fun hzu => hwz.not_ge (hwmax z (mem_filter.2 ⟨hz, hzu⟩))) hzv,
      fun hzT => ⟨hwu.trans_le (T.min'_le z hzT), T.le_max' z hzT⟩⟩
  · -- Otherwise `T` starts at the first position of `s` and misses its last position `m`.
    replace hw : ∀ z ∈ s, T.min' hT ≤ z := fun z hz => not_lt.1 fun h => hw ⟨z, hz, h⟩
    have hs : s.Nonempty := hT.mono hTs
    have hgt : ∀ z ∈ s, z ∉ T → T.max' hT < z := fun z hz hzT =>
      lt_of_not_ge fun hzv => hzT (hconv _ hu _ hv z hz (hw z hz) hzv)
    obtain ⟨c, hcs, hcT⟩ := hsT
    have hm := s.max'_mem hs
    have hvm : T.max' hT < s.max' hs := (hgt c hcs hcT).trans_le (s.le_max' c hcs)
    refine ⟨_, hv, s.max' hs, hK hm False fun z hz => ?_,
      fun hmT => hvm.not_ge (T.le_max' _ hmT)⟩
    rw [Set.uIoc_of_le hvm.le, Set.mem_Ioc, iff_false]
    exact ⟨fun ⟨hvz, _⟩ hzT => hvz.not_ge (T.le_max' z hzT),
      fun hzT => ⟨hgt z hz hzT, s.le_max' z hz⟩⟩

/-- Let `Q ≤ K(P)`, and let `c < c'` lie in a part `C` of `K(P)` such that `C ∩ (c, c']` is a union
of parts of `Q`. Then `(c, c']` is a union of parts of `P` and a union of parts of `Q`: a part of
`K(P)` other than `C` meeting `(c, c')` lies inside it, as `K(P)` is noncrossing. -/
private theorem forall_mem_Ioc_of_mem_part_kreweras (hle : Q ≤ P.kreweras) {x c c' : α}
    (hx : x ∈ s) (hc : c ∈ P.kreweras.part x) (hc' : c' ∈ P.kreweras.part x) (hcc' : c < c')
    (hC : ∀ y ∈ P.kreweras.part x, c < y → y ≤ c' → ∀ z ∈ Q.part y, c < z ∧ z ≤ c') :
    (∀ a, ∀ b ∈ P.part a, c < a → a ≤ c' → c < b ∧ b ≤ c') ∧
      ∀ a, ∀ b ∈ Q.part a, c < a → a ≤ c' → c < b ∧ b ≤ c' := by
  have hK := isNoncrossing_kreweras P
  have hcs := P.kreweras.part_subset x hc
  have hc's := P.kreweras.part_subset x hc'
  have hxc := (P.kreweras.mem_part_iff_part_eq_part hcs hx).1 hc
  have hxc' := (P.kreweras.mem_part_iff_part_eq_part hc's hx).1 hc'
  refine ⟨fun a b hb hca hac' => ?_, fun a b hb hca hac' => ?_⟩
  · have := (mem_part_kreweras_iff.1 (hxc ▸ hxc' ▸ P.kreweras.mem_part_self.2 hc's)).2.2 a b hb
    rw [Set.uIoc_of_le hcc'.le] at this
    exact this ⟨hca, hac'⟩
  by_cases haC : a ∈ P.kreweras.part x
  · exact hC a haC hca hac' b hb
  -- The part of `K(P)` through `a` contains `b` and would cross `C` if `b ∉ (c, c']`.
  have has : a ∈ s := Q.part_nonempty.1 ⟨b, hb⟩
  have hbs : b ∈ s := Q.part_subset a hb
  have hab : P.kreweras.part a = P.kreweras.part b :=
    ((P.kreweras.mem_part_iff_part_eq_part hbs has).1 (part_mono hle a hb)).symm
  have haC' : P.kreweras.part a ≠ P.kreweras.part x := fun h =>
    haC (h ▸ P.kreweras.mem_part_self.2 has)
  have hac' : a < c' := lt_of_le_of_ne hac' fun h => haC (h ▸ hc')
  by_contra hbc
  rcases not_and_or.1 hbc with hbc | hbc
  · have hbc : b < c := lt_of_le_of_ne (not_lt.1 hbc) fun h => haC' (by rw [hab, h, hxc])
    exact haC' (hab.trans ((hK.part_eq_part hbs hcs hab.symm (hxc.trans hxc'.symm) hbc hca
      hac').trans hxc))
  · exact haC' ((hK.part_eq_part hcs has (hxc.trans hxc'.symm) hab hca hac'
      (not_le.1 hbc)).symm.trans hxc)

/-- Let `Q ≤ K(P)`, and let `E` be a part of `Q` inside a part `C` of `K(P)`, other than `C`,
containing every position of `C` between two of its positions. Then there are `c < c'` in `C` such
that `C ∩ (c, c']` is a union of parts of `Q`: it is `E` if `E` misses the first position of `C`,
and `C \ E` otherwise. -/
private theorem exists_lt_forall_mem_part_kreweras (hle : Q ≤ P.kreweras) {x e : α} (hx : x ∈ s)
    (heC : e ∈ P.kreweras.part x) (hEne : Q.part e ≠ P.kreweras.part x)
    (hEint : ∀ y ∈ Q.part e, ∀ z ∈ Q.part e, ∀ w ∈ P.kreweras.part x, y < w → w < z →
      w ∈ Q.part e) :
    ∃ c ∈ P.kreweras.part x, ∃ c' ∈ P.kreweras.part x, c < c' ∧
      ∀ y ∈ P.kreweras.part x, c < y → y ≤ c' → ∀ z ∈ Q.part y, c < z ∧ z ≤ c' := by
  set C := P.kreweras.part x
  have hCs : C ⊆ s := P.kreweras.part_subset x
  have hQC : ∀ y ∈ C, Q.part y ⊆ C := fun y hy =>
    (part_mono hle y).trans ((P.kreweras.part_eq_of_mem (P.kreweras.part_mem.2 hx) hy).subset)
  have hes : e ∈ s := hCs heC
  have hEsub := hQC e heC
  have hEnon : (Q.part e).Nonempty := ⟨e, Q.mem_part_self.2 hes⟩
  have hCnon : C.Nonempty := ⟨x, P.kreweras.mem_part_self.2 hx⟩
  -- Positions of `C` between the first and the last position of `E` lie in `E`.
  have hEint' : ∀ y ∈ C, (Q.part e).min' hEnon ≤ y → y ≤ (Q.part e).max' hEnon →
      y ∈ Q.part e := fun y hy h₁ h₂ => by
    rcases h₁.lt_or_eq with h₁ | rfl
    · rcases h₂.lt_or_eq with h₂ | rfl
      · exact hEint _ (min'_mem _ _) _ (max'_mem _ _) y hy h₁ h₂
      · exact max'_mem _ _
    · exact min'_mem _ _
  -- A part of `Q` inside `C` is `E` or disjoint from it.
  have hQE : ∀ y ∈ C, ∀ z ∈ Q.part y, z ∈ Q.part e → y ∈ Q.part e := fun y hy z hz hzE => by
    rw [← Q.part_eq_of_mem (Q.part_mem.2 hes) hzE, Q.part_eq_of_mem (Q.part_mem.2 (hCs hy)) hz]
    exact Q.mem_part_self.2 (hCs hy)
  by_cases hmE : C.min' hCnon ∈ Q.part e
  · -- `E` starts at the first position of `C`: take `c` the last position of `E` and `c'` the
    -- last position of `C`.
    have hgt : ∀ y ∈ C, y ∉ Q.part e → (Q.part e).max' hEnon < y := fun y hy hyE =>
      lt_of_not_ge fun hyv => hyE (hEint' y hy ((min'_le _ _ hmE).trans (C.min'_le y hy)) hyv)
    obtain ⟨y, hy, hyE⟩ : ∃ y ∈ C, y ∉ Q.part e := by
      by_contra! h
      exact hEne (Subset.antisymm hEsub h)
    refine ⟨(Q.part e).max' hEnon, hEsub (max'_mem _ _), C.max' hCnon, C.max'_mem hCnon,
      (hgt y hy hyE).trans_le (C.le_max' y hy), fun y' hy' hcy' _ z hz => ?_⟩
    have hy'E : y' ∉ Q.part e := fun h => hcy'.not_ge ((Q.part e).le_max' y' h)
    have hzC := hQC y' hy' hz
    exact ⟨hgt z hzC fun hzE => hy'E (hQE y' hy' z hz hzE), C.le_max' z hzC⟩
  · -- Otherwise take `c` the last position of `C` before `E` and `c'` the last position of `E`.
    have hlt : C.min' hCnon < (Q.part e).min' hEnon :=
      lt_of_le_of_ne (C.min'_le _ (hEsub (min'_mem _ _))) fun h => hmE (h ▸ min'_mem _ _)
    obtain ⟨c, hc, hcmax⟩ := {y ∈ C | y < (Q.part e).min' hEnon}.exists_max_image id
      ⟨_, mem_filter.2 ⟨C.min'_mem hCnon, hlt⟩⟩
    obtain ⟨hcC, hcE⟩ := mem_filter.1 hc
    refine ⟨c, hcC, (Q.part e).max' hEnon, hEsub (max'_mem _ _),
      hcE.trans_le (min'_le _ _ (max'_mem _ _)), fun y' hy' hcy' hy'v z hz => ?_⟩
    have hy'E : y' ∈ Q.part e := hEint' y' hy'
      (not_lt.1 fun h => hcy'.not_ge (hcmax y' (mem_filter.2 ⟨hy', h⟩))) hy'v
    have hzE : z ∈ Q.part e := (Q.part_eq_of_mem (Q.part_mem.2 hes) hy'E) ▸ hz
    exact ⟨hcE.trans_le ((Q.part e).min'_le z hzE), (Q.part e).le_max' z hzE⟩

/-- Let `Q ≤ K(P)` be noncrossing and different from `K(P)`. Then there are positions `c < c'` of
`s` such that `(c, c']` is a union of parts of `P` and a union of parts of `Q`. They are found in a
part `C` of `K(P)` that `Q` splits, using an interval part of the restriction of `Q` to `C`. -/
theorem exists_lt_forall_mem_Ioc_of_lt_kreweras (hQ : Q.IsNoncrossing)
    (hle : Q ≤ P.kreweras) (hne : Q ≠ P.kreweras) :
    ∃ c ∈ s, ∃ c' ∈ s, c < c' ∧
      (∀ a, ∀ b ∈ P.part a, c < a → a ≤ c' → c < b ∧ b ≤ c') ∧
        ∀ a, ∀ b ∈ Q.part a, c < a → a ≤ c' → c < b ∧ b ≤ c' := by
  obtain ⟨x, hx, hQx⟩ : ∃ x ∈ s, Q.part x ≠ P.kreweras.part x := by
    by_contra! h
    exact hne (ext_of_part h)
  have hCs : P.kreweras.part x ⊆ s := P.kreweras.part_subset x
  obtain ⟨E, hE, hEint⟩ := (hQ.restrict hCs).exists_interval_mem_parts
    ⟨x, P.kreweras.mem_part_self.2 hx⟩
  obtain ⟨e, heE⟩ := (Q.restrict hCs).nonempty_of_mem_parts hE
  have heC : e ∈ P.kreweras.part x := (Q.restrict hCs).part_subset e
    (((Q.restrict hCs).part_eq_of_mem hE heE) ▸ heE)
  -- The parts of the restriction of `Q` to `C` are the parts of `Q` inside `C`.
  have hEe : E = Q.part e := by
    rw [← (Q.restrict hCs).part_eq_of_mem hE heE, part_restrict _ _ heC, inter_eq_left]
    exact (part_mono hle e).trans (P.kreweras.part_eq_of_mem (P.kreweras.part_mem.2 hx) heC).le
  subst hEe
  have hEne : Q.part e ≠ P.kreweras.part x := fun h => hQx
    ((Q.part_eq_of_mem (Q.part_mem.2 (hCs heC)) (h ▸ P.kreweras.mem_part_self.2 hx)).trans h)
  obtain ⟨c, hc, c', hc', hcc', hC⟩ := exists_lt_forall_mem_part_kreweras hle hx heC hEne hEint
  exact ⟨c, hCs hc, c', hCs hc', hcc', forall_mem_Ioc_of_mem_part_kreweras hle hx hc hc' hcc' hC⟩

end Finpartition

namespace TauCeti.NoncrossingPartition

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The Kreweras complement as a map `NC(s) → NC(s)`: the Kreweras complement
`Finpartition.kreweras` of a noncrossing partition of `s`, with the bars after the positions of
`s` labelled by those positions. -/
noncomputable def kreweras (π : NoncrossingPartition s) : NoncrossingPartition s :=
  ⟨π.1.kreweras, π.1.isNoncrossing_kreweras⟩

@[simp, norm_cast]
theorem coe_kreweras (π : NoncrossingPartition s) :
    ((kreweras π : NoncrossingPartition s) : Finpartition s) = (π : Finpartition s).kreweras :=
  (rfl)

/-- The Kreweras complement `K(π)` is the largest noncrossing partition of the bars
complementary to `π`: no part of it crosses a part of `π` in the interlaced order
`a₁ < ā₁ < a₂ < ā₂ < ⋯` of positions and bars. -/
theorem isGreatest_kreweras (π : NoncrossingPartition s) :
    IsGreatest {σ : NoncrossingPartition s | ∀ x, ∀ y ∈ σ.1.part x, ∀ a, ∀ b ∈ π.1.part a,
      ¬(a ≤ x ∧ x < b ∧ b ≤ y) ∧ ¬(x < a ∧ a ≤ y ∧ y < b)} (kreweras π) :=
  ⟨Finpartition.le_kreweras_iff.1 le_rfl, fun _ hσ => Finpartition.le_kreweras_iff.2 hσ⟩

/-- The Kreweras complement reverses refinement on `NC(s)`. -/
theorem kreweras_antitone : Antitone (kreweras (s := s)) :=
  fun _ _ h => Finpartition.kreweras_antitone h

/-- The Kreweras complement of the bottom of `NC(s)` is its top. -/
@[simp]
theorem kreweras_bot : kreweras (⊥ : NoncrossingPartition s) = ⊤ :=
  Subtype.ext Finpartition.kreweras_bot

/-- The Kreweras complement of the top of `NC(s)` is its bottom. -/
@[simp]
theorem kreweras_top : kreweras (⊤ : NoncrossingPartition s) = ⊥ :=
  Subtype.ext Finpartition.kreweras_top

/-- A noncrossing partition `π` of a nonempty finite set `s` and its Kreweras complement have
`#s + 1` parts in total. -/
theorem card_parts_add_card_parts_kreweras (π : NoncrossingPartition s) (hs : s.Nonempty) :
    #(π : Finpartition s).parts + #(kreweras π : Finpartition s).parts = #s + 1 :=
  π.2.card_parts_add_card_parts_kreweras hs

/-! ### The square of the Kreweras complement on `NC(n)` -/

section Fin

variable {n : ℕ}

/-- The inverse rotation of `π` refines `K(K(π))`: two positions whose successors lie in a common
part of `π` lie in a common part of `K(K(π))`. A chord of `K(π)` between the bars after `a < b`
that separated them would separate the successors as well. -/
private theorem rotate_symm_le_kreweras_kreweras
    (π : NoncrossingPartition (univ : Finset (Fin n))) :
    (rotate n).symm π ≤ kreweras (kreweras π) := by
  cases n with
  | zero => exact (Subsingleton.elim _ _).le
  | succ n =>
  refine Subtype.coe_le_coe.1 ?_
  rw [coe_kreweras, coe_kreweras]
  refine Finpartition.le_kreweras_iff.2 fun x y hy a b hb => ?_
  rw [mem_part_rotate_symm] at hy
  have hK := (Finpartition.mem_part_kreweras_iff.1 hb).2.2
  have hval (i : Fin (n + 1)) :
      (finRotate (n + 1) i : ℕ) = if (i : ℕ) = n then 0 else (i : ℕ) + 1 := by
    rw [coe_finRotate]
    simp only [Fin.ext_iff, Fin.val_last]
  constructor
  · rintro ⟨hax, hxb, hby⟩
    have h := hK _ _ hy (by
      simp only [Set.mem_uIoc, Fin.lt_def, Fin.le_def, hval] at hax hxb hby ⊢
      split_ifs <;> omega)
    simp only [Set.mem_uIoc, Fin.lt_def, Fin.le_def, hval] at hax hxb hby h
    have := y.is_lt
    split_ifs at h <;> omega
  · rintro ⟨hxa, hay, hyb⟩
    have h := hK _ _ (Finpartition.mem_part_comm.1 hy) (by
      simp only [Set.mem_uIoc, Fin.lt_def, Fin.le_def, hval] at hxa hay hyb ⊢
      have := b.is_lt
      split_ifs <;> omega)
    simp only [Set.mem_uIoc, Fin.lt_def, Fin.le_def, hval] at hxa hay hyb h
    have := b.is_lt
    split_ifs at h <;> omega

/-- The square of the Kreweras complement on `NC(n)` is the inverse rotation: the parts of
`K(K(π))` are the parts of `π` moved along `i ↦ i - 1`, with `0` going to the last position. -/
@[simp]
theorem kreweras_kreweras (π : NoncrossingPartition (univ : Finset (Fin n))) :
    kreweras (kreweras π) = (rotate n).symm π := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact Subsingleton.elim _ _
  -- `(rotate n).symm π` refines `K(K(π))`, and both have as many parts as `π`.
  refine (Subtype.ext (Finpartition.eq_of_le_of_card_parts_le
    (rotate_symm_le_kreweras_kreweras π) ?_)).symm
  have hne : (univ : Finset (Fin n)).Nonempty := univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩
  have h₁ := card_parts_add_card_parts_kreweras π hne
  have h₂ := card_parts_add_card_parts_kreweras (kreweras π) hne
  rw [parts_rotate_symm, card_image_of_injective _ (map_injective _)]
  omega

/-- The Kreweras complement commutes with the rotation of `NC(n)`. -/
theorem kreweras_rotate (π : NoncrossingPartition (univ : Finset (Fin n))) :
    kreweras (rotate n π) = rotate n (kreweras π) := by
  have h := kreweras_kreweras (kreweras (rotate n π))
  rw [kreweras_kreweras (rotate n π), OrderIso.symm_apply_apply] at h
  rw [h, OrderIso.apply_symm_apply]

/-- The Kreweras complement on `NC(n)` reverses refinement in both directions. -/
@[simp]
theorem kreweras_le_kreweras_iff {π σ : NoncrossingPartition (univ : Finset (Fin n))} :
    kreweras π ≤ kreweras σ ↔ σ ≤ π :=
  ⟨fun h => by simpa using kreweras_antitone h, fun h => kreweras_antitone h⟩

/-- The Kreweras complement is a bijection of `NC(n)`; its inverse is `σ ↦ rotate n (K(σ))`. -/
theorem kreweras_bijective :
    Function.Bijective (kreweras : NoncrossingPartition (univ : Finset (Fin n)) → _) :=
  ⟨fun _ _ h => le_antisymm (kreweras_le_kreweras_iff.1 h.ge) (kreweras_le_kreweras_iff.1 h.le),
    fun σ => ⟨rotate n (kreweras σ), by
      rw [kreweras_rotate, kreweras_kreweras, OrderIso.apply_symm_apply]⟩⟩

/-- The Kreweras complement on `NC(n)` is injective. -/
@[simp]
theorem kreweras_inj {π σ : NoncrossingPartition (univ : Finset (Fin n))} :
    kreweras π = kreweras σ ↔ π = σ :=
  kreweras_bijective.1.eq_iff

variable (n) in
/-- The Kreweras complement as an order isomorphism from `NC(n)` onto its order dual, so an order
anti-automorphism of `NC(n)`. Its inverse sends `σ` to `rotate n (K(σ))`. -/
noncomputable def krewerasOrderIso :
    NoncrossingPartition (univ : Finset (Fin n)) ≃o (NoncrossingPartition (univ : Finset (Fin n)))ᵒᵈ
    where
  toFun π := OrderDual.toDual (kreweras π)
  invFun σ := rotate n (kreweras (OrderDual.ofDual σ))
  left_inv π := by simp
  right_inv σ := by simp [kreweras_rotate]
  map_rel_iff' := by simp

/-- The order isomorphism `krewerasOrderIso n` sends `π` to its Kreweras complement. -/
@[simp]
theorem krewerasOrderIso_apply (π : NoncrossingPartition (univ : Finset (Fin n))) :
    krewerasOrderIso n π = OrderDual.toDual (kreweras π) :=
  (rfl)

/-- The inverse of `krewerasOrderIso n` sends `σ` to the rotation of its Kreweras complement. -/
@[simp]
theorem krewerasOrderIso_symm_apply
    (σ : (NoncrossingPartition (univ : Finset (Fin n)))ᵒᵈ) :
    (krewerasOrderIso n).symm σ = rotate n (kreweras (OrderDual.ofDual σ)) :=
  (rfl)

/-- The Kreweras complement on `NC(n)` turns joins into meets. -/
@[simp]
theorem kreweras_sup (π σ : NoncrossingPartition (univ : Finset (Fin n))) :
    kreweras (π ⊔ σ) = kreweras π ⊓ kreweras σ :=
  congrArg OrderDual.ofDual ((krewerasOrderIso n).map_sup π σ)

/-- The Kreweras complement on `NC(n)` turns meets into joins. -/
@[simp]
theorem kreweras_inf (π σ : NoncrossingPartition (univ : Finset (Fin n))) :
    kreweras (π ⊓ σ) = kreweras π ⊔ kreweras σ :=
  congrArg OrderDual.ofDual ((krewerasOrderIso n).map_inf π σ)

/-- No two distinct positions lie in a common part both of `K(π)` and of the inverse rotation of
`π`: if the bars after `x < y` lie in a common part of `K(π)`, then the part of `π` through the
position after `x` stays in `(x, y]`, so it does not contain the position after `y`. -/
private theorem eq_of_mem_part_kreweras_of_mem_part_rotate_symm
    (π : NoncrossingPartition (univ : Finset (Fin n))) {x y : Fin n}
    (hK : y ∈ π.1.kreweras.part x) (hR : y ∈ ((rotate n).symm π).1.part x) : y = x := by
  cases n with
  | zero => exact x.elim0
  | succ n =>
  have hval (i : Fin (n + 1)) :
      (finRotate (n + 1) i : ℕ) = if (i : ℕ) = n then 0 else (i : ℕ) + 1 := by
    rw [coe_finRotate]
    simp only [Fin.ext_iff, Fin.val_last]
  -- By symmetry of both relations, it suffices to rule out `x < y`.
  have key {x y : Fin (n + 1)} (hxy : x < y) (hK : y ∈ π.1.kreweras.part x)
      (hR : y ∈ ((rotate (n + 1)).symm π).1.part x) : False := by
    rw [mem_part_rotate_symm] at hR
    have hy := y.is_lt
    rw [Fin.lt_def] at hxy
    have h := (Finpartition.mem_part_kreweras_iff.1 hK).2.2 _ _ hR (by
      rw [Set.uIoc_of_le (Fin.le_def.2 hxy.le), Set.mem_Ioc, Fin.lt_def, Fin.le_def, hval]
      split_ifs <;> omega)
    rw [Set.uIoc_of_le (Fin.le_def.2 hxy.le), Set.mem_Ioc, Fin.lt_def, Fin.le_def, hval] at h
    split_ifs at h <;> omega
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · exact (key hxy hK hR).elim
  · rfl
  · exact (key hxy (Finpartition.mem_part_comm.1 hK) (Finpartition.mem_part_comm.1 hR)).elim

/-- The Kreweras complement of `π` and the inverse rotation of `π` have no common part with two
positions. -/
private theorem kreweras_inf_rotate_symm_eq_bot
    (π : NoncrossingPartition (univ : Finset (Fin n))) :
    kreweras π ⊓ (rotate n).symm π = ⊥ := by
  refine Subtype.ext ?_
  rw [coe_inf, coe_kreweras, coe_bot]
  refine le_bot_iff.1 (Finpartition.le_iff_forall_part_subset.2 fun x y hy => ?_)
  rw [Finpartition.part_bot (mem_univ x), mem_singleton]
  exact eq_of_mem_part_kreweras_of_mem_part_rotate_symm π
    (Finpartition.part_mono inf_le_left x hy) (Finpartition.part_mono inf_le_right x hy)

/-- Let `m < t` be positions in a common part of `ρ` such that `[m, t)` is a union of parts of `π`.
Then the positions `x ≠ y` before `m` and before `t` lie in a common part both of `K(π)` and of the
inverse rotation of `ρ`: the positions strictly between the bars after `x` and after `y` are those
of `[m, t)`, or of its complement if `m = 0`. -/
private theorem exists_ne_mem_part_kreweras_mem_part_rotate_symm_of_forall
    {π ρ : NoncrossingPartition (univ : Finset (Fin n))} {m t : Fin n} (hmt : m < t)
    (hρ : t ∈ ρ.1.part m) (hint : ∀ a b, b ∈ π.1.part a → m ≤ a → a < t → m ≤ b ∧ b < t) :
    ∃ x y, x ≠ y ∧ y ∈ π.1.kreweras.part x ∧ y ∈ ((rotate n).symm ρ).1.part x := by
  cases n with
  | zero => exact m.elim0
  | succ n =>
  have hval (i : Fin (n + 1)) :
      (finRotate (n + 1) i : ℕ) = if (i : ℕ) = n then 0 else (i : ℕ) + 1 := by
    rw [coe_finRotate]
    simp only [Fin.ext_iff, Fin.val_last]
  set x := (finRotate (n + 1)).symm m
  set y := (finRotate (n + 1)).symm t
  have hxm : finRotate (n + 1) x = m := Equiv.apply_symm_apply _ _
  have hyt : finRotate (n + 1) y = t := Equiv.apply_symm_apply _ _
  have hm := hval x
  have ht := hval y
  rw [hxm] at hm
  rw [hyt] at ht
  rw [Fin.lt_def] at hmt
  have hI (a : Fin (n + 1)) :
      a ∈ Set.uIoc x y ↔ if (m : ℕ) = 0 then t ≤ a else m ≤ a ∧ a < t := by
    have := x.is_lt
    have := y.is_lt
    simp only [Set.mem_uIoc, Fin.lt_def, Fin.le_def]
    split_ifs at hm ht ⊢ <;> omega
  refine ⟨x, y, fun h => hmt.ne (by rw [← hxm, ← hyt, h]),
    Finpartition.mem_part_kreweras_iff.2 ⟨mem_univ x, mem_univ y, fun a b hb ha => ?_⟩, ?_⟩
  · rw [hI] at ha ⊢
    split_ifs at ha ⊢ with h0
    · exact le_of_not_gt fun hbt =>
        ha.not_gt (hint b a (Finpartition.mem_part_comm.1 hb) (Fin.le_def.2 (by omega)) hbt).2
    · exact hint a b hb ha.1 ha.2
  · rwa [mem_part_rotate_symm, hxm, hyt]

/-- If `π < ρ` in `NC(n)`, then two distinct positions lie in a common part both of `K(π)` and of
the inverse rotation of `ρ`. Let `B` be a part of `π` inside a part `C` of `ρ` that misses the
last position of `C`, let `m` and `M` be the first and the last position of `B`, and let `t` be
the first position of `C` after `M`. Then `[m, t)` is a union of parts of `π`, and `m`, `t` lie in
`C`. -/
private theorem exists_ne_mem_part_kreweras_mem_part_rotate_symm
    {π ρ : NoncrossingPartition (univ : Finset (Fin n))} (hπρ : π ≤ ρ) (hne : π ≠ ρ) :
    ∃ x y, x ≠ y ∧ y ∈ π.1.kreweras.part x ∧ y ∈ ((rotate n).symm ρ).1.part x := by
  have hπ (a b : Fin n) : b ∈ π.1.part a ↔ π.1.part b = π.1.part a :=
    π.1.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)
  have hρ (a b : Fin n) : b ∈ ρ.1.part a ↔ ρ.1.part b = ρ.1.part a :=
    ρ.1.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)
  -- The part `C` of `ρ` through `c` contains a part of `π` missing the last position of `C`.
  obtain ⟨c, d, hdc, hdπ⟩ : ∃ c d, d ∈ ρ.1.part c ∧ d ∉ π.1.part c := by
    by_contra! h
    exact hne (le_antisymm hπρ (Subtype.coe_le_coe.1
      (Finpartition.le_iff_forall_part_subset.2 fun c d hd => h c d hd)))
  have hCne : (ρ.1.part c).Nonempty := ⟨c, ρ.1.mem_part_self.2 (mem_univ c)⟩
  obtain ⟨e, heC, heM⟩ : ∃ e ∈ ρ.1.part c, (ρ.1.part c).max' hCne ∉ π.1.part e := by
    by_cases hcM : (ρ.1.part c).max' hCne ∈ π.1.part c
    · refine ⟨d, hdc, fun hdM => hdπ ?_⟩
      rw [hπ] at hcM hdM ⊢
      exact hdM.symm.trans hcM
    · exact ⟨c, ρ.1.mem_part_self.2 (mem_univ c), hcM⟩
  -- `m` and `M` are the first and the last position of the part of `π` through `e`.
  have hBne : (π.1.part e).Nonempty := ⟨e, π.1.mem_part_self.2 (mem_univ e)⟩
  set m := (π.1.part e).min' hBne
  set M := (π.1.part e).max' hBne
  have hme : π.1.part m = π.1.part e := (hπ e m).1 (min'_mem _ _)
  have hmc : ρ.1.part m = ρ.1.part c :=
    ((hρ e m).1 (Finpartition.part_mono hπρ e (min'_mem _ _))).trans ((hρ c e).1 heC)
  have hMC : M ∈ ρ.1.part c := by
    rw [← (hρ c e).1 heC]
    exact Finpartition.part_mono hπρ e (max'_mem _ _)
  have hMlt : M < (ρ.1.part c).max' hCne :=
    lt_of_le_of_ne (le_max' _ _ hMC) fun h => heM (h ▸ max'_mem _ _)
  -- `t` is the first position of `C` after `M`.
  have htne : ((ρ.1.part c).filter (M < ·)).Nonempty :=
    ⟨_, mem_filter.2 ⟨max'_mem _ _, hMlt⟩⟩
  obtain ⟨htC, hMt⟩ := mem_filter.1 (min'_mem _ htne)
  refine exists_ne_mem_part_kreweras_mem_part_rotate_symm_of_forall
    ((min'_le _ _ (max'_mem _ _)).trans_lt hMt) (by rw [hρ, hmc, (hρ c _).1 htC]) fun a b hb =>
      π.2.le_and_lt_of_mem_part ρ.2 hπρ (mem_univ m) (by rw [hme]; exact max'_mem _ _)
        (fun z hz => min'_le _ _ (hme ▸ hz)) (fun z hz => le_max' _ _ (hme ▸ hz))
        (by rw [hmc]; exact htC) hMt (fun z hz h => min'_le _ _ (mem_filter.2 ⟨hmc ▸ hz, h⟩)) hb

/-- A noncrossing partition `σ` finer than the Kreweras complement `K(π)` joins with `π` to the
partition into one part exactly when it is `K(π)` itself. -/
theorem sup_eq_top_iff_eq_kreweras {π σ : NoncrossingPartition (univ : Finset (Fin n))}
    (hσ : σ ≤ kreweras π) : π ⊔ σ = ⊤ ↔ σ = kreweras π := by
  obtain ⟨ρ, rfl⟩ := kreweras_bijective.2 σ
  rw [kreweras_le_kreweras_iff] at hσ
  rw [kreweras_inj]
  conv_lhs => rw [← kreweras_inj, kreweras_sup, kreweras_kreweras, kreweras_top]
  refine ⟨fun h => by_contra fun hne => ?_, by rintro rfl; exact kreweras_inf_rotate_symm_eq_bot _⟩
  obtain ⟨x, y, hxy, hK, hR⟩ := exists_ne_mem_part_kreweras_mem_part_rotate_symm hσ (Ne.symm hne)
  have hle := le_inf (Finpartition.pairPartition_le (hij := subset_univ _) hK)
    (Finpartition.pairPartition_le (hij := subset_univ _) hR)
  rw [← coe_kreweras, ← coe_inf, h, coe_bot, le_bot_iff] at hle
  exact Finpartition.pairPartition_ne_bot hxy hle

/-- A noncrossing partition joins with its Kreweras complement to the partition into one part. -/
@[simp]
theorem sup_kreweras_eq_top (π : NoncrossingPartition (univ : Finset (Fin n))) :
    π ⊔ kreweras π = ⊤ :=
  (sup_eq_top_iff_eq_kreweras le_rfl).2 rfl

end Fin

end TauCeti.NoncrossingPartition
