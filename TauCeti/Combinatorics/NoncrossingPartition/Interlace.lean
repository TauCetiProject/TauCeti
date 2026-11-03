/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Prod.Lex.Basic
public import TauCeti.Combinatorics.NoncrossingPartition.Comap
public import TauCeti.Combinatorics.NoncrossingPartition.Kreweras

/-!
# Noncrossing partitions of interlaced positions

Let `s = {a₁ < ⋯ < aₙ}` be a finite set of positions in a linear order. The Kreweras complement
lives on the *interlaced positions* `a₁ < ā₁ < a₂ < ā₂ < ⋯ < aₙ < āₙ`, where the bar `āᵢ` sits
just after `aᵢ`. We realise them as the pairs `(x, false)` and `(x, true)` for `x ∈ s`, ordered
lexicographically in `α ×ₗ Bool`, so that the bar after `x` is labelled by `x` as in
`Finpartition.kreweras`.

A partition `P` of the positions and a partition `Q` of the bars together give a partition
`P.interlace Q` of the interlaced positions, with the parts of `P` on the positions and the parts of
`Q` on the bars. It is noncrossing exactly when `P` and `Q` are noncrossing and `Q` refines the
Kreweras complement of `P` (`Finpartition.isNoncrossing_interlace_iff`). Every partition of the
interlaced positions none of whose parts meets both positions and bars is of this form
(`Finpartition.exists_eq_interlace`), and `P`, `Q` are determined by it
(`Finpartition.interlace_inj`).

These partitions index the moment–cumulant expansion of the alternating products
`a₁b₁a₂b₂⋯aₙbₙ` of two free families: the noncrossing partitions of the interlaced word that do not
mix the two families are exactly the pairs of a noncrossing partition `π` of the `a`-letters and a
noncrossing partition of the `b`-letters below the Kreweras complement of `π`.

For the free cumulants of these products, one also groups each position with the bar after it.
For noncrossing `P` and `Q ≤ K(P)`, the join of `P.interlace Q` with the partition
`interlacePairs s` into the pairs `{(x, false), (x, true)}` in the lattice of noncrossing partitions
of the interlaced positions is the partition into one part exactly when `Q = K(P)`
(`TauCeti.NoncrossingPartition.sup_interlacePairs_eq_top_iff`). If `Q = K(P)`, an interval part of
a coarser noncrossing partition other than the one-part partition would give a nonempty interval of
`s` other than `s` itself that is a union of parts of both `P` and `K(P)`, and there is no such
interval (`Finpartition.exists_mem_part_kreweras_notMem`). If `Q < K(P)`, a part of `K(P)` split by
`Q` yields an interval `(c, c']` that is a union of parts of both `P` and `Q`
(`Finpartition.exists_lt_forall_mem_Ioc_of_lt_kreweras`), and splitting off its interlaced
positions gives a coarser noncrossing partition with two parts.

## Main definitions

* `Finset.interlace s` — the interlaced positions of `s`, a finite subset of `α ×ₗ Bool`.
* `Finpartition.interlace P Q` — the partition of the interlaced positions of `s` with the parts of
  `P` on the positions and the parts of `Q` on the bars.
* `TauCeti.NoncrossingPartition.interlacePairs s` — the partition of the interlaced positions of `s`
  into the pairs `{(x, false), (x, true)}`.

## Main results

* `Finpartition.part_interlace_false`, `Finpartition.part_interlace_true` — the parts of
  `P.interlace Q` are the parts of `P` placed on the positions and the parts of `Q` placed on the
  bars.
* `Finpartition.prod_parts_interlace` — a product over the parts of `P.interlace Q` splits as a
  product over the parts of `P` and a product over the parts of `Q`.
* `Finpartition.interlace_inj` and `Finpartition.exists_eq_interlace` — interlacing is injective,
  and its image consists of the partitions none of whose parts meets both positions and bars.
* `Finpartition.isNoncrossing_interlace_iff` — `P.interlace Q` is noncrossing exactly when `P` and
  `Q` are noncrossing and `Q ≤ P.kreweras`.
* `TauCeti.NoncrossingPartition.sup_interlacePairs_eq_top_iff` — for noncrossing `P` and `Q ≤ K(P)`,
  the join of `P.interlace Q` with the pairs `{(x, false), (x, true)}` is the partition into one
  part exactly when `Q = K(P)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 9 (the
  complementation map) and Lecture 14.
-/

public section

open Finset

namespace Finset

variable {α : Type*}

/-- The *interlaced positions* of a finite set `s`: the pairs `(x, b)` with `x ∈ s` and `b : Bool`,
ordered lexicographically. The pair `(x, false)` stands for the position `x` and `(x, true)` for the
bar just after it, so that for `s = {a₁ < ⋯ < aₙ}` the interlaced positions are
`a₁ < ā₁ < a₂ < ā₂ < ⋯ < aₙ < āₙ`. -/
def interlace (s : Finset α) : Finset (α ×ₗ Bool) :=
  (s ×ˢ univ).map toLex.toEmbedding

/-- A pair lies in the interlaced positions of `s` exactly when its first coordinate lies in `s`. -/
@[simp]
theorem mem_interlace {s : Finset α} {p : α ×ₗ Bool} : p ∈ s.interlace ↔ (ofLex p).1 ∈ s := by
  simp [interlace, mem_map_equiv]

/-- The position `(x, false)` and the bar `(x, true)` are interlaced positions of `s` exactly when
`x ∈ s`. -/
theorem toLex_mem_interlace {s : Finset α} {x : α} {b : Bool} :
    toLex (x, b) ∈ s.interlace ↔ x ∈ s :=
  mem_interlace

/-- The interlaced positions of `s` over a position `x ∈ s` are the position `(x, false)` and the
bar `(x, true)`. -/
theorem filter_interlace_fst_eq [DecidableEq α] {s : Finset α} {x : α} (hx : x ∈ s) :
    {p ∈ s.interlace | (ofLex p).1 = x} = {toLex (x, false), toLex (x, true)} := by
  ext p
  obtain ⟨⟨y, c⟩, rfl⟩ := toLex.surjective p
  simp only [mem_filter, mem_interlace, ofLex_toLex, mem_insert, mem_singleton]
  cases c <;> simp +contextual [hx]

/-- The first coordinates of the interlaced positions of `s` are the positions of `s`. -/
@[simp]
theorem image_interlace_fst [DecidableEq α] {s : Finset α} :
    s.interlace.image (fun p => (ofLex p).1) = s := by
  ext x
  simp only [mem_image, mem_interlace]
  exact ⟨fun ⟨p, hp, hpx⟩ => hpx ▸ hp, fun hx => ⟨toLex (x, false), hx, rfl⟩⟩

end Finset

namespace Finpartition

section Interlace

variable {α : Type*} [DecidableEq α] {s : Finset α} {P Q P' Q' : Finpartition s}

omit [DecidableEq α] in
/-- Placing a position on the positions (`b = false`) or on the bars (`b = true`) is injective. -/
private theorem toLex_mk_injective (b : Bool) : Function.Injective fun x : α => toLex (x, b) :=
  toLex.injective.comp (Prod.mk_left_injective b)

/-- The partition of the positions placed on the sheet `b`: `P` on the positions, `Q` on the bars.
-/
private abbrev sheet (P Q : Finpartition s) (b : Bool) : Finpartition s := bif b then Q else P

/-- The parts of `P` placed on the positions together with the parts of `Q` placed on the bars. -/
private def interlaceParts (P Q : Finpartition s) : Finset (Finset (α ×ₗ Bool)) :=
  P.parts.image (image fun x => toLex (x, false)) ∪ Q.parts.image (image fun x => toLex (x, true))

private theorem mem_interlaceParts {C : Finset (α ×ₗ Bool)} :
    C ∈ interlaceParts P Q ↔
      ∃ b, ∃ B ∈ (sheet P Q b).parts, B.image (fun x => toLex (x, b)) = C := by
  simp only [interlaceParts, mem_union, mem_image]
  constructor
  · rintro (h | h)
    exacts [⟨false, h⟩, ⟨true, h⟩]
  · rintro ⟨_ | _, h⟩
    exacts [Or.inl h, Or.inr h]

/-- The part of the sheet `b` through a position `x` of `s`, placed on that sheet, is the unique
member of `interlaceParts P Q` containing `(x, b)`. -/
private theorem existsUnique_mem_interlaceParts {x : α} (hx : x ∈ s) (b : Bool) :
    ∃! C ∈ interlaceParts P Q, toLex (x, b) ∈ C := by
  refine ⟨((sheet P Q b).part x).image fun y => toLex (y, b),
    ⟨mem_interlaceParts.2 ⟨b, _, (sheet P Q b).part_mem.2 hx, rfl⟩,
      mem_image_of_mem _ ((sheet P Q b).mem_part_self.2 hx)⟩, ?_⟩
  rintro C ⟨hC, hxC⟩
  obtain ⟨c, B, hB, rfl⟩ := mem_interlaceParts.1 hC
  obtain ⟨y, hy, hyx⟩ := mem_image.1 hxC
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (toLex.injective hyx)
  rw [part_eq_of_mem _ hB hy]

/-- The *interlaced partition* of two partitions `P` and `Q` of `s`: the partition of the interlaced
positions of `s` whose parts are the parts of `P` placed on the positions `(x, false)` and the parts
of `Q` placed on the bars `(x, true)`. -/
def interlace (P Q : Finpartition s) : Finpartition s.interlace :=
  ofExistsUnique (interlaceParts P Q)
    (fun C hC => by
      obtain ⟨b, B, hB, rfl⟩ := mem_interlaceParts.1 hC
      intro p hp
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hp
      exact mem_interlace.2 ((sheet P Q b).le hB hx))
    (fun p hp => by
      obtain ⟨⟨x, b⟩, rfl⟩ := toLex.surjective p
      exact existsUnique_mem_interlaceParts (mem_interlace.1 hp) b)
    (fun h => by
      obtain ⟨b, B, hB, hBe⟩ := mem_interlaceParts.1 h
      exact (sheet P Q b).ne_empty hB (image_eq_empty.1 hBe))

/-- The parts of `P.interlace Q` are the parts of `P` placed on the positions and the parts of `Q`
placed on the bars. -/
theorem parts_interlace (P Q : Finpartition s) :
    (P.interlace Q).parts =
      P.parts.image (image fun x => toLex (x, false)) ∪
        Q.parts.image (image fun x => toLex (x, true)) :=
  (rfl)

private theorem part_interlace {x : α} (hx : x ∈ s) (b : Bool) :
    (P.interlace Q).part (toLex (x, b)) = ((sheet P Q b).part x).image fun y => toLex (y, b) :=
  part_eq_of_mem _ (mem_interlaceParts.2 ⟨b, _, (sheet P Q b).part_mem.2 hx, rfl⟩)
    (mem_image_of_mem _ ((sheet P Q b).mem_part_self.2 hx))

/-- The part of `P.interlace Q` through the position `x` is the part of `P` through `x`, placed on
the positions. -/
@[simp]
theorem part_interlace_false {x : α} (hx : x ∈ s) :
    (P.interlace Q).part (toLex (x, false)) = (P.part x).image fun y => toLex (y, false) :=
  part_interlace hx false

/-- The part of `P.interlace Q` through the bar after `x` is the part of `Q` through `x`, placed on
the bars. -/
@[simp]
theorem part_interlace_true {x : α} (hx : x ∈ s) :
    (P.interlace Q).part (toLex (x, true)) = (Q.part x).image fun y => toLex (y, true) :=
  part_interlace hx true

/-- Two interlaced positions lie in a common part of `P.interlace Q` exactly when they lie on the
same sheet and their labels lie in a common part of the partition of that sheet. -/
private theorem mem_part_interlace_iff {x y : α} (hx : x ∈ s) {b c : Bool} :
    toLex (y, c) ∈ (P.interlace Q).part (toLex (x, b)) ↔ c = b ∧ y ∈ (sheet P Q b).part x := by
  rw [part_interlace hx, mem_image]
  constructor
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (toLex.injective hzy)
    exact ⟨rfl, hz⟩
  · rintro ⟨rfl, hy⟩
    exact ⟨y, hy, rfl⟩

/-- A product over the parts of `P.interlace Q` is the product over the parts of `P`, placed on the
positions, times the product over the parts of `Q`, placed on the bars. -/
theorem prod_parts_interlace {M : Type*} [CommMonoid M] (P Q : Finpartition s)
    (g : Finset (α ×ₗ Bool) → M) :
    ∏ C ∈ (P.interlace Q).parts, g C =
      (∏ B ∈ P.parts, g (B.image fun x => toLex (x, false))) *
        ∏ B ∈ Q.parts, g (B.image fun x => toLex (x, true)) := by
  rw [parts_interlace, prod_union, prod_image fun _ _ _ _ h => image_injective
    (toLex_mk_injective false) h, prod_image fun _ _ _ _ h => image_injective
    (toLex_mk_injective true) h]
  refine disjoint_left.2 fun C hP hQ => ?_
  obtain ⟨B, hB, rfl⟩ := mem_image.1 hP
  obtain ⟨B', hB', hBB'⟩ := mem_image.1 hQ
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
  obtain ⟨y, -, hyx⟩ := mem_image.1 (hBB' ▸ mem_image_of_mem (fun x => toLex (x, false)) hx)
  exact Bool.noConfusion (Prod.mk.inj (toLex.injective hyx)).2

/-- Interlacing is injective: `P.interlace Q` determines `P` and `Q`. -/
@[simp]
theorem interlace_inj : P.interlace Q = P'.interlace Q' ↔ P = P' ∧ Q = Q' := by
  refine ⟨fun h => ?_, fun ⟨hP, hQ⟩ => hP ▸ hQ ▸ rfl⟩
  have key (b : Bool) : sheet P Q b = sheet P' Q' b := ext_of_part fun x hx => by
    have := part_interlace (P := P) (Q := Q) hx b
    rw [h, part_interlace hx b] at this
    exact (image_injective (toLex_mk_injective b) this).symm
  exact ⟨key false, key true⟩

/-- A partition of the interlaced positions of `s` none of whose parts meets both the positions and
the bars is the interlaced partition of two partitions of `s`. -/
theorem exists_eq_interlace {σ : Finpartition s.interlace}
    (h : ∀ p ∈ s.interlace, ∀ q ∈ σ.part p, (ofLex q).2 = (ofLex p).2) :
    ∃ P Q : Finpartition s, σ = P.interlace Q := by
  -- The partition of the sheet `b` is the restriction of `σ` to that sheet, pulled back to `s`.
  have hsub (b : Bool) : s.image (fun x => toLex (x, b)) ≤ s.interlace := fun p hp => by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hp
    exact mem_interlace.2 hx
  set R : Bool → Finpartition s := fun b => (σ.restrict (hsub b)).comap fun x => toLex (x, b)
  have hR {b : Bool} {x y : α} (hx : x ∈ s) :
      y ∈ (R b).part x ↔ y ∈ s ∧ toLex (y, b) ∈ σ.part (toLex (x, b)) := by
    rw [mem_part_comap hx, part_restrict _ _ (mem_image_of_mem _ hx), mem_inter,
      and_congr_right fun hy => and_iff_left (mem_image_of_mem _ hy)]
  refine ⟨R false, R true, ext_of_part fun p hp => ?_⟩
  obtain ⟨⟨x, b⟩, rfl⟩ := toLex.surjective p
  have hx : x ∈ s := mem_interlace.1 hp
  ext q
  obtain ⟨⟨y, c⟩, rfl⟩ := toLex.surjective q
  rw [mem_part_interlace_iff hx]
  have hRb : sheet (R false) (R true) b = R b := by cases b <;> rfl
  rw [hRb, hR hx]
  constructor
  · intro hq
    obtain rfl : c = b := h _ hp _ hq
    exact ⟨rfl, mem_interlace.1 (σ.part_subset _ hq), hq⟩
  · rintro ⟨rfl, -, hq⟩
    exact hq

end Interlace

section Noncrossing

variable {α : Type*} [LinearOrder α] {s : Finset α} {P Q : Finpartition s}

/-- Placing positions on the positions or on the bars is strictly monotone. -/
private theorem toLex_mk_strictMono (b : Bool) : StrictMono fun x : α => toLex (x, b) :=
  fun _ _ h => Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

/-- Two positions in a common part of the partition of a sheet give the same part of
`P.interlace Q` when placed on that sheet. -/
private theorem part_interlace_eq_part_interlace {x y : α} (hx : x ∈ s) {b : Bool}
    (hy : y ∈ (sheet P Q b).part x) :
    (P.interlace Q).part (toLex (x, b)) = (P.interlace Q).part (toLex (y, b)) := by
  have hys := (sheet P Q b).part_subset x hy
  rw [part_interlace hx, part_interlace hys,
    ((sheet P Q b).mem_part_iff_part_eq_part hys hx).1 hy]

/-- A position and a bar never lie in a common part of `P.interlace Q`. -/
private theorem part_interlace_false_ne_true {a x : α} (ha : a ∈ s) (hx : x ∈ s) :
    (P.interlace Q).part (toLex (a, false)) ≠ (P.interlace Q).part (toLex (x, true)) := by
  intro he
  have hxx : toLex (x, true) ∈ (P.interlace Q).part (toLex (x, true)) :=
    (P.interlace Q).mem_part_self.2 (toLex_mem_interlace.2 hx)
  rw [← he, mem_part_interlace_iff ha] at hxx
  exact Bool.noConfusion hxx.1

/-- If `P.interlace Q` is noncrossing, then so is the partition of each sheet. -/
private theorem isNoncrossing_sheet_of_isNoncrossing_interlace
    (h : (P.interlace Q).IsNoncrossing) (b : Bool) : (sheet P Q b).IsNoncrossing := by
  refine isNoncrossing_iff_part.2 fun x hx y hy z hz w hw hxy hyz hzw => ?_
  have hlt := toLex_mk_strictMono (α := α) b
  have := h.part_eq_part (toLex_mem_interlace.2 hx) (toLex_mem_interlace.2 hy)
    (part_interlace_eq_part_interlace hx hz) (part_interlace_eq_part_interlace hy hw)
    (hlt hxy) (hlt hyz) (hlt hzw)
  rw [part_interlace hx, part_interlace hy] at this
  exact image_injective (toLex_mk_injective b) this

/-- If `P.interlace Q` is noncrossing, then `Q` refines the Kreweras complement of `P`: a part of
`Q` crossing a part of `P` would make `P.interlace Q` cross. -/
private theorem le_kreweras_of_isNoncrossing_interlace (h : (P.interlace Q).IsNoncrossing) :
    Q ≤ P.kreweras := by
  refine le_kreweras_iff.2 fun x y hy a b hb => ?_
  have hx : x ∈ s := Q.part_nonempty.1 ⟨y, hy⟩
  have ha : a ∈ s := P.part_nonempty.1 ⟨b, hb⟩
  have hP := part_interlace_eq_part_interlace (P := P) (Q := Q) ha (b := false) hb
  have hQ := part_interlace_eq_part_interlace (P := P) (Q := Q) hx (b := true) hy
  have hne := part_interlace_false_ne_true (P := P) (Q := Q) ha hx
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact hne (h.part_eq_part (toLex_mem_interlace.2 ha) (toLex_mem_interlace.2 hx) hP hQ
      (Prod.Lex.toLex_lt_toLex.2 (by simp [lt_or_eq_of_le h₁]))
      (Prod.Lex.toLex_lt_toLex.2 (Or.inl h₂))
      (Prod.Lex.toLex_lt_toLex.2 (by simp [lt_or_eq_of_le h₃])))
  · rintro ⟨h₁, h₂, h₃⟩
    exact hne (h.part_eq_part (toLex_mem_interlace.2 hx) (toLex_mem_interlace.2 ha) hQ hP
      (Prod.Lex.toLex_lt_toLex.2 (Or.inl h₁))
      (Prod.Lex.toLex_lt_toLex.2 (by simp [lt_or_eq_of_le h₂]))
      (Prod.Lex.toLex_lt_toLex.2 (Or.inl h₃))).symm

/-- If `P` and `Q` are noncrossing and `Q ≤ P.kreweras`, then `P.interlace Q` is noncrossing: two
crossing parts would lie on the same sheet, where `P` and `Q` are noncrossing, or on different
sheets, where `Q ≤ P.kreweras` rules the crossing out. -/
private theorem isNoncrossing_interlace_of_le_kreweras (hP : P.IsNoncrossing)
    (hQ : Q.IsNoncrossing) (hK : Q ≤ P.kreweras) : (P.interlace Q).IsNoncrossing := by
  have hsheet (b : Bool) : (sheet P Q b).IsNoncrossing := by cases b <;> assumption
  have hK' := le_kreweras_iff.1 hK
  refine isNoncrossing_iff_part.2 fun p hp q hq r hr w hw hpq hqr hrw => ?_
  obtain ⟨⟨x, b⟩, rfl⟩ := toLex.surjective p
  obtain ⟨⟨y, c⟩, rfl⟩ := toLex.surjective q
  obtain ⟨⟨z, b'⟩, rfl⟩ := toLex.surjective r
  obtain ⟨⟨u, c'⟩, rfl⟩ := toLex.surjective w
  have hx : x ∈ s := mem_interlace.1 hp
  have hy : y ∈ s := mem_interlace.1 hq
  obtain ⟨hb, hz⟩ := (mem_part_interlace_iff hx).1 hr
  obtain ⟨hc, hu⟩ := (mem_part_interlace_iff hy).1 hw
  subst b' c'
  rw [Prod.Lex.toLex_lt_toLex] at hpq hqr hrw
  rw [part_interlace hx, part_interlace hy]
  have hxz := (part_eq_of_mem _ ((sheet P Q b).part_mem.2 hx) hz).symm
  have hyu := (part_eq_of_mem _ ((sheet P Q c).part_mem.2 hy) hu).symm
  rcases Bool.eq_false_or_eq_true b with rfl | rfl <;>
    rcases Bool.eq_false_or_eq_true c with rfl | rfl <;>
    simp only [lt_self_iff_false, Bool.false_lt_true, (by decide : ¬true < false), and_false,
      and_true, or_false, ← le_iff_lt_or_eq] at hpq hqr hrw
  · rw [(hsheet true).part_eq_part hx hy hxz hyu hpq hqr hrw]
  · exact absurd ⟨hpq, hqr, hrw⟩ (hK' x z hz y u hu).2
  · exact absurd ⟨hpq, hqr, hrw⟩ (hK' y u hu x z hz).1
  · rw [(hsheet false).part_eq_part hx hy hxz hyu hpq hqr hrw]

/-- The interlaced partition `P.interlace Q` is noncrossing exactly when `P` and `Q` are
noncrossing and no part of `Q` crosses a part of `P` in the interlaced order, that is, when `Q`
refines the Kreweras complement of `P`. -/
theorem isNoncrossing_interlace_iff :
    (P.interlace Q).IsNoncrossing ↔ P.IsNoncrossing ∧ Q.IsNoncrossing ∧ Q ≤ P.kreweras :=
  ⟨fun h => ⟨isNoncrossing_sheet_of_isNoncrossing_interlace h false,
    isNoncrossing_sheet_of_isNoncrossing_interlace h true,
    le_kreweras_of_isNoncrossing_interlace h⟩,
    fun ⟨hP, hQ, hK⟩ => isNoncrossing_interlace_of_le_kreweras hP hQ hK⟩

end Noncrossing

end Finpartition

namespace TauCeti.NoncrossingPartition

variable {α : Type*} [LinearOrder α] {s : Finset α}

open Finpartition

/-- The partition of the interlaced positions of `s` into the pairs `{(x, false), (x, true)}` of a
position and the bar after it: the fibres of the first coordinate. -/
def interlacePairs (s : Finset α) : NoncrossingPartition s.interlace :=
  comap (s := s.interlace) (f := fun p => (ofLex p).1) (Prod.Lex.monotone_fst_ofLex.monotoneOn _) ⊥

/-- `interlacePairs s` is the pullback of the finest partition of `s` along the first coordinate,
whichever proof of monotonicity is used. -/
theorem comap_fst_bot_eq_interlacePairs
    (hf : MonotoneOn (fun p : α ×ₗ Bool => (ofLex p).1) s.interlace) :
    comap hf ⊥ = interlacePairs s := by
  rw [interlacePairs]

/-- The part of `interlacePairs s` through `(x, b)` is the pair `{(x, false), (x, true)}`. -/
@[simp]
theorem part_interlacePairs {x : α} (hx : x ∈ s) (b : Bool) :
    (interlacePairs s : Finpartition s.interlace).part (toLex (x, b)) =
      {toLex (x, false), toLex (x, true)} := by
  rw [interlacePairs, coe_comap, coe_bot, part_comap_bot (toLex_mem_interlace.2 hx), ofLex_toLex,
    filter_interlace_fst_eq hx]

/-- A noncrossing partition of the interlaced positions coarser than the pairs
`{(x, false), (x, true)}` joins each position `(x, false)` with the bar `(x, true)`. -/
private theorem toLex_mem_part_of_interlacePairs_le {ρ : NoncrossingPartition s.interlace}
    (hρ : interlacePairs s ≤ ρ) {x : α} (hx : x ∈ s) (b c : Bool) :
    toLex (x, c) ∈ ρ.1.part (toLex (x, b)) := by
  refine part_mono (Subtype.coe_le_coe.2 hρ) _ ?_
  rw [part_interlacePairs hx]
  cases c <;> simp

/-- For positions `c < c'` of `s`, splitting the interlaced positions over `(c, c']` off the others
is a noncrossing partition: two interlaced positions lie in a common part exactly when their first
coordinates both lie in `(c, c']` or both lie outside it. -/
private theorem exists_forall_toLex_mem_part_iff {c c' : α} (hc' : c' ∈ s) (hcc' : c < c') :
    ∃ ρ : NoncrossingPartition s.interlace, ∀ x ∈ s, ∀ y ∈ s, ∀ b b' : Bool,
      toLex (y, b') ∈ ρ.1.part (toLex (x, b)) ↔ (c < y ∧ y ≤ c' ↔ c < x ∧ x ≤ c') := by
  set T : Finset (α ×ₗ Bool) := {p ∈ s.interlace | c < (ofLex p).1 ∧ (ofLex p).1 ≤ c'}
  have hT {x : α} (hx : x ∈ s) (b : Bool) : toLex (x, b) ∈ T ↔ c < x ∧ x ≤ c' := by
    simp [T, hx]
  have hTconv : ∀ p ∈ T, ∀ r ∈ T, ∀ q ∈ s.interlace, p < q → q < r → q ∈ T :=
    fun p hp r hr q hq hpq hqr => by
      simp only [T, mem_filter] at hp hr ⊢
      exact ⟨hq, hp.2.1.trans_le (Prod.Lex.monotone_fst_ofLex hpq.le),
        (Prod.Lex.monotone_fst_ofLex hqr.le).trans hr.2.2⟩
  have hTne : T.Nonempty := ⟨_, (hT hc' false).2 ⟨hcc', le_rfl⟩⟩
  refine ⟨⟨splitPartition _ T hTne (filter_subset _ _), isNoncrossing_splitPartition hTconv⟩,
    fun x hx y hy b b' => ?_⟩
  by_cases hxT : c < x ∧ x ≤ c'
  · rw [part_splitPartition_of_mem ((hT hx b).2 hxT), hT hy]
    exact ⟨fun h => iff_of_true h hxT, fun h => h.2 hxT⟩
  · rw [part_splitPartition_of_notMem (toLex_mem_interlace.2 hx) (mt (hT hx b).1 hxT),
      mem_sdiff, hT hy]
    exact ⟨fun h => iff_of_false h.2 hxT, fun h => ⟨toLex_mem_interlace.2 hy, mt h.1 hxT⟩⟩

/-- If `(c, c']` is a union of parts of `P` and of `Q` for positions `c < c'` of `s`, then the join
of `P.interlace Q` with the pairs `{(x, false), (x, true)}` is not the partition into one part: it
is finer than the partition splitting off the interlaced positions over `(c, c']`. -/
private theorem sup_interlacePairs_ne_top {P Q : Finpartition s}
    {σ : NoncrossingPartition s.interlace} (hσ : (σ : Finpartition s.interlace) = P.interlace Q)
    {c c' : α} (hc : c ∈ s) (hc' : c' ∈ s) (hcc' : c < c')
    (hPc : ∀ a, ∀ b ∈ P.part a, c < a → a ≤ c' → c < b ∧ b ≤ c')
    (hQc : ∀ a, ∀ b ∈ Q.part a, c < a → a ≤ c' → c < b ∧ b ≤ c') :
    σ ⊔ interlacePairs s ≠ ⊤ := by
  obtain ⟨ρ, hρ⟩ := exists_forall_toLex_mem_part_iff hc' hcc'
  have hle : σ ⊔ interlacePairs s ≤ ρ := by
    refine sup_le (le_iff_forall_part_subset.2 fun p q hq => ?_)
      (le_iff_forall_part_subset.2 fun p q hq => ?_)
    · have hp : p ∈ s.interlace := σ.1.part_nonempty.1 ⟨q, hq⟩
      obtain ⟨⟨x, b⟩, rfl⟩ := toLex.surjective p
      obtain ⟨⟨y, b'⟩, rfl⟩ := toLex.surjective q
      have hx := toLex_mem_interlace.1 hp
      obtain ⟨rfl, hy⟩ := (mem_part_interlace_iff hx).1 (hσ ▸ hq)
      have hc (R : Finpartition s)
          (hR : ∀ a, ∀ b ∈ R.part a, c < a → a ≤ c' → c < b ∧ b ≤ c') (hy : y ∈ R.part x) :
          toLex (y, b') ∈ ρ.1.part (toLex (x, b')) :=
        (hρ x hx y (R.part_subset x hy) _ _).2
          ⟨fun h => hR y x (mem_part_comm.1 hy) h.1 h.2, fun h => hR x y hy h.1 h.2⟩
      cases b'
      exacts [hc P hPc hy, hc Q hQc hy]
    · have hp : p ∈ s.interlace := (Finpartition.part_nonempty _).1 ⟨q, hq⟩
      obtain ⟨⟨x, b⟩, rfl⟩ := toLex.surjective p
      have hx := toLex_mem_interlace.1 hp
      rw [part_interlacePairs hx, mem_insert, mem_singleton] at hq
      rcases hq with rfl | rfl <;> exact (hρ x hx x hx b _).2 Iff.rfl
  -- But `ρ` is not the partition into one part: it separates `c` from `c'`.
  intro htop
  have hρtop : ρ = ⊤ := top_le_iff.1 (htop ▸ hle)
  have hmem := (hρ c hc c' hc' false false).1 <| by
    rw [hρtop, coe_top, part_top (toLex_mem_interlace.2 hc)]
    exact toLex_mem_interlace.2 hc'
  exact lt_irrefl c (hmem.1 ⟨hcc', le_rfl⟩).1

/-- A noncrossing partition `ρ` of the interlaced positions, coarser than the pairs
`{(x, false), (x, true)}` and other than the partition into one part, has an interval part that
yields a nonempty interval `T` of `s` other than `s` itself: the positions `x` with `(x, false)`,
equivalently `(x, true)`, in that part. -/
private theorem exists_interval_of_interlacePairs_le {ρ : NoncrossingPartition s.interlace}
    (hρ : interlacePairs s ≤ ρ) (hne : ρ ≠ ⊤) :
    ∃ T ⊆ s, (∀ x ∈ T, ∀ z ∈ T, ∀ y ∈ s, x ≤ y → y ≤ z → y ∈ T) ∧ T.Nonempty ∧
      (∃ x ∈ s, x ∉ T) ∧ ∀ x ∈ T, ∀ y ∈ s, ∀ b b' : Bool,
        toLex (y, b') ∈ ρ.1.part (toLex (x, b)) → y ∈ T := by
  rcases s.interlace.eq_empty_or_nonempty with hI | hI
  · exact absurd ((eq_bot_of_eq_empty hI _).trans (eq_bot_of_eq_empty hI _).symm) hne
  obtain ⟨B, hB, hBint⟩ := ρ.2.exists_interval_mem_parts hI
  have hBρ {p : α ×ₗ Bool} (hp : p ∈ B) : ρ.1.part p = B := ρ.1.part_eq_of_mem hB hp
  set T := {x ∈ s | toLex (x, false) ∈ B}
  have hTB {x : α} (hx : x ∈ s) (b : Bool) : x ∈ T ↔ toLex (x, b) ∈ B := by
    simp only [T, mem_filter, hx, true_and]
    exact ⟨fun h => hBρ h ▸ toLex_mem_part_of_interlacePairs_le hρ hx false b,
      fun h => hBρ h ▸ toLex_mem_part_of_interlacePairs_le hρ hx b false⟩
  refine ⟨T, filter_subset _ s, fun x hx z hz y hy hxy hyz => ?_, ?_, ?_,
    fun x hx y hy b b' h => ?_⟩
  · obtain ⟨hxs, hxB⟩ := mem_filter.1 hx
    obtain ⟨hzs, hzB⟩ := mem_filter.1 hz
    refine mem_filter.2 ⟨hy, ?_⟩
    rcases hxy.lt_or_eq with hxy | rfl
    · rcases hyz.lt_or_eq with hyz | rfl
      · exact hBint _ hxB _ hzB _ (toLex_mem_interlace.2 hy)
          (Prod.Lex.toLex_lt_toLex.2 (Or.inl hxy)) (Prod.Lex.toLex_lt_toLex.2 (Or.inl hyz))
      · exact hzB
    · exact hxB
  · obtain ⟨p, hp⟩ := ρ.1.nonempty_of_mem_parts hB
    obtain ⟨⟨x, b⟩, rfl⟩ := toLex.surjective p
    exact ⟨x, (hTB (toLex_mem_interlace.1 (ρ.1.le hB hp)) b).2 hp⟩
  · -- `B` is not everything, as `ρ` is not the partition into one part.
    obtain ⟨p, hpI, hpB⟩ : ∃ p ∈ s.interlace, p ∉ B := by
      by_contra! h
      exact hne (Subtype.ext ((eq_top_of_mem_parts
        (Subset.antisymm (ρ.1.le hB) h ▸ hB : s.interlace ∈ ρ.1.parts)).trans coe_top.symm))
    obtain ⟨⟨x, b⟩, rfl⟩ := toLex.surjective p
    have hx := toLex_mem_interlace.1 hpI
    exact ⟨x, hx, fun hxT => hpB ((hTB hx b).1 hxT)⟩
  · have hxs := (mem_filter.1 hx).1
    exact (hTB hy b').2 (hBρ ((hTB hxs b).1 hx) ▸ h)

/-- Let `P` and `Q` be noncrossing partitions of `s` with `Q ≤ K(P)`, so that their interlaced
partition `σ = P.interlace Q` is a noncrossing partition of the interlaced positions. The join of
`σ` in `NC(s.interlace)` with the partition into the pairs `{(x, false), (x, true)}`, the fibres of
the first coordinate, is the partition into one part exactly when `Q = K(P)`. This is the
combinatorial input of the formula for the free cumulants of products of two free families. -/
theorem sup_interlacePairs_eq_top_iff {P Q : NoncrossingPartition s}
    {σ : NoncrossingPartition s.interlace} (hσ : (σ : Finpartition s.interlace) = P.1.interlace Q.1)
    (hQ : Q ≤ kreweras P) :
    σ ⊔ interlacePairs s = ⊤ ↔ Q = kreweras P := by
  refine ⟨fun htop => by_contra fun hne => ?_, fun hQK => by_contra fun hne => ?_⟩
  · -- If `Q < K(P)`, an interval `(c, c']` that is a union of parts of `P` and of `Q` separates.
    obtain ⟨c, hc, c', hc', hcc', hPc, hQc⟩ := exists_lt_forall_mem_Ioc_of_lt_kreweras (P := P.1)
      Q.2 (coe_kreweras P ▸ Subtype.coe_le_coe.2 hQ)
      fun h => hne (Subtype.ext (h.trans (coe_kreweras P).symm))
    exact sup_interlacePairs_ne_top hσ hc hc' hcc' hPc hQc htop
  · -- If `Q = K(P)`, an interval part of the join other than everything would give an interval of
    -- `s` that is a union of parts of both `P` and `K(P)`, which does not exist.
    obtain ⟨T, hTs, hconv, hTne, hsT, hρT⟩ := exists_interval_of_interlacePairs_le le_sup_right hne
    have hσT {x y : α} (hx : x ∈ T) (b : Bool) (hy : y ∈ (bif b then Q.1 else P.1).part x) :
        y ∈ T :=
      hρT x hx y ((bif b then Q.1 else P.1).part_subset x hy) b b <|
        part_mono (Subtype.coe_le_coe.2 (le_sup_left (b := interlacePairs s))) _
          (hσ ▸ (mem_part_interlace_iff (hTs hx)).2 ⟨rfl, hy⟩)
    obtain ⟨x, hxT, y, hy, hyT⟩ := exists_mem_part_kreweras_notMem hTs hconv hTne hsT
      fun x hx y hy => hσT hx false hy
    exact hyT (hσT hxT true (by rw [Bool.cond_true, hQK, coe_kreweras]; exact hy))

end TauCeti.NoncrossingPartition
