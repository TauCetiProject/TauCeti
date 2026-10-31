/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max
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
For noncrossing `P` and `Q ≤ K(P)`, the join of `P.interlace Q` with the partition into the pairs
`{(x, false), (x, true)}` in the lattice of noncrossing partitions of the interlaced positions is
the partition into one part exactly when `Q = K(P)`
(`TauCeti.NoncrossingPartition.sup_comap_fst_bot_eq_top_iff`). If `Q = K(P)`, an interval part of a
coarser noncrossing partition other than the one-part partition would give a nonempty interval of
`s` other than `s` itself that is a union of parts of both `P` and `K(P)`, and there is no such
interval. If `Q < K(P)`, a part of
`K(P)` split by `Q` yields an interval `(c, c']` that is a union of parts of both `P` and `Q`, and
splitting off its interlaced positions gives a coarser noncrossing partition with two parts.

## Main definitions

* `Finset.interlace s` — the interlaced positions of `s`, a finite subset of `α ×ₗ Bool`.
* `Finpartition.interlace P Q` — the partition of the interlaced positions of `s` with the parts of
  `P` on the positions and the parts of `Q` on the bars.

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
* `TauCeti.NoncrossingPartition.sup_comap_fst_bot_eq_top_iff` — for noncrossing `P` and `Q ≤ K(P)`,
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

section Cut

variable {α : Type*} [LinearOrder α] {s : Finset α} {P Q : Finpartition s}

/-- Let `T` be a nonempty union of parts of `P` that is an interval of `s` but not all of `s`. Then
`T` is not a union of parts of the Kreweras complement `K(P)`: the bar after the last position `v`
of `T` lies in a common part of `K(P)` with the bar just before `T`, or, if `T` contains the first
position of `s`, with the bar after the last position of `s`. -/
private theorem exists_mem_part_kreweras_notMem {T : Finset α} (hTs : T ⊆ s)
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
private theorem exists_lt_forall_mem_Ioc_of_lt_kreweras (hQ : Q.IsNoncrossing)
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

end Cut

end Finpartition

namespace TauCeti.NoncrossingPartition

variable {α : Type*} [LinearOrder α] {s : Finset α}

open Finpartition

/-- A noncrossing partition of the interlaced positions coarser than the pairs
`{(x, false), (x, true)}` joins each position `(x, false)` with the bar `(x, true)`. -/
private theorem toLex_mem_part_of_comap_fst_bot_le {ρ : NoncrossingPartition s.interlace}
    (hρ : comap (s := s.interlace) (f := fun p => (ofLex p).1)
      (Prod.Lex.monotone_fst_ofLex.monotoneOn _) ⊥ ≤ ρ) {x : α} (hx : x ∈ s) (b c : Bool) :
    toLex (x, c) ∈ ρ.1.part (toLex (x, b)) := by
  refine part_mono (Subtype.coe_le_coe.2 hρ) _ ?_
  rw [coe_comap, coe_bot, part_comap_bot (toLex_mem_interlace.2 hx)]
  exact mem_filter.2 ⟨toLex_mem_interlace.2 hx, rfl⟩

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
private theorem sup_comap_fst_bot_ne_top {P Q : Finpartition s}
    {σ : NoncrossingPartition s.interlace} (hσ : (σ : Finpartition s.interlace) = P.interlace Q)
    {c c' : α} (hc : c ∈ s) (hc' : c' ∈ s) (hcc' : c < c')
    (hPc : ∀ a, ∀ b ∈ P.part a, c < a → a ≤ c' → c < b ∧ b ≤ c')
    (hQc : ∀ a, ∀ b ∈ Q.part a, c < a → a ≤ c' → c < b ∧ b ≤ c') :
    σ ⊔ comap (s := s.interlace) (f := fun p => (ofLex p).1)
      (Prod.Lex.monotone_fst_ofLex.monotoneOn _) ⊥ ≠ ⊤ := by
  obtain ⟨ρ, hρ⟩ := exists_forall_toLex_mem_part_iff hc' hcc'
  have hle : σ ⊔ comap (s := s.interlace) (f := fun p => (ofLex p).1)
      (Prod.Lex.monotone_fst_ofLex.monotoneOn _) ⊥ ≤ ρ := by
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
      rw [coe_comap, coe_bot, part_comap_bot hp, mem_filter] at hq
      obtain ⟨⟨x, b⟩, rfl⟩ := toLex.surjective p
      obtain ⟨⟨y, b'⟩, rfl⟩ := toLex.surjective q
      obtain ⟨hy, hxy⟩ := hq
      simp only [ofLex_toLex] at hxy
      subst hxy
      exact (hρ _ (toLex_mem_interlace.1 hp) _ (toLex_mem_interlace.1 hy) b b').2 Iff.rfl
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
private theorem exists_interval_of_comap_fst_bot_le {ρ : NoncrossingPartition s.interlace}
    (hρ : comap (s := s.interlace) (f := fun p => (ofLex p).1)
      (Prod.Lex.monotone_fst_ofLex.monotoneOn _) ⊥ ≤ ρ) (hne : ρ ≠ ⊤) :
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
    exact ⟨fun h => hBρ h ▸ toLex_mem_part_of_comap_fst_bot_le hρ hx false b,
      fun h => hBρ h ▸ toLex_mem_part_of_comap_fst_bot_le hρ hx b false⟩
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
theorem sup_comap_fst_bot_eq_top_iff {P Q : NoncrossingPartition s}
    {σ : NoncrossingPartition s.interlace} (hσ : (σ : Finpartition s.interlace) = P.1.interlace Q.1)
    (hQ : Q ≤ kreweras P) :
    σ ⊔ comap (s := s.interlace) (f := fun p => (ofLex p).1)
      (Prod.Lex.monotone_fst_ofLex.monotoneOn _) ⊥ = ⊤ ↔ Q = kreweras P := by
  refine ⟨fun htop => by_contra fun hne => ?_, fun hQK => by_contra fun hne => ?_⟩
  · -- If `Q < K(P)`, an interval `(c, c']` that is a union of parts of `P` and of `Q` separates.
    obtain ⟨c, hc, c', hc', hcc', hPc, hQc⟩ := exists_lt_forall_mem_Ioc_of_lt_kreweras (P := P.1)
      Q.2 (coe_kreweras P ▸ Subtype.coe_le_coe.2 hQ)
      fun h => hne (Subtype.ext (h.trans (coe_kreweras P).symm))
    exact sup_comap_fst_bot_ne_top hσ hc hc' hcc' hPc hQc htop
  · -- If `Q = K(P)`, an interval part of the join other than everything would give an interval of
    -- `s` that is a union of parts of both `P` and `K(P)`, which does not exist.
    obtain ⟨T, hTs, hconv, hTne, hsT, hρT⟩ := exists_interval_of_comap_fst_bot_le le_sup_right hne
    have hσT {x y : α} (hx : x ∈ T) (b : Bool) (hy : y ∈ (bif b then Q.1 else P.1).part x) :
        y ∈ T :=
      hρT x hx y ((bif b then Q.1 else P.1).part_subset x hy) b b <|
        part_mono (Subtype.coe_le_coe.2 (le_sup_left (b := comap (s := s.interlace)
          (f := fun p => (ofLex p).1) (Prod.Lex.monotone_fst_ofLex.monotoneOn _) ⊥))) _
          (hσ ▸ (mem_part_interlace_iff (hTs hx)).2 ⟨rfl, hy⟩)
    obtain ⟨x, hxT, y, hy, hyT⟩ := exists_mem_part_kreweras_notMem hTs hconv hTne hsT
      fun x hx y hy => hσT hx false hy
    exact hyT (hσT hxT true (by rw [Bool.cond_true, hQK, coe_kreweras]; exact hy))

end TauCeti.NoncrossingPartition
