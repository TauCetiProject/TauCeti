/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Prod.Lex.Basic
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

end Finpartition
