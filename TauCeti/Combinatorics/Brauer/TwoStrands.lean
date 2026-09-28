/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Generator

/-!
# The Brauer diagrams on at most two strands

On few strands the Brauer diagrams can be listed. This file lists them, and reads off the
multiplication table that the loop-weighted stacking of
`TauCeti/Combinatorics/Brauer/Compose.lean` and `TauCeti/Combinatorics/Brauer/LoopCount.lean`
gives them.

What decides the list is the set `TauCeti.BrauerDiagram.bottomCap` of capped bottom points: a
diagram is a permutation diagram exactly when that set is empty
(`TauCeti.BrauerDiagram.exists_eq_permToBrauer_iff_bottomCap_eq_empty`), the caps pair its points
off among themselves so it is even in size, and it is a set of bottom points so it has at most
`k` elements. On `k ≤ 1` strands there is no room for a pair, so the identity is the only diagram
(`TauCeti.BrauerDiagram.eq_permToBrauer_one_of_le_one`). On two strands the set is empty or
everything, which leaves the three diagrams

`1` (two through strands), `s` (the crossing), and `e` (the cap on the bottom together with the
cup on the top),

and no others (`TauCeti.BrauerDiagram.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup`).
That is three diagrams, which is what the general count `(2 * k - 1)‼` of
`TauCeti.card_brauerDiagram` gives at `k = 2`.

Their nine products are then Brauer's relations for `B₂(δ)`: `1` is a two-sided identity,
`s * s = 1`, and `e` absorbs everything from either side, with a loop closing up in the middle for
`e * e` alone. The last two of those are stated for an arbitrary diagram on two strands
(`TauCeti.BrauerDiagram.capCup_composeDiagram_two` and
`TauCeti.BrauerDiagram.middleLoopCount_two`) rather than one case at a time, so the loop-weighted
multiplication `D₁ * D₂ = δ ^ middleLoopCount D₁ D₂ • composeDiagram D₁ D₂` of `B₂(δ)` is pinned
down by them together with the products of permutation diagrams; the relation carrying the loop
value reads `e * e = δ • e`.

## Main results

* `TauCeti.BrauerDiagram.forall_isThrough_iff_bottomCap_eq_empty` and
  `TauCeti.BrauerDiagram.exists_eq_permToBrauer_iff_bottomCap_eq_empty`: a diagram is a
  permutation diagram exactly when it caps no bottom point.
* `TauCeti.BrauerDiagram.eq_permToBrauer_one_of_le_one`: on at most one strand the identity
  diagram is the only diagram.
* `TauCeti.BrauerDiagram.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup` and
  `TauCeti.BrauerDiagram.univ_two`: **the three Brauer diagrams on two strands**, as a case
  distinction and as an enumeration of the whole type.
* `TauCeti.BrauerDiagram.capCup_composeDiagram_two` and
  `TauCeti.BrauerDiagram.composeDiagram_capCup_two`: on two strands the cap-cup diagram absorbs
  every diagram from either side.
* `TauCeti.BrauerDiagram.middleLoopCount_two`: on two strands a loop closes up in the middle only
  for the product of the cap-cup diagram with itself, where exactly one does.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9, and its `B₂(δ)` acceptance criterion.
-/

public section

open scoped Nat

namespace TauCeti

namespace BrauerDiagram

variable {k : ℕ}

/-! ### Permutation diagrams are the diagrams with no cap -/

/-- **A diagram all of whose arcs go through is one that caps no bottom point**, and conversely.
The forward direction is immediate; the converse also has to reach the top boundary, and gets
there by `TauCeti.BrauerDiagram.card_bottomCap_eq_card_topCup`: a diagram with no cap has no cup
either. -/
theorem forall_isThrough_iff_bottomCap_eq_empty (D : BrauerDiagram k) :
    (∀ x, D.IsThrough x) ↔ D.bottomCap = ∅ := by
  refine ⟨fun h => Finset.eq_empty_of_forall_notMem fun i hi => ?_, fun h x => ?_⟩
  · exact (D.isCap_inl_iff i).mp ((mem_bottomCap _).mp hi) (h _)
  · have htop : D.topCup = ∅ := by
      rw [← Finset.card_eq_zero, ← D.card_bottomCap_eq_card_topCup, h, Finset.card_empty]
    rcases x with i | j
    · exact not_not.mp fun hx => (Finset.eq_empty_iff_forall_notMem.mp h i)
        ((mem_bottomCap _).mpr ((D.isCap_inl_iff i).mpr hx))
    · exact not_not.mp fun hx => (Finset.eq_empty_iff_forall_notMem.mp htop j)
        ((mem_topCup _).mpr ((D.isCup_inr_iff j).mpr hx))

/-- **A diagram is a permutation diagram exactly when it caps no bottom point.** The permutation
is then `TauCeti.BrauerDiagram.throughPerm`. -/
theorem exists_eq_permToBrauer_iff_bottomCap_eq_empty (D : BrauerDiagram k) :
    (∃ σ : Equiv.Perm (Fin k), D = permToBrauer σ) ↔ D.bottomCap = ∅ := by
  rw [← forall_isThrough_iff_bottomCap_eq_empty]
  refine ⟨?_, fun h => ⟨throughPerm D h, (permToBrauer_throughPerm h).symm⟩⟩
  rintro ⟨σ, rfl⟩
  exact isThrough_permToBrauer σ

/-! ### At most one strand -/

/-- **A cap joins two distinct bottom points**, so on at most one strand no bottom point is
capped. -/
theorem bottomCap_eq_empty_of_le_one (D : BrauerDiagram k) (hk : k ≤ 1) : D.bottomCap = ∅ := by
  have hsub : Subsingleton (Fin k) :=
    ⟨fun a b => Fin.val_injective (by have := a.isLt; have := b.isLt; omega)⟩
  refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
  obtain ⟨i', hi'⟩ : ∃ i', D.val (Sum.inl i) = Sum.inl i' :=
    ⟨_, (Sum.inl_getLeft _ ((D.isCap_def _).mp ((mem_bottomCap _).mp hi)).2).symm⟩
  exact D.apply_ne (Sum.inl i) (by rw [hi', Subsingleton.elim i' i])

/-- **On at most one strand the identity diagram is the only Brauer diagram.** -/
theorem eq_permToBrauer_one_of_le_one (D : BrauerDiagram k) (hk : k ≤ 1) :
    D = permToBrauer 1 := by
  obtain ⟨σ, rfl⟩ :=
    (exists_eq_permToBrauer_iff_bottomCap_eq_empty D).mpr (D.bottomCap_eq_empty_of_le_one hk)
  have hsub : Subsingleton (Fin k) :=
    ⟨fun a b => Fin.val_injective (by have := a.isLt; have := b.isLt; omega)⟩
  exact congrArg permToBrauer (Equiv.ext fun _ => Subsingleton.elim _ _)

/-! ### Two strands -/

/-- On two letters an index other than `0` is `1`. -/
private theorem fin_two_eq_one_of_ne_zero (i : Fin 2) (h : i ≠ 0) : i = 1 := by
  revert i
  decide

/-- On two letters a permutation is the identity or the transposition. -/
private theorem perm_fin_two_eq (σ : Equiv.Perm (Fin 2)) : σ = 1 ∨ σ = Equiv.swap 0 1 := by
  revert σ
  decide

/-- **A Brauer diagram on two strands either caps nothing, or caps and cups its whole boundary.**
The capped bottom points are even in number and there are at most two of them, so there are none
or two, and in the second case both the cap and the cup are forced. -/
theorem eq_permToBrauer_or_eq_capCup (D : BrauerDiagram 2) :
    (∃ σ : Equiv.Perm (Fin 2), D = permToBrauer σ) ∨ D = capCup 0 1 := by
  rcases Finset.eq_empty_or_nonempty D.bottomCap with h | h
  · exact Or.inl ((exists_eq_permToBrauer_iff_bottomCap_eq_empty D).mpr h)
  refine Or.inr ?_
  have hcard : D.bottomCap.card = 2 := by
    have hle : D.bottomCap.card ≤ 2 := by simpa using Finset.card_le_univ D.bottomCap
    have hpos : 0 < D.bottomCap.card := Finset.card_pos.mpr h
    obtain ⟨m, hm⟩ := D.even_card_bottomCap
    omega
  have hbot : ∀ i : Fin 2, D.IsCap (Sum.inl i) := by
    have huniv : D.bottomCap = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
    exact fun i => (mem_bottomCap _).mp (by rw [huniv]; exact Finset.mem_univ i)
  have htop : ∀ j : Fin 2, D.IsCup (Sum.inr j) := by
    have huniv : D.topCup = Finset.univ :=
      Finset.eq_univ_of_card _ (by
        rw [← D.card_bottomCap_eq_card_topCup, hcard, Fintype.card_fin])
    exact fun j => (mem_topCup _).mp (by rw [huniv]; exact Finset.mem_univ j)
  -- The cap at the bottom point `0` can only reach the bottom point `1`, and likewise the cup.
  have hcap : D.val (Sum.inl 0) = Sum.inl 1 := by
    obtain ⟨i, hi⟩ : ∃ i, D.val (Sum.inl 0) = Sum.inl i :=
      ⟨_, (Sum.inl_getLeft _ ((D.isCap_def _).mp (hbot 0)).2).symm⟩
    rw [hi, fin_two_eq_one_of_ne_zero i fun hz => D.apply_ne (Sum.inl 0) (by rw [hi, hz])]
  have hcup : D.val (Sum.inr 0) = Sum.inr 1 := by
    obtain ⟨j, hj⟩ : ∃ j, D.val (Sum.inr 0) = Sum.inr j :=
      ⟨_, (Sum.inr_getRight _ ((D.isCup_def _).mp (htop 0)).2).symm⟩
    rw [hj, fin_two_eq_one_of_ne_zero j fun hz => D.apply_ne (Sum.inr 0) (by rw [hj, hz])]
  exact (eq_capCup_iff (by decide)).mpr
    ⟨hcap, hcup, fun i hi0 hi1 => absurd (fin_two_eq_one_of_ne_zero i hi0) hi1⟩

/-- **The three Brauer diagrams on two strands**: the identity diagram, the crossing, and the
cap-cup diagram. -/
theorem eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup (D : BrauerDiagram 2) :
    D = permToBrauer 1 ∨ D = permToBrauer (Equiv.swap 0 1) ∨ D = capCup 0 1 := by
  rcases eq_permToBrauer_or_eq_capCup D with ⟨σ, rfl⟩ | h
  · rcases perm_fin_two_eq σ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr h)

/-- **The identity diagram and the crossing are distinct**, so the three diagrams on two strands
really are three. -/
theorem permToBrauer_one_ne_permToBrauer_swap :
    permToBrauer (1 : Equiv.Perm (Fin 2)) ≠ permToBrauer (Equiv.swap 0 1) := fun h =>
  (by decide : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1) (permToBrauer_injective 2 h)

/-- **The enumeration of the Brauer diagrams on two strands.** -/
theorem univ_two : (Finset.univ : Finset (BrauerDiagram 2)) =
    {permToBrauer 1, permToBrauer (Equiv.swap 0 1), capCup 0 1} := by
  refine Finset.ext fun D => ⟨fun _ => ?_, fun _ => Finset.mem_univ D⟩
  simpa using eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup D

-- The three diagrams listed are distinct, so their number is the general count `(2 * k - 1)‼`
-- at `k = 2`.
example : ({permToBrauer 1, permToBrauer (Equiv.swap 0 1), capCup 0 1} :
    Finset (BrauerDiagram 2)).card = (2 * 2 - 1)‼ := by
  rw [← univ_two, Finset.card_univ, card_brauerDiagram]

/-! ### The multiplication table on two strands -/

/-- **The cap-cup diagram absorbs on the right**: on two strands, stacking any diagram underneath
`e` gives `e` back. Each of the three cases is a relation already available on the diagram basis
for an arbitrary number of strands; what is special to two strands is that they are all the
cases. -/
theorem capCup_composeDiagram_two (D : BrauerDiagram 2) :
    composeDiagram (capCup 0 1) D = capCup 0 1 := by
  rcases eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup D with rfl | rfl | rfl
  · exact composeDiagram_permToBrauer_one_right _
  · exact composeDiagram_capCup_permToBrauer_swap 0 1
  · exact composeDiagram_capCup_capCup 0 1

/-- **The cap-cup diagram absorbs on the left**: on two strands, stacking any diagram above `e`
gives `e` back. -/
theorem composeDiagram_capCup_two (D : BrauerDiagram 2) :
    composeDiagram D (capCup 0 1) = capCup 0 1 := by
  rcases eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup D with rfl | rfl | rfl
  · exact composeDiagram_permToBrauer_one_left _
  · exact composeDiagram_permToBrauer_swap_capCup 0 1
  · exact composeDiagram_capCup_capCup 0 1

/-- **The loop rule on two strands**: the only product of Brauer diagrams on two strands that
closes a loop up in the middle is `e * e`, which closes exactly one. So the loop-weighted
multiplication of `B₂(δ)` is the stacking of diagrams with the single correction
`e * e = δ • e`. -/
theorem middleLoopCount_two (D₁ D₂ : BrauerDiagram 2) :
    middleLoopCount D₁ D₂ = if D₁ = capCup 0 1 ∧ D₂ = capCup 0 1 then 1 else 0 := by
  have hne : ∀ σ : Equiv.Perm (Fin 2), permToBrauer σ ≠ capCup 0 1 := fun σ h =>
    capCup_ne_permToBrauer (a := 0) (b := 1) (by decide) σ h.symm
  rcases eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup D₁ with rfl | rfl | rfl
  · rw [middleLoopCount_permToBrauer_left]
    simp [hne 1]
  · rw [middleLoopCount_permToBrauer_left]
    simp [hne (Equiv.swap 0 1)]
  rcases eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup D₂ with rfl | rfl | rfl
  · rw [middleLoopCount_permToBrauer_right]
    simp [hne 1]
  · rw [middleLoopCount_permToBrauer_right]
    simp [hne (Equiv.swap 0 1)]
  · rw [middleLoopCount_capCup_capCup (by decide)]
    simp

/-! The four products of permutation diagrams complete the table. They are instances of
`TauCeti.composeDiagram_permToBrauer`, so no name is claimed for them; what the `example`s record
is that the general relations do assemble into the table of `B₂(δ)`, with `1` a two-sided identity
and `s * s = 1`. -/

-- `1 * 1 = 1`.
example : composeDiagram (permToBrauer (1 : Equiv.Perm (Fin 2))) (permToBrauer 1) =
    permToBrauer 1 := by rw [composeDiagram_permToBrauer, one_mul]

-- `1 * s = s` and `s * 1 = s`.
example : composeDiagram (permToBrauer (1 : Equiv.Perm (Fin 2))) (permToBrauer (Equiv.swap 0 1)) =
    permToBrauer (Equiv.swap 0 1) := by rw [composeDiagram_permToBrauer, one_mul]

example : composeDiagram (permToBrauer (Equiv.swap (0 : Fin 2) 1)) (permToBrauer 1) =
    permToBrauer (Equiv.swap 0 1) := by rw [composeDiagram_permToBrauer, mul_one]

-- `s * s = 1`.
example : composeDiagram (permToBrauer (Equiv.swap (0 : Fin 2) 1))
    (permToBrauer (Equiv.swap 0 1)) = permToBrauer 1 := by
  rw [composeDiagram_permToBrauer, Equiv.swap_mul_self]

end BrauerDiagram

end TauCeti
