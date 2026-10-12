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

What decides the list is the count `TauCeti.card_brauerDiagram`: there are `(2 * k - 1)‼`
Brauer diagrams on `k` strands. On `k ≤ 1` strands that count is `1`, so the identity diagram is
the only diagram (`TauCeti.BrauerDiagram.eq_permToBrauer_one_of_le_one`). On two strands it is
`3`, and the three diagrams

`1` (two through strands), `s` (the crossing), and `e` (the cap on the bottom together with the
cup on the top),

are pairwise distinct, hence all of them
(`TauCeti.BrauerDiagram.univ_two` and
`TauCeti.BrauerDiagram.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup`).

Their nine products are then Brauer's relations for `B₂(δ)`. On the diagram basis `1` is a
two-sided identity, `s` composed with itself is `1`, and `e` absorbs every diagram from either
side (`TauCeti.composeDiagram_capCup_left_two` and `TauCeti.composeDiagram_capCup_right_two`).
The loop-weighted multiplication `D₁ * D₂ = δ ^ middleLoopCount D₁ D₂ • composeDiagram D₁ D₂` of
`B₂(δ)` differs from that stacking for the product of `e` with itself alone, where exactly one
loop closes up in the middle (`TauCeti.middleLoopCount_two`). So the relations of `B₂(δ)` read
`s * s = 1`, `s * e = e = e * s` and `e * e = δ • e`.

## Main results

* `TauCeti.BrauerDiagram.eq_permToBrauer_one_of_le_one`: on at most one strand the identity
  diagram is the only diagram.
* `TauCeti.BrauerDiagram.univ_two` and
  `TauCeti.BrauerDiagram.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup`: **the three
  Brauer diagrams on two strands**, as an enumeration of the whole type and as a case
  distinction.
* `TauCeti.composeDiagram_capCup_left_two` and `TauCeti.composeDiagram_capCup_right_two`: on two
  strands the cap-cup diagram absorbs every diagram from either side.
* `TauCeti.middleLoopCount_two`: on two strands a loop closes up in the middle only for the
  product of the cap-cup diagram with itself, where exactly one does.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
-/

public section

open scoped Nat

namespace TauCeti

namespace BrauerDiagram

/-! ### At most one strand -/

/-- **On at most one strand the identity diagram is the only Brauer diagram.** -/
theorem eq_permToBrauer_one_of_le_one {k : ℕ} (D : BrauerDiagram k) (hk : k ≤ 1) :
    D = permToBrauer 1 := by
  have hcard : Fintype.card (BrauerDiagram k) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · rw [card_brauerDiagram]
      decide
    · rw [card_brauerDiagram]
      decide
  exact Fintype.card_le_one_iff.mp hcard D (permToBrauer 1)

/-! ### Two strands -/

/-- **The enumeration of the Brauer diagrams on two strands**: the identity diagram, the crossing
and the cap-cup diagram, which are three in number as `TauCeti.card_brauerDiagram` asks. -/
theorem univ_two : (Finset.univ : Finset (BrauerDiagram 2)) =
    {permToBrauer 1, permToBrauer (Equiv.swap 0 1), capCup 0 1} := by
  have hne : ∀ σ : Equiv.Perm (Fin 2), permToBrauer σ ≠ capCup 0 1 := fun σ h =>
    capCup_ne_permToBrauer (a := 0) (b := 1) (by decide) σ h.symm
  have hswap : permToBrauer (1 : Equiv.Perm (Fin 2)) ≠ permToBrauer (Equiv.swap 0 1) := by
    intro h
    have h0 : (permToBrauer (1 : Equiv.Perm (Fin 2))).val (Sum.inl 0)
        = (permToBrauer (Equiv.swap 0 1)).val (Sum.inl 0) := by rw [h]
    simp [Equiv.swap_apply_left] at h0
  have hmem : permToBrauer (1 : Equiv.Perm (Fin 2)) ∉
      ({permToBrauer (Equiv.swap 0 1), capCup 0 1} : Finset (BrauerDiagram 2)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim hswap (hne 1)
  refine (Finset.eq_univ_of_card _ ?_).symm
  rw [Finset.card_insert_of_notMem hmem,
    Finset.card_pair_eq_two_iff.mpr (hne (Equiv.swap 0 1)), card_brauerDiagram]
  decide

/-- **The three Brauer diagrams on two strands**: the identity diagram, the crossing, and the
cap-cup diagram. -/
theorem eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup (D : BrauerDiagram 2) :
    D = permToBrauer 1 ∨ D = permToBrauer (Equiv.swap 0 1) ∨ D = capCup 0 1 := by
  have hD : D ∈ ({permToBrauer 1, permToBrauer (Equiv.swap 0 1), capCup 0 1} :
      Finset (BrauerDiagram 2)) := by
    rw [← univ_two]
    exact Finset.mem_univ D
  simpa using hD

-- The three diagrams are `(2 * 2 - 1)‼` in number, the dimension of `B₂(δ)`.
example : ({permToBrauer 1, permToBrauer (Equiv.swap 0 1), capCup 0 1} :
    Finset (BrauerDiagram 2)).card = (2 * 2 - 1)‼ := by
  rw [← univ_two, Finset.card_univ, card_brauerDiagram]

end BrauerDiagram

/-! ### The multiplication table on two strands -/

/-- **The cap-cup diagram absorbs on the left**: on two strands, stacking any diagram underneath
`e` gives `e` back. -/
@[simp]
theorem composeDiagram_capCup_left_two (D : BrauerDiagram 2) :
    composeDiagram (capCup 0 1) D = capCup 0 1 := by
  rcases D.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl
  · exact composeDiagram_permToBrauer_one_right _
  · exact composeDiagram_capCup_permToBrauer_swap 0 1
  · exact composeDiagram_capCup_capCup 0 1

/-- **The cap-cup diagram absorbs on the right**: on two strands, stacking any diagram above `e`
gives `e` back. -/
@[simp]
theorem composeDiagram_capCup_right_two (D : BrauerDiagram 2) :
    composeDiagram D (capCup 0 1) = capCup 0 1 := by
  rcases D.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl
  · exact composeDiagram_permToBrauer_one_left _
  · exact composeDiagram_permToBrauer_swap_capCup 0 1
  · exact composeDiagram_capCup_capCup 0 1

/-- **The loop rule on two strands**: the only product of Brauer diagrams on two strands that
closes a loop up in the middle is `e * e`, which closes exactly one. So the loop-weighted
multiplication of `B₂(δ)` is the stacking of diagrams with the single correction
`e * e = δ • e`. -/
@[simp]
theorem middleLoopCount_two (D₁ D₂ : BrauerDiagram 2) :
    middleLoopCount D₁ D₂ = if D₁ = capCup 0 1 ∧ D₂ = capCup 0 1 then 1 else 0 := by
  have hperm : ∀ D : BrauerDiagram 2, D ≠ capCup 0 1 →
      ∃ σ : Equiv.Perm (Fin 2), D = permToBrauer σ := by
    intro D hD
    rcases D.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨Equiv.swap 0 1, rfl⟩
    · exact absurd rfl hD
  rcases eq_or_ne D₁ (capCup 0 1) with rfl | h₁
  · rcases eq_or_ne D₂ (capCup 0 1) with rfl | h₂
    · rw [middleLoopCount_capCup_capCup (by decide)]
      simp
    · obtain ⟨σ, rfl⟩ := hperm D₂ h₂
      rw [middleLoopCount_permToBrauer_right]
      simp [h₂]
  · obtain ⟨σ, rfl⟩ := hperm D₁ h₁
    rw [middleLoopCount_permToBrauer_left]
    simp [h₁]

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

end TauCeti
