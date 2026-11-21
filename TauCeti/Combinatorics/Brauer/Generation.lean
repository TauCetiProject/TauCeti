/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Generator

/-!
# Every Brauer diagram is built from cap-cup diagrams and a permutation diagram

A Brauer diagram `D` with a cap has a cup as well, since it has as many caps as cups. Take a cap
of `D`, joining the bottom points `a` and `b`, and a cup, joining the top points `c` and `d`.
Reconnecting these two arcs into the through strands `a`–`c` and `b`–`d` gives a diagram `X` with
one cap fewer, `X = D.reconnect (Sum.inr c) (Sum.inl a)`. Stacking the cap-cup diagram
`TauCeti.capCup c d` above `X` undoes the reconnection: its cup restores the cup `c`–`d`, and its
cap joins the middle points `c` and `d`, where the strands of `X` from `a` and from `b` arrive, so
it restores the cap `a`–`b`. Every other strand of `X` passes straight through the cap-cup
diagram. No closed loop is formed in the middle, because every middle point lies on a through
strand of one of the two diagrams. So

`D = capCup c d ∘ X` with no middle loop (`TauCeti.composeDiagram_capCup_reconnect` and
`TauCeti.middleLoopCount_capCup_reconnect`).

Repeating this until no cap is left reaches a diagram without caps, which is a permutation
diagram. This gives an induction principle for Brauer diagrams
(`TauCeti.BrauerDiagram.capCup_induction_on`): a property of diagrams that holds for the
permutation diagrams, and passes from `X` to `capCup a b ∘ X` whenever no loop closes up in the
middle, holds for every diagram. In the Brauer algebra, where a loop-free stack is the product,
this says that the permutation diagrams and the cap-cup diagrams generate the algebra
(`TauCeti/Algebra/BrauerAlgebra/Generation.lean`).

## Main results

* `TauCeti.composeDiagram_capCup_reconnect`: stacking `capCup c d` above the reconnected diagram
  gives back `D`.
* `TauCeti.middleLoopCount_capCup_reconnect`: that stack closes up no loop.
* `TauCeti.BrauerDiagram.bottomCap_reconnect`: the reconnected diagram caps the bottom points of
  `D` other than `a` and `b`, so it has one cap fewer
  (`TauCeti.BrauerDiagram.card_bottomCap_reconnect`).
* `TauCeti.BrauerDiagram.capCup_induction_on`: **induction on Brauer diagrams** from the
  permutation diagrams by stacking cap-cup diagrams on top.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

namespace TauCeti

variable {k : ℕ} {a b c d : Fin k} {D : BrauerDiagram k}

/-! ### The arcs of the reconnected diagram -/

namespace BrauerDiagram

section Reconnect

variable (hcap : D.val (Sum.inl a) = Sum.inl b) (hcup : D.val (Sum.inr c) = Sum.inr d)
include hcap hcup

/-- **The reconnected diagram has one cap fewer**: it caps exactly the bottom points capped by `D`
other than `a` and `b`. -/
theorem bottomCap_reconnect :
    bottomCap (D.reconnect (Sum.inr c) (Sum.inl a)) = (D.bottomCap.erase a).erase b := by
  ext i
  simp only [mem_bottomCap, Finset.mem_erase, isCap_def, Sum.isLeft_inl, true_and]
  by_cases hia : i = a
  · subst i
    simp [PerfectMatching.reconnect_val_right Sum.inl_ne_inr]
  by_cases hib : i = b
  · subst i
    simp [hcap ▸ hcup ▸ PerfectMatching.reconnect_val_val_right (D := D) Sum.inl_ne_inr]
  rw [PerfectMatching.reconnect_val_of_ne Sum.inl_ne_inr (by simpa using hia)
    (hcup ▸ Sum.inl_ne_inr) (hcap ▸ by simpa using hib)]
  simp [hia, hib]

/-- The reconnected diagram has two capped bottom points fewer than `D`. -/
theorem card_bottomCap_reconnect :
    (bottomCap (D.reconnect (Sum.inr c) (Sum.inl a))).card + 2 = D.bottomCap.card := by
  have hab : b ≠ a := fun h => D.apply_ne (Sum.inl a) (by rw [hcap, h])
  have ha : a ∈ D.bottomCap := by simp [isCap_def, hcap]
  have hb : b ∈ D.bottomCap.erase a := by
    simp [hab, isCap_def, D.apply_eq_of_apply_eq hcap]
  have h : 0 < (D.bottomCap.erase a).card := Finset.card_pos.mpr ⟨b, hb⟩
  rw [Finset.card_erase_of_mem ha] at h
  rw [bottomCap_reconnect hcap hcup, Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
  omega

end Reconnect

end BrauerDiagram

/-! ### Undoing the reconnection by a cap-cup diagram -/

/-- **A cap-cup diagram undoes the reconnection of a cap and a cup.** If `D` cups the top points
`c` and `d`, then stacking `capCup c d` above `D.reconnect (Sum.inr c) (Sum.inl a)` reconnects
`Sum.inr c` back to `Sum.inr d` and gives back `D`. -/
theorem composeDiagram_capCup_reconnect (a : Fin k) (hcup : D.val (Sum.inr c) = Sum.inr d) :
    composeDiagram (capCup c d) (D.reconnect (Sum.inr c) (Sum.inl a)) = D := by
  rw [composeDiagram_capCup_left, ← hcup, PerfectMatching.reconnect_reconnect_val]

/-- **Undoing the reconnection closes up no loop**: in `D.reconnect (Sum.inr c) (Sum.inl a)`, the
top point `c` is joined to the bottom point `a` rather than to `Sum.inr d`. -/
theorem middleLoopCount_capCup_reconnect (a c d : Fin k) (D : BrauerDiagram k) :
    middleLoopCount (capCup c d) (D.reconnect (Sum.inr c) (Sum.inl a)) = 0 := by
  rw [middleLoopCount_capCup_left, PerfectMatching.reconnect_val_self Sum.inl_ne_inr,
    ite_eq_right Sum.inl_ne_inr]

/-! ### Induction on Brauer diagrams -/

namespace BrauerDiagram

/-- **A diagram with a cap is a loop-free stack of a cap-cup diagram on a diagram with one cap
fewer.** -/
theorem exists_composeDiagram_capCup_eq (ha : a ∈ D.bottomCap) :
    ∃ c d : Fin k, ∃ X : BrauerDiagram k, c ≠ d ∧ middleLoopCount (capCup c d) X = 0 ∧
      X.bottomCap.card + 2 = D.bottomCap.card ∧ composeDiagram (capCup c d) X = D := by
  obtain ⟨b, hcap⟩ : ∃ b, D.val (Sum.inl a) = Sum.inl b :=
    Sum.isLeft_iff.mp ((isCap_def D _).mp ((mem_bottomCap D).mp ha)).2
  obtain ⟨c, hc⟩ : D.topCup.Nonempty := by
    rw [← Finset.card_pos, ← card_bottomCap_eq_card_topCup]
    exact Finset.card_pos.mpr ⟨a, ha⟩
  obtain ⟨d, hcup⟩ : ∃ d, D.val (Sum.inr c) = Sum.inr d :=
    Sum.isRight_iff.mp ((isCup_def D _).mp ((mem_topCup D).mp hc)).2
  exact ⟨c, d, _, fun h => D.apply_ne (Sum.inr c) (by rw [hcup, h]),
    middleLoopCount_capCup_reconnect a c d D, card_bottomCap_reconnect hcap hcup,
    composeDiagram_capCup_reconnect a hcup⟩

/-- **Induction on Brauer diagrams.** A property of Brauer diagrams that holds for every
permutation diagram, and passes from a diagram `X` to the stack `capCup a b ∘ X` of a cap-cup
diagram on two distinct strands above it whenever that stack closes up no loop, holds for every
Brauer diagram. -/
@[elab_as_elim]
theorem capCup_induction_on {motive : BrauerDiagram k → Prop} (D : BrauerDiagram k)
    (permToBrauer : ∀ σ : Equiv.Perm (Fin k), motive (permToBrauer σ))
    (capCup_compose : ∀ (a b : Fin k) (X : BrauerDiagram k), a ≠ b →
      middleLoopCount (capCup a b) X = 0 → motive X → motive (composeDiagram (capCup a b) X)) :
    motive D := by
  induction hD : D.bottomCap.card using Nat.strong_induction_on generalizing D with
  | _ m ih =>
    obtain hempty | ⟨a, ha⟩ := D.bottomCap.eq_empty_or_nonempty
    · obtain ⟨σ, rfl⟩ := (exists_eq_permToBrauer_iff_bottomCap_eq_empty (D := D)).mpr hempty
      exact permToBrauer σ
    obtain ⟨c, d, X, hcd, hloop, hcard, rfl⟩ := exists_composeDiagram_capCup_eq ha
    exact capCup_compose c d X hcd hloop (ih _ (by omega) X rfl)

end BrauerDiagram

end TauCeti
