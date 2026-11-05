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

section Reconnect

variable (hcap : D.val (Sum.inl a) = Sum.inl b) (hcup : D.val (Sum.inr c) = Sum.inr d)
include hcap hcup

open BrauerDiagram

/-- **A cap-cup diagram undoes the reconnection of a cap and a cup.** If `D` caps the bottom
points `a` and `b` and cups the top points `c` and `d`, then stacking `capCup c d` above the
diagram `D.reconnect (Sum.inr c) (Sum.inl a)`, in which these two arcs have become the through
strands `a`–`c` and `b`–`d`, gives back `D`. -/
theorem composeDiagram_capCup_reconnect :
    composeDiagram (capCup c d) (D.reconnect (Sum.inr c) (Sum.inl a)) = D := by
  set X := D.reconnect (Sum.inr c) (Sum.inl a)
  have hcd : c ≠ d := fun h => D.apply_ne (Sum.inr c) (by rw [hcup, h])
  have hba : D.val (Sum.inl b) = Sum.inl a := D.apply_eq_of_apply_eq hcap
  have hdc : D.val (Sum.inr d) = Sum.inr c := D.apply_eq_of_apply_eq hcup
  have hXa : X.val (Sum.inl a) = Sum.inr c := PerfectMatching.reconnect_val_right Sum.inl_ne_inr
  have hXb : X.val (Sum.inl b) = Sum.inr d :=
    hcap ▸ hcup ▸ PerfectMatching.reconnect_val_val_right Sum.inl_ne_inr
  have hXc : X.val (Sum.inr c) = Sum.inl a := PerfectMatching.reconnect_val_self Sum.inl_ne_inr
  have hXd : X.val (Sum.inr d) = Sum.inl b :=
    hcap ▸ hcup ▸ PerfectMatching.reconnect_val_val_self Sum.inl_ne_inr
  refine Subtype.ext (Equiv.ext fun x => ?_)
  -- The four points `a`, `b`, `c`, `d` are treated by hand; every other point keeps its arc.
  by_cases hxa : x = Sum.inl a
  · subst x
    rw [hcap]
    exact composeDiagram_val_inl_eq_inl_of_cap_upper _ _ hXa
      (capCup_val_inl_left hcd) hXd
  by_cases hxb : x = Sum.inl b
  · subst x
    rw [hba]
    exact composeDiagram_val_inl_eq_inl_of_cap_upper _ _ hXb
      (capCup_val_inl_right hcd) hXc
  by_cases hxc : x = Sum.inr c
  · subst x
    rw [hcup]
    exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hcd)
  by_cases hxd : x = Sum.inr d
  · subst x
    rw [hdc]
    exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_right hcd)
  have hX : X.val x = D.val x :=
    PerfectMatching.reconnect_val_of_ne hxc hxa (hcup ▸ hxd) (hcap ▸ hxb)
  obtain ⟨hyc, hyd⟩ := (D.apply_ne_and_ne_iff hcup x).mpr ⟨hxc, hxd⟩
  rcases x with i | j <;> rcases hy : D.val _ with i' | j'
  · exact composeDiagram_val_inl_eq_inl_of_cap_lower _ _ (hX.trans hy)
  · rw [hy] at hyc hyd
    exact composeDiagram_val_inl_eq_inr_of_through _ _ (hX.trans hy)
      (capCup_val_inl_of_ne (by simpa using hyc) (by simpa using hyd))
  · exact composeDiagram_val_inr_eq_inl_of_through _ _
      (capCup_val_inr_of_ne (by simpa using hxc) (by simpa using hxd)) (hX.trans hy)
  · rw [hy] at hyc hyd
    exact composeDiagram_val_inr_eq_inr_of_cup_lower _ _
      (capCup_val_inr_of_ne (by simpa using hxc) (by simpa using hxd)) (hX.trans hy)
      (capCup_val_inl_of_ne (by simpa using hyc) (by simpa using hyd))

/-- **Undoing the reconnection closes up no loop**: every middle point lies on a through strand,
of the reconnected diagram at the two middle points `c` and `d` of the cap, and of the cap-cup
diagram at every other middle point. -/
theorem middleLoopCount_capCup_reconnect :
    middleLoopCount (capCup c d) (D.reconnect (Sum.inr c) (Sum.inl a)) = 0 := by
  refine middleLoopCount_eq_zero_iff.mpr fun m => ?_
  by_cases hmc : m = c
  · subst m
    exact not_onMiddleLoop_of_isThrough_right <| by
      simp [isThrough_def]
  by_cases hmd : m = d
  · subst m
    exact not_onMiddleLoop_of_isThrough_right <| by
      simp [isThrough_def,
        hcap ▸ hcup ▸ PerfectMatching.reconnect_val_val_self (D := D) Sum.inl_ne_inr]
  exact not_onMiddleLoop_of_isThrough_left <| by
    simp [isThrough_def, capCup_val_inl_of_ne hmc hmd]

end Reconnect

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
    middleLoopCount_capCup_reconnect hcap hcup, card_bottomCap_reconnect hcap hcup,
    composeDiagram_capCup_reconnect hcap hcup⟩

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
