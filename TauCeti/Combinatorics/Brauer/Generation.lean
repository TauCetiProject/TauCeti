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
* `TauCeti.composeDiagram_capCup_left` and `TauCeti.composeDiagram_capCup_right`: stacking
  `capCup a b` above (or below) any diagram `D` reconnects the top (or bottom) points `a` and `b`
  of `D`.
* `TauCeti.middleLoopCount_capCup_left` and `TauCeti.middleLoopCount_capCup_right`: for `a ≠ b`,
  that stack closes up one middle loop when `D` already joins those two boundary points, and none
  otherwise.
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

/-! ### Stacking a cap-cup diagram with an arbitrary diagram -/

namespace BrauerDiagram

/-- Reflecting a reconnected diagram reconnects the reflected endpoints in the reflected diagram. -/
@[simp]
theorem flip_reconnect (D : BrauerDiagram k) (x y : Fin k ⊕ Fin k) :
    flip (D.reconnect x y) = D.flip.reconnect x.swap y.swap := by
  have hswap : ∀ u v w : Fin k ⊕ Fin k,
      (Equiv.swap u.swap v.swap) w = ((Equiv.swap u v) w.swap).swap := fun u v w => by
    rcases u with _ | _ <;> rcases v with _ | _ <;> rcases w with _ | _ <;>
      simp [Equiv.swap_apply_def] <;> split_ifs <;> simp_all
  refine Subtype.ext (Equiv.ext fun z => ?_)
  rw [flip_val, PerfectMatching.reconnect_val, PerfectMatching.reconnect_val,
    Equiv.permCongr_apply, Equiv.permCongr_apply, flip_val_swap]
  simp only [Equiv.symm_swap, hswap, flip_val_swap, Sum.swap_swap]

end BrauerDiagram

section CapCupStack

/-- When `D` does not cup `a` to `b`, the strand of `capCup a b ∘ D` starting at `D.val (Sum.inr a)`
runs through the cap `a`–`b` of `capCup a b` and emerges at `D.val (Sum.inr b)`. -/
private theorem composeDiagram_capCup_val_partner (hab : a ≠ b)
    (hcup : D.val (Sum.inr a) ≠ Sum.inr b) :
    (composeDiagram (capCup a b) D).val (D.val (Sum.inr a)) = D.val (Sum.inr b) := by
  set p := D.val (Sum.inr a) with hp_def
  set q := D.val (Sum.inr b) with hq_def
  have hp_val : D.val p = Sum.inr a := D.apply_apply (Sum.inr a)
  have hpa : p ≠ Sum.inr a := D.apply_ne (Sum.inr a)
  have hqb : q ≠ Sum.inr b := D.apply_ne (Sum.inr b)
  have hqa : q ≠ Sum.inr a := fun h => hcup (D.apply_eq_of_apply_eq (hq_def.symm.trans h))
  have hcap_step : stackStep (capCup a b) D (Sum.inl a) = Sum.inr (Sum.inr b) := by
    rw [stackStep_inl, capCup_val_inl_left hab, Sum.elim_inl]
  rw [composeDiagram_val_eq_iff]
  refine Or.inr ?_
  rcases p with i | i
  · have hstart : stackStart (capCup a b) D (Sum.inl i) = Sum.inr (Sum.inl a) := by
      rw [stackStart_inl, hp_val, Sum.elim_inr]
    rcases q with j | j
    · exact ⟨Sum.inl a, Sum.inr b, hstart, .single hcap_step,
        by rw [stackStep_inr, ← hq_def, Sum.elim_inl]⟩
    · have hja : j ≠ a := fun h => hqa (congrArg Sum.inr h)
      have hjb : j ≠ b := fun h => hqb (congrArg Sum.inr h)
      exact ⟨Sum.inl a, Sum.inl j, hstart,
        Relation.ReflTransGen.tail (.single hcap_step)
          (by rw [stackStep_inr, ← hq_def, Sum.elim_inr]),
        by rw [stackStep_inl, capCup_val_inl_of_ne hja hjb, Sum.elim_inr]⟩
  · have hia : i ≠ a := fun h => hpa (congrArg Sum.inr h)
    have hib : i ≠ b := fun h => hcup (congrArg Sum.inr h)
    have hstart : stackStart (capCup a b) D (Sum.inr i) = Sum.inr (Sum.inr i) := by
      rw [stackStart_inr, capCup_val_inr_of_ne hia hib, Sum.elim_inl]
    have hstep₁ : stackStep (capCup a b) D (Sum.inr i) = Sum.inr (Sum.inl a) := by
      rw [stackStep_inr, hp_val, Sum.elim_inr]
    rcases q with j | j
    · exact ⟨Sum.inr i, Sum.inr b, hstart,
        Relation.ReflTransGen.tail (.single hstep₁) hcap_step,
        by rw [stackStep_inr, ← hq_def, Sum.elim_inl]⟩
    · have hja : j ≠ a := fun h => hqa (congrArg Sum.inr h)
      have hjb : j ≠ b := fun h => hqb (congrArg Sum.inr h)
      exact ⟨Sum.inr i, Sum.inl j, hstart,
        Relation.ReflTransGen.tail (Relation.ReflTransGen.tail (.single hstep₁) hcap_step)
          (by rw [stackStep_inr, ← hq_def, Sum.elim_inr]),
        by rw [stackStep_inl, capCup_val_inl_of_ne hja hjb, Sum.elim_inr]⟩

/-- **Stacking `capCup a b` above `D` reconnects the top points `a` and `b` of `D`**: when `D`
already cups `a` to `b` this leaves `D` unchanged, and otherwise it cups `a` to `b` and joins their
old partners in `D` to one another. -/
theorem composeDiagram_capCup_left (a b : Fin k) (D : BrauerDiagram k) :
    composeDiagram (capCup a b) D = D.reconnect (Sum.inr a) (Sum.inr b) := by
  rcases eq_or_ne a b with rfl | hab
  · rw [capCup_self, composeDiagram_permToBrauer_one_left, PerfectMatching.reconnect_self]
  have hba_inr : (Sum.inr b : Fin k ⊕ Fin k) ≠ Sum.inr a := Sum.inr_injective.ne hab.symm
  refine Subtype.ext (Equiv.ext fun x => ?_)
  by_cases hxa : x = Sum.inr a
  · subst hxa
    rw [composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hab),
      PerfectMatching.reconnect_val_self hba_inr]
  by_cases hxb : x = Sum.inr b
  · subst hxb
    rw [composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_right hab),
      PerfectMatching.reconnect_val_right hba_inr]
  have hpass (hya : D.val x ≠ Sum.inr a) (hyb : D.val x ≠ Sum.inr b) :
      (composeDiagram (capCup a b) D).val x = D.val x := by
    rcases x with i | j <;> rcases hy : D.val _ with i' | j'
    · exact composeDiagram_val_inl_eq_inl_of_cap_lower _ _ hy
    · rw [hy] at hya hyb
      exact composeDiagram_val_inl_eq_inr_of_through _ _ hy
        (capCup_val_inl_of_ne (by simpa using hya) (by simpa using hyb))
    · exact composeDiagram_val_inr_eq_inl_of_through _ _
        (capCup_val_inr_of_ne (by simpa using hxa) (by simpa using hxb)) hy
    · rw [hy] at hya hyb
      exact composeDiagram_val_inr_eq_inr_of_cup_lower _ _
        (capCup_val_inr_of_ne (by simpa using hxa) (by simpa using hxb)) hy
        (capCup_val_inl_of_ne (by simpa using hya) (by simpa using hyb))
  by_cases hcup : D.val (Sum.inr a) = Sum.inr b
  · have hrec : D.reconnect (Sum.inr a) (Sum.inr b) = D :=
      hcup ▸ PerfectMatching.reconnect_partner D (Sum.inr a)
    rw [hrec]
    exact hpass (fun h => hxb (by simpa [hcup] using congrArg D.val h))
      (fun h => hxa (by simpa [D.apply_eq_of_apply_eq hcup] using congrArg D.val h))
  · by_cases hxp : x = D.val (Sum.inr a)
    · subst hxp
      rw [composeDiagram_capCup_val_partner hab hcup,
        PerfectMatching.reconnect_val_val_self hba_inr]
    by_cases hxq : x = D.val (Sum.inr b)
    · subst hxq
      rw [(composeDiagram (capCup a b) D).apply_eq_of_apply_eq
          (composeDiagram_capCup_val_partner hab hcup),
        PerfectMatching.reconnect_val_val_right hba_inr]
    rw [PerfectMatching.reconnect_val_of_ne hxa hxb hxp hxq]
    exact hpass (fun h => hxp (by simpa using congrArg D.val h))
      (fun h => hxq (by simpa using congrArg D.val h))

/-- **Stacking `capCup a b` below `D` reconnects the bottom points `a` and `b` of `D`**, the
reflection of `TauCeti.composeDiagram_capCup_left`. -/
theorem composeDiagram_capCup_right (D : BrauerDiagram k) (a b : Fin k) :
    composeDiagram D (capCup a b) = D.reconnect (Sum.inl a) (Sum.inl b) := by
  simpa using congrArg BrauerDiagram.flip (composeDiagram_capCup_left a b D.flip)

/-- **Stacking `capCup a b` (`a ≠ b`) above `D` closes up one loop when `D` cups `a` to `b`, and no
loop otherwise.** -/
theorem middleLoopCount_capCup_left (hab : a ≠ b) (D : BrauerDiagram k) :
    middleLoopCount (capCup a b) D = if D.val (Sum.inr a) = Sum.inr b then 1 else 0 := by
  split_ifs with hcup
  · have hloop_iff {x : Fin k} : OnMiddleLoop (capCup a b) D x ↔ x = a ∨ x = b := by
      refine ⟨fun hx => (BrauerDiagram.isCap_capCup_inl_iff hab).mp
        ((isMiddleVertex_def _ _ _).mp hx.isMiddleVertex).1, ?_⟩
      rintro (rfl | rfl)
      · exact onMiddleLoop_of_val_eq (capCup_val_inl_left hab) hcup
      · exact onMiddleLoop_of_val_eq (capCup_val_inl_right hab) (D.apply_eq_of_apply_eq hcup)
    have hset : {x : Fin k | IsMiddleLoopMin (capCup a b) D x} = {min a b} := by
      have hab' : Relation.ReflTransGen (MiddleAdj (capCup a b) D) a b :=
        .single ((middleAdj_def _ _ _ _).mpr (Or.inl (capCup_val_inl_left hab)))
      have hba' : Relation.ReflTransGen (MiddleAdj (capCup a b) D) b a :=
        .single ((middleAdj_def _ _ _ _).mpr (Or.inl (capCup_val_inl_right hab)))
      ext x
      rw [Set.mem_ofPred_eq, isMiddleLoopMin_def, hloop_iff, Set.mem_singleton_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨rfl | rfl, hmin⟩
        · exact (min_eq_left (hmin _ hab')).symm
        · exact (min_eq_right (hmin _ hba')).symm
      · rintro rfl
        rcases le_total a b with hle | hle
        · rw [min_eq_left hle]
          refine ⟨Or.inl rfl, fun y hy => ?_⟩
          rcases hloop_iff.mp ((hloop_iff.mpr (Or.inl rfl)).reflTransGen hy) with rfl | rfl
          · exact le_rfl
          · exact hle
        · rw [min_eq_right hle]
          refine ⟨Or.inr rfl, fun y hy => ?_⟩
          rcases hloop_iff.mp ((hloop_iff.mpr (Or.inr rfl)).reflTransGen hy) with rfl | rfl
          · exact hle
          · exact le_rfl
    rw [middleLoopCount_def, hset, Set.ncard_singleton]
  · refine middleLoopCount_eq_zero_iff.mpr fun x hx => ?_
    have ha : OnMiddleLoop (capCup a b) D a := by
      rcases (BrauerDiagram.isCap_capCup_inl_iff hab).mp
        ((isMiddleVertex_def _ _ _).mp hx.isMiddleVertex).1 with rfl | rfl
      · exact hx
      · exact hx.reflTransGen
          (.single ((middleAdj_def _ _ _ _).mpr (Or.inl (capCup_val_inl_right hab))))
    obtain ⟨c, hc⟩ := Sum.isRight_iff.mp
      ((BrauerDiagram.isCup_def D _).mp ((isMiddleVertex_def _ _ _).mp ha.isMiddleVertex).2).2
    have hc_loop : OnMiddleLoop (capCup a b) D c :=
      ha.reflTransGen (.single ((middleAdj_def _ _ _ _).mpr (Or.inr hc)))
    rcases (BrauerDiagram.isCap_capCup_inl_iff hab).mp
      ((isMiddleVertex_def _ _ _).mp hc_loop.isMiddleVertex).1 with rfl | rfl
    · exact D.apply_ne (Sum.inr c) hc
    · exact hcup hc

/-- **Stacking `capCup a b` (`a ≠ b`) below `D` closes up one loop when `D` caps `a` to `b`, and no
loop otherwise**, the reflection of `TauCeti.middleLoopCount_capCup_left`. -/
theorem middleLoopCount_capCup_right (D : BrauerDiagram k) (hab : a ≠ b) :
    middleLoopCount D (capCup a b) = if D.val (Sum.inl a) = Sum.inl b then 1 else 0 := by
  rw [← middleLoopCount_flip, BrauerDiagram.flip_capCup, middleLoopCount_capCup_left hab,
    BrauerDiagram.flip_val_inr]
  rcases D.val (Sum.inl a) with c | c <;> simp

end CapCupStack

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
