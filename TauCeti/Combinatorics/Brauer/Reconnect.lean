/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Generator

import TauCeti.Combinatorics.Brauer.Relations

/-!
# Reconnecting caps and cups in Brauer diagrams

`TauCeti/Combinatorics/Brauer/Generation.lean` decomposes any Brauer diagram `D` with a bottom cap
`(a, b)` and a top cup `(c, d)` as the loop-free stack `D = capCup c d ∘ X` above the reconnected
diagram `X = D.reconnect (Sum.inr c) (Sum.inl a)` (`TauCeti.composeDiagram_capCup_reconnect`,
`TauCeti.middleLoopCount_capCup_reconnect`). To construct algebra maps out of the Brauer algebra by
recursion on the number of caps (`TauCeti/Algebra/BrauerAlgebra/Presentation.lean`), one must also
compare the reconnected diagrams obtained from different choices of cap and cup, and undo the stack
`capCup p q ∘ X` when `p` and `q` lie on through strands of `X`.

This file proves those reconnection identities:

* reconnecting two boundary points in a perfect matching transports it along a single transposition
  (`TauCeti.PerfectMatching.reconnect_eq_congr`), so stacking a permutation diagram on top commutes
  with reconnecting a top point to a bottom point
  (`TauCeti.BrauerDiagram.reconnect_composeDiagram_permToBrauer_left`);
* swapping the chosen endpoint of the top cup is the same as swapping the chosen endpoint of the
  bottom cap (`TauCeti.BrauerDiagram.reconnect_swap_top`), which in turn stacks the transposition of
  the cup on top (`TauCeti.BrauerDiagram.reconnect_swap_bottom`);
* reconnections at two distinct bottom points and two disjoint top cups commute
  (`TauCeti.BrauerDiagram.reconnect_reconnect_comm`), while exchanging which bottom point is paired
  with which cup stacks `Equiv.swap c c' * Equiv.swap d d'` on top
  (`TauCeti.BrauerDiagram.reconnect_reconnect_swap_caps`);
* stacking `capCup p q` above `X` at two through strands closes up no loop
  (`TauCeti.middleLoopCount_capCup_of_isThrough`), and reconnecting the resulting cap and cup gives
  back `X` (`TauCeti.BrauerDiagram.reconnect_composeDiagram_capCup`).

It also records the transposition form
`TauCeti.composeDiagram_capCup_capCup_eq_composeDiagram_permToBrauer_swap` of a stack of two cap-cup
diagrams sharing one strand.

## Main results

* `TauCeti.PerfectMatching.reconnect_eq_congr`: reconnecting `a` to `b` transports a matching along
  `Equiv.swap (D.val a) b`.
* `TauCeti.composeDiagram_capCup_capCup_eq_composeDiagram_permToBrauer_swap`: for `a ≠ c`,
  `capCup a c ∘ capCup a b = capCup a c ∘ permToBrauer (Equiv.swap b c)`.
* `TauCeti.BrauerDiagram.reconnect_composeDiagram_permToBrauer_left`: top permutations commute with
  reconnecting a top point to a bottom point.
* `TauCeti.composeDiagram_permToBrauer_swap_of_cup` and
  `TauCeti.composeDiagram_permToBrauer_swap_mul_swap_of_cups`: swapping the endpoints of a cup, or
  exchanging two disjoint cups, fixes a diagram.
* `TauCeti.BrauerDiagram.reconnect_swap_top` and `TauCeti.BrauerDiagram.reconnect_swap_bottom`:
  changing the chosen endpoint of the reconnected cup or cap.
* `TauCeti.BrauerDiagram.reconnect_reconnect_comm` and
  `TauCeti.BrauerDiagram.reconnect_reconnect_swap_caps`: commuting and exchanging two disjoint
  reconnections.
* `TauCeti.middleLoopCount_capCup_of_isThrough` and
  `TauCeti.BrauerDiagram.reconnect_composeDiagram_capCup`: stacking `capCup p q` on two through
  strands closes up no loop and is undone by reconnection.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

namespace TauCeti

namespace PerfectMatching

/-- **Reconnecting `a` to `b` transports a perfect matching along `Equiv.swap (D.val a) b`.** -/
theorem reconnect_eq_congr {α : Type*} [DecidableEq α] (D : PerfectMatching α) (a b : α) :
    D.reconnect a b = PerfectMatching.congr (Equiv.swap (D.val a) b) D :=
  Subtype.ext ((PerfectMatching.reconnect_val D a b).trans (PerfectMatching.congr_val _ D).symm)

end PerfectMatching

variable {k : ℕ}

/-! ### Stacking overlapping cap-cup diagrams and cup-fixing permutations -/

/-- **Two cap-cup diagrams sharing one strand compose to a cap-cup diagram above a transposition.**
For `a ≠ c`, stacking `capCup a c` above `capCup a b` equals stacking `capCup a c` above the
transposition `Equiv.swap b c`; the degenerate cases `a = b` and `b = c` are included. -/
theorem composeDiagram_capCup_capCup_eq_composeDiagram_permToBrauer_swap
    {a b c : Fin k} (hac : a ≠ c) :
    composeDiagram (capCup a c) (capCup a b) =
      composeDiagram (capCup a c) (permToBrauer (Equiv.swap b c)) := by
  rcases eq_or_ne a b with rfl | hab
  · rw [capCup_self, composeDiagram_permToBrauer_one_right, composeDiagram_capCup_permToBrauer_swap]
  rcases eq_or_ne b c with rfl | hbc
  · rw [Equiv.swap_self, ← Equiv.Perm.one_def, composeDiagram_permToBrauer_one_right,
      composeDiagram_capCup_capCup]
  have hperm : Equiv.swap c a * Equiv.swap a b = Equiv.swap b c * Equiv.swap c a :=
    Equiv.ext fun x => by
      simp only [Equiv.Perm.mul_apply]
      by_cases hxa : x = a
      · subst x
        rw [Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hbc hab.symm]
      by_cases hxb : x = b
      · subst x
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hbc hab.symm, Equiv.swap_apply_left]
      by_cases hxc : x = c
      · subst x
        rw [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne hab hac]
      rw [Equiv.swap_apply_of_ne_of_ne hxa hxb, Equiv.swap_apply_of_ne_of_ne hxc hxa,
        Equiv.swap_apply_of_ne_of_ne hxb hxc]
  rw [capCup_comm c a, composeDiagram_capCup_capCup_eq_relabel_right hac.symm b, hperm,
    ← mul_one (1 : Equiv.Perm (Fin k)),
    ← BrauerDiagram.relabel_relabel (capCup c a) (Equiv.swap c a) 1 (Equiv.swap b c) 1,
    BrauerDiagram.relabel_swap_one_capCup, composeDiagram_permToBrauer_right, Equiv.Perm.inv_def,
    Equiv.symm_swap]

/-- **Swapping the two endpoints of a top cup fixes the diagram.** -/
theorem composeDiagram_permToBrauer_swap_of_cup {D : BrauerDiagram k} {c d : Fin k}
    (hcup : D.val (Sum.inr c) = Sum.inr d) :
    composeDiagram (permToBrauer (Equiv.swap c d)) D = D := by
  have he : Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin k)) (Equiv.swap c d) =
      Equiv.swap (Sum.inr d) (Sum.inr c) :=
    Equiv.ext fun x => by
      rcases x with i | j
      · simp only [Equiv.Perm.sumCongr_apply, Sum.map_inl, Equiv.Perm.one_def, Equiv.refl_apply]
        exact (Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr Sum.inl_ne_inr).symm
      · simp only [Equiv.Perm.sumCongr_apply, Sum.map_inr]
        by_cases hjc : j = c
        · subst j; rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
        by_cases hjd : j = d
        · subst j; rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
        rw [Equiv.swap_apply_of_ne_of_ne hjc hjd,
          Equiv.swap_apply_of_ne_of_ne (by simpa using hjd) (by simpa using hjc)]
  rw [composeDiagram_permToBrauer_left, BrauerDiagram.relabel_def, he, ← hcup,
    ← PerfectMatching.reconnect_eq_congr]
  exact PerfectMatching.reconnect_self D (Sum.inr c)

/-- **Exchanging two disjoint top cups by `Equiv.swap c c' * Equiv.swap d d'` fixes the
diagram.** -/
theorem composeDiagram_permToBrauer_swap_mul_swap_of_cups {D : BrauerDiagram k}
    {c d c' d' : Fin k} (hcup : D.val (Sum.inr c) = Sum.inr d)
    (hcup' : D.val (Sum.inr c') = Sum.inr d') (hcc' : c' ≠ c) (hc'd : c' ≠ d) :
    composeDiagram (permToBrauer (Equiv.swap c c' * Equiv.swap d d')) D = D := by
  have hcd : c ≠ d := fun h => D.apply_ne (Sum.inr c) (by rw [hcup, h])
  have hc'd' : c' ≠ d' := fun h => D.apply_ne (Sum.inr c') (by rw [hcup', h])
  have hd'c : d' ≠ c := fun h => hc'd (Sum.inr.inj ((D.apply_eq_of_apply_eq hcup').symm.trans
    (h ▸ hcup)))
  have hdc : D.val (Sum.inr d) = Sum.inr c := D.apply_eq_of_apply_eq hcup
  have hd'c' : D.val (Sum.inr d') = Sum.inr c' := D.apply_eq_of_apply_eq hcup'
  set τ := Equiv.swap c c' * Equiv.swap d d'
  have hτc : τ c = c' := by simp [τ, Equiv.swap_apply_of_ne_of_ne hcd hd'c.symm]
  have hτc' : τ c' = c := by simp [τ, Equiv.swap_apply_of_ne_of_ne hc'd hc'd']
  have hτd : τ d = d' := by simp [τ, Equiv.swap_apply_of_ne_of_ne hd'c hc'd'.symm]
  have hτd' : τ d' = d := by simp [τ, Equiv.swap_apply_of_ne_of_ne hcd.symm hc'd.symm]
  have hτ_other : ∀ {j : Fin k}, j ≠ c → j ≠ d → j ≠ c' → j ≠ d' → τ j = j := by
    intro j hjc hjd hjc' hjd'
    simp [τ, Equiv.swap_apply_of_ne_of_ne, hjc, hjd, hjc', hjd']
  have hτ_symm : τ.symm = τ :=
    Equiv.ext fun j => by
      rw [Equiv.symm_apply_eq]
      rcases eq_or_ne j c with rfl | hjc
      · rw [hτc, hτc']
      rcases eq_or_ne j d with rfl | hjd
      · rw [hτd, hτd']
      rcases eq_or_ne j c' with rfl | hjc'
      · rw [hτc', hτc]
      rcases eq_or_ne j d' with rfl | hjd'
      · rw [hτd', hτd]
      · rw [hτ_other hjc hjd hjc' hjd', hτ_other hjc hjd hjc' hjd']
  rw [composeDiagram_permToBrauer_left]
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rcases x with i | j
  · rw [BrauerDiagram.relabel_val_inl, Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply]
    rcases hy : D.val (Sum.inl i) with i' | j'
    · rfl
    · obtain ⟨hyc, hyd⟩ := (D.apply_ne_and_ne_iff hcup (Sum.inl i)).mpr
        ⟨Sum.inl_ne_inr, Sum.inl_ne_inr⟩
      obtain ⟨hyc', hyd'⟩ := (D.apply_ne_and_ne_iff hcup' (Sum.inl i)).mpr
        ⟨Sum.inl_ne_inr, Sum.inl_ne_inr⟩
      rw [hy] at hyc hyd hyc' hyd'
      simp [hτ_other (by simpa using hyc) (by simpa using hyd)
        (by simpa using hyc') (by simpa using hyd')]
  · rw [BrauerDiagram.relabel_val_inr, hτ_symm]
    rcases eq_or_ne j c with rfl | hjc
    · simp [hτc, hcup', hcup, hτd']
    rcases eq_or_ne j d with rfl | hjd
    · simp [hτd, hd'c', hdc, hτc']
    rcases eq_or_ne j c' with rfl | hjc'
    · simp [hτc', hcup, hcup', hτd]
    rcases eq_or_ne j d' with rfl | hjd'
    · simp [hτd', hdc, hd'c', hτc]
    rw [hτ_other hjc hjd hjc' hjd']
    obtain ⟨hyc, hyd⟩ := (D.apply_ne_and_ne_iff hcup (Sum.inr j)).mpr
      ⟨by simpa using hjc, by simpa using hjd⟩
    obtain ⟨hyc', hyd'⟩ := (D.apply_ne_and_ne_iff hcup' (Sum.inr j)).mpr
      ⟨by simpa using hjc', by simpa using hjd'⟩
    rcases hy : D.val (Sum.inr j) with i' | j'
    · simp [Equiv.Perm.one_def]
    · rw [hy] at hyc hyd hyc' hyd'
      simp [hτ_other (by simpa using hyc) (by simpa using hyd) (by simpa using hyc')
        (by simpa using hyd')]

/-- **Stacking `capCup p q` above a diagram where `p` and `q` lie on through strands closes up no
loop.** -/
theorem middleLoopCount_capCup_of_isThrough {X : BrauerDiagram k} {p q : Fin k} (hpq : p ≠ q)
    (hp : X.IsThrough (Sum.inr p)) (hq : X.IsThrough (Sum.inr q)) :
    middleLoopCount (capCup p q) X = 0 := by
  refine middleLoopCount_eq_zero_iff.mpr fun m hm => ?_
  have hvert := (isMiddleVertex_def _ _ _).mp hm.isMiddleVertex
  rcases (BrauerDiagram.isCap_capCup_inl_iff hpq).mp hvert.1 with rfl | rfl
  · exact X.not_isThrough_of_isCup _ hvert.2 hp
  · exact X.not_isThrough_of_isCup _ hvert.2 hq

/-! ### Reconnecting caps and cups -/

namespace BrauerDiagram

/-- **Stacking a permutation diagram on top commutes with reconnecting a top point to a bottom
point.** -/
theorem reconnect_composeDiagram_permToBrauer_left (D : BrauerDiagram k)
    (σ : Equiv.Perm (Fin k)) (c a : Fin k) :
    (composeDiagram (permToBrauer σ) D).reconnect (Sum.inr (σ c)) (Sum.inl a) =
      composeDiagram (permToBrauer σ) (D.reconnect (Sum.inr c) (Sum.inl a)) := by
  rw [composeDiagram_permToBrauer_left, composeDiagram_permToBrauer_left,
    PerfectMatching.reconnect_eq_congr, relabel_val_inr, σ.symm_apply_apply,
    relabel_def, relabel_def, PerfectMatching.reconnect_eq_congr,
    PerfectMatching.congr_trans, PerfectMatching.congr_trans]
  refine congrArg (fun e => PerfectMatching.congr e D) (Equiv.ext fun x => ?_)
  simp only [Equiv.trans_apply]
  set φ : Equiv.Perm (Fin k ⊕ Fin k) := Equiv.Perm.sumCongr 1 σ
  change Equiv.swap (φ (D.val (Sum.inr c))) (φ (Sum.inl a)) (φ x) =
    φ (Equiv.swap (D.val (Sum.inr c)) (Sum.inl a) x)
  by_cases hxu : x = D.val (Sum.inr c)
  · subst x; simp
  by_cases hxv : x = Sum.inl a
  · subst x; simp
  rw [Equiv.swap_apply_of_ne_of_ne hxu hxv,
    Equiv.swap_apply_of_ne_of_ne (φ.injective.ne hxu) (φ.injective.ne hxv)]

/-- **Reconnecting the other endpoint of the top cup is the same as reconnecting the other endpoint
of the bottom cap.** -/
theorem reconnect_swap_top {D : BrauerDiagram k} {a b c d : Fin k}
    (hcap : D.val (Sum.inl a) = Sum.inl b) (hcup : D.val (Sum.inr c) = Sum.inr d) :
    D.reconnect (Sum.inr d) (Sum.inl a) = D.reconnect (Sum.inr c) (Sum.inl b) := by
  have hba : D.val (Sum.inl b) = Sum.inl a := D.apply_eq_of_apply_eq hcap
  have hdc : D.val (Sum.inr d) = Sum.inr c := D.apply_eq_of_apply_eq hcup
  set X₁ : BrauerDiagram k := D.reconnect (Sum.inr d) (Sum.inl a)
  set X₂ : BrauerDiagram k := D.reconnect (Sum.inr c) (Sum.inl b)
  have hX₁b : X₁.val (Sum.inl b) = Sum.inr c :=
    hcap ▸ hdc ▸ PerfectMatching.reconnect_val_val_right Sum.inl_ne_inr
  have hX₁c : X₁.val (Sum.inr c) = Sum.inl b :=
    hcap ▸ hdc ▸ PerfectMatching.reconnect_val_val_self Sum.inl_ne_inr
  have hX₂a : X₂.val (Sum.inl a) = Sum.inr d :=
    hba ▸ hcup ▸ PerfectMatching.reconnect_val_val_right Sum.inl_ne_inr
  have hX₂d : X₂.val (Sum.inr d) = Sum.inl a :=
    hba ▸ hcup ▸ PerfectMatching.reconnect_val_val_self Sum.inl_ne_inr
  refine Subtype.ext (Equiv.ext fun x => ?_)
  by_cases hxa : x = Sum.inl a
  · subst x; rw [PerfectMatching.reconnect_val_right Sum.inl_ne_inr, hX₂a]
  by_cases hxb : x = Sum.inl b
  · subst x; rw [hX₁b, PerfectMatching.reconnect_val_right Sum.inl_ne_inr]
  by_cases hxc : x = Sum.inr c
  · subst x; rw [hX₁c, PerfectMatching.reconnect_val_self Sum.inl_ne_inr]
  by_cases hxd : x = Sum.inr d
  · subst x; rw [PerfectMatching.reconnect_val_self Sum.inl_ne_inr, hX₂d]
  rw [PerfectMatching.reconnect_val_of_ne hxd hxa (hdc ▸ hxc) (hcap ▸ hxb),
    PerfectMatching.reconnect_val_of_ne hxc hxb (hcup ▸ hxd) (hba ▸ hxa)]

/-- **Reconnecting the other endpoint of the bottom cap swaps the two endpoints of the top cup.** -/
theorem reconnect_swap_bottom {D : BrauerDiagram k} {a b c d : Fin k}
    (hcap : D.val (Sum.inl a) = Sum.inl b) (hcup : D.val (Sum.inr c) = Sum.inr d) :
    D.reconnect (Sum.inr c) (Sum.inl b) =
      composeDiagram (permToBrauer (Equiv.swap c d)) (D.reconnect (Sum.inr c) (Sum.inl a)) := by
  conv_lhs => rw [← reconnect_swap_top hcap hcup, ← Equiv.swap_apply_left c d]
  rw [← reconnect_composeDiagram_permToBrauer_left, composeDiagram_permToBrauer_swap_of_cup hcup]

/-- **Reconnections at two distinct bottom points and two disjoint top cups commute.** -/
theorem reconnect_reconnect_comm {D : BrauerDiagram k} {a a' c d c' d' : Fin k}
    (hcup : D.val (Sum.inr c) = Sum.inr d) (hcup' : D.val (Sum.inr c') = Sum.inr d')
    (haa' : a' ≠ a) (hcc' : c' ≠ c) (hc'd : c' ≠ d) :
    (D.reconnect (Sum.inr c) (Sum.inl a)).reconnect (Sum.inr c') (Sum.inl a') =
      (D.reconnect (Sum.inr c') (Sum.inl a')).reconnect (Sum.inr c) (Sum.inl a) := by
  have hd'c : d' ≠ c := fun h => hc'd (Sum.inr.inj ((D.apply_eq_of_apply_eq hcup').symm.trans
    (h ▸ hcup)))
  have hd'd : d' ≠ d := fun h => hcc' (Sum.inr.inj (D.val.injective (hcup'.trans (h ▸ hcup.symm))))
  have h₁ : (D.reconnect (Sum.inr c) (Sum.inl a)).val (Sum.inr c') = Sum.inr d' :=
    PerfectMatching.reconnect_val_of_val_eq hcup' (by simpa using hcc') Sum.inr_ne_inl
      (by simpa using hd'c) Sum.inr_ne_inl
  have h₂ : (D.reconnect (Sum.inr c') (Sum.inl a')).val (Sum.inr c) = Sum.inr d :=
    PerfectMatching.reconnect_val_of_val_eq hcup (by simpa using hcc'.symm) Sum.inr_ne_inl
      (by simpa using hc'd.symm) Sum.inr_ne_inl
  rw [PerfectMatching.reconnect_eq_congr, h₁, PerfectMatching.reconnect_eq_congr, hcup,
    PerfectMatching.congr_trans, PerfectMatching.reconnect_eq_congr, h₂,
    PerfectMatching.reconnect_eq_congr, hcup', PerfectMatching.congr_trans]
  refine congrArg (fun e => PerfectMatching.congr e D) (Equiv.ext fun x => ?_)
  simp only [Equiv.trans_apply]
  by_cases hxd' : x = Sum.inr d'
  · subst x
    rw [Equiv.swap_apply_of_ne_of_ne (by simpa using hd'd) Sum.inr_ne_inl,
      Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (by simpa using haa')]
  by_cases hxa' : x = Sum.inl a'
  · subst x
    rw [Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (by simpa using haa'),
      Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (by simpa using hd'd) Sum.inr_ne_inl]
  by_cases hxd : x = Sum.inr d
  · subst x
    rw [Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (by simpa using haa'.symm),
      Equiv.swap_apply_of_ne_of_ne (by simpa using hd'd.symm) Sum.inr_ne_inl,
      Equiv.swap_apply_left]
  by_cases hxa : x = Sum.inl a
  · subst x
    rw [Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (by simpa using hd'd.symm) Sum.inr_ne_inl,
      Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (by simpa using haa'.symm),
      Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne hxd hxa, Equiv.swap_apply_of_ne_of_ne hxd' hxa',
    Equiv.swap_apply_of_ne_of_ne hxd hxa]

/-- **Exchanging the bottom points paired with two disjoint top cups renames those two top cups by
`Equiv.swap c c' * Equiv.swap d d'`.** -/
theorem reconnect_reconnect_swap_caps {D : BrauerDiagram k} {a a' c d c' d' : Fin k}
    (hcup : D.val (Sum.inr c) = Sum.inr d) (hcup' : D.val (Sum.inr c') = Sum.inr d')
    (haa' : a' ≠ a) (hcc' : c' ≠ c) (hc'd : c' ≠ d) :
    (D.reconnect (Sum.inr c) (Sum.inl a')).reconnect (Sum.inr c') (Sum.inl a) =
      composeDiagram (permToBrauer (Equiv.swap c c' * Equiv.swap d d'))
        ((D.reconnect (Sum.inr c) (Sum.inl a)).reconnect (Sum.inr c') (Sum.inl a')) := by
  have hcd : c ≠ d := fun h => D.apply_ne (Sum.inr c) (by rw [hcup, h])
  have hc'd' : c' ≠ d' := fun h => D.apply_ne (Sum.inr c') (by rw [hcup', h])
  have hd'c : d' ≠ c := fun h => hc'd (Sum.inr.inj ((D.apply_eq_of_apply_eq hcup').symm.trans
    (h ▸ hcup)))
  set τ := Equiv.swap c c' * Equiv.swap d d'
  have hτc : τ c = c' := by simp [τ, Equiv.swap_apply_of_ne_of_ne hcd hd'c.symm]
  have hτc' : τ c' = c := by simp [τ, Equiv.swap_apply_of_ne_of_ne hc'd hc'd']
  symm
  calc composeDiagram (permToBrauer τ)
        ((D.reconnect (Sum.inr c) (Sum.inl a)).reconnect (Sum.inr c') (Sum.inl a'))
      = ((composeDiagram (permToBrauer τ) D).reconnect (Sum.inr (τ c)) (Sum.inl a)).reconnect
          (Sum.inr (τ c')) (Sum.inl a') := by
        rw [← reconnect_composeDiagram_permToBrauer_left,
          ← reconnect_composeDiagram_permToBrauer_left]
    _ = (D.reconnect (Sum.inr c') (Sum.inl a)).reconnect (Sum.inr c) (Sum.inl a') := by
        rw [composeDiagram_permToBrauer_swap_mul_swap_of_cups hcup hcup' hcc' hc'd, hτc, hτc']
    _ = (D.reconnect (Sum.inr c) (Sum.inl a')).reconnect (Sum.inr c') (Sum.inl a) :=
        reconnect_reconnect_comm hcup' hcup haa' hcc'.symm hd'c.symm

/-- **Reconnecting the cap and cup created by stacking `capCup p q` on two through strands gives
back the original diagram**, converse to `TauCeti.composeDiagram_capCup_reconnect`. -/
theorem reconnect_composeDiagram_capCup {X : BrauerDiagram k} {p q a : Fin k}
    (hpq : p ≠ q) (hXp : X.val (Sum.inr p) = Sum.inl a) (hq : X.IsThrough (Sum.inr q)) :
    (composeDiagram (capCup p q) X).reconnect (Sum.inr p) (Sum.inl a) = X := by
  obtain ⟨b, hXq⟩ := Sum.isLeft_iff.mp (X.isLeft_val_inr hq)
  have hXa : X.val (Sum.inl a) = Sum.inr p := X.apply_eq_of_apply_eq hXp
  have hXb : X.val (Sum.inl b) = Sum.inr q := X.apply_eq_of_apply_eq hXq
  set D : BrauerDiagram k := composeDiagram (capCup p q) X
  have hDcap : D.val (Sum.inl a) = Sum.inl b :=
    composeDiagram_val_inl_eq_inl_of_cap_upper _ _ hXa (capCup_val_inl_left hpq) hXq
  have hDcup : D.val (Sum.inr p) = Sum.inr q :=
    composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hpq)
  set Y : BrauerDiagram k := D.reconnect (Sum.inr p) (Sum.inl a)
  have hYb : Y.val (Sum.inl b) = Sum.inr q :=
    hDcap ▸ hDcup ▸ PerfectMatching.reconnect_val_val_right Sum.inl_ne_inr
  have hYq : Y.val (Sum.inr q) = Sum.inl b :=
    hDcap ▸ hDcup ▸ PerfectMatching.reconnect_val_val_self Sum.inl_ne_inr
  refine Subtype.ext (Equiv.ext fun x => ?_)
  by_cases hxa : x = Sum.inl a
  · subst x; rw [PerfectMatching.reconnect_val_right Sum.inl_ne_inr, hXa]
  by_cases hxb : x = Sum.inl b
  · subst x; rw [hYb, hXb]
  by_cases hxp : x = Sum.inr p
  · subst x; rw [PerfectMatching.reconnect_val_self Sum.inl_ne_inr, hXp]
  by_cases hxq : x = Sum.inr q
  · subst x; rw [hYq, hXq]
  rw [PerfectMatching.reconnect_val_of_ne hxp hxa (hDcup ▸ hxq) (hDcap ▸ hxb)]
  have hyp : X.val x ≠ Sum.inr p := fun h => hxa ((X.apply_eq_of_apply_eq h).symm.trans hXp)
  have hyq : X.val x ≠ Sum.inr q := fun h => hxb ((X.apply_eq_of_apply_eq h).symm.trans hXq)
  rcases x with i | j <;> rcases hy : X.val _ with i' | j'
  · exact composeDiagram_val_inl_eq_inl_of_cap_lower _ _ hy
  · rw [hy] at hyp hyq
    exact composeDiagram_val_inl_eq_inr_of_through _ _ hy
      (capCup_val_inl_of_ne (by simpa using hyp) (by simpa using hyq))
  · exact composeDiagram_val_inr_eq_inl_of_through _ _
      (capCup_val_inr_of_ne (by simpa using hxp) (by simpa using hxq)) hy
  · rw [hy] at hyp hyq
    exact composeDiagram_val_inr_eq_inr_of_cup_lower _ _
      (capCup_val_inr_of_ne (by simpa using hxp) (by simpa using hxq)) hy
      (capCup_val_inl_of_ne (by simpa using hyp) (by simpa using hyq))

end BrauerDiagram

end TauCeti
