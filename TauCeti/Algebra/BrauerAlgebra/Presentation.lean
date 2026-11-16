/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerAlgebra.Basic

import TauCeti.Algebra.BrauerAlgebra.Generation
import TauCeti.Combinatorics.Brauer.Relations
import TauCeti.Combinatorics.Brauer.WeightedAssociativity

/-!
# Presentation of the Brauer algebra by permutations and cap-cup generators

`TauCeti/Algebra/BrauerAlgebra/Basic.lean` constructs maps out of the Brauer algebra `B_k(δ)` from
families of elements indexed by all `(2 * k - 1)‼` Brauer diagrams that obey the loop rule
(`TauCeti.BrauerAlgebra.lift`), and `TauCeti/Algebra/BrauerAlgebra/Generation.lean` shows that the
permutation diagrams and the cap-cup diagrams generate `B_k(δ)` as an `R`-algebra. When an action
of `B_k(δ)` carries signs — as the action on the tensor powers of a symplectic module does, where
crossings act by the sign-twisted permutation representation and horizontal arcs contract against an
alternating form — checking the loop rule directly on arbitrary stacked diagrams requires tracking
orientation signs across every closed loop and open strand, whereas the relations among the
permutation and cap-cup generators involve at most four strands at a time.

This file proves the universal property of `B_k(δ)` on those generators
(`TauCeti.BrauerAlgebra.liftOfPermCapCup`). Given an `R`-algebra `A`, a monoid homomorphism
`s : Equiv.Perm (Fin k) →* A` for the permutation diagrams, and elements `e a b : A` for the
cap-cup diagrams `TauCeti.capCup a b` at distinct indices `a ≠ b`, there is a unique `R`-algebra
homomorphism `B_k(δ) →ₐ[R] A` sending `of (permToBrauer σ)` to `s σ` and `of (capCup a b)` (for
`a ≠ b`) to `e a b` provided:

* `e a b = e b a`: a cap-cup generator depends only on the unordered pair;
* `e a b * e a b = δ • e a b` for `a ≠ b`: the loop rule on a repeated arc;
* `Commute (e a b) (e c d)` when `{a, b}` and `{c, d}` are disjoint: disjoint arcs commute;
* `s σ * e a b = e (σ a) (σ b) * s σ` for `a ≠ b`: permutations rename arcs;
* `s (Equiv.swap a b) * e a b = e a b` for `a ≠ b`: the transposition of an arc is absorbed;
* `e a c * e a b = e a c * s (Equiv.swap b c)` for pairwise distinct `a, b, c`: two arcs sharing a
  strand compose to an arc after a transposition.

It also records the remaining generator relations in `B_k(δ)` itself (`of_capCup_comm`,
`commute_of_capCup_of_disjoint`, `of_permToBrauer_mul_of_capCup`,
`of_capCup_mul_of_capCup_of_ne`, and `of_capCup_mul_of_capCup_mul_of_capCup`), complementing those
already in `TauCeti/Algebra/BrauerAlgebra/Basic.lean`, so that `B_k(δ)` visibly satisfies all six
hypotheses.

## Proof outline

Every Brauer diagram `D` with at least one cap is obtained by stacking a cap-cup diagram
`capCup c d` above the reconnected diagram `D.reconnect (Sum.inr c) (Sum.inl a)` with one cap fewer,
closing no middle loop (`TauCeti.composeDiagram_capCup_reconnect`,
`TauCeti.middleLoopCount_capCup_reconnect`). Evaluating a diagram recursively along one chosen
reconnection defines a candidate map `evalDiagram : BrauerDiagram k → A`. Strong induction on
`D.bottomCap.card` proves simultaneously that `evalDiagram D` is independent of which cap `(a, b)`
and cup `(c, d)` are reconnected, and that left multiplication by `s σ` renames the top boundary by
`σ`. From these two properties the loop rule
`e p q * evalDiagram X = δ ^ middleLoopCount (capCup p q) X • evalDiagram (capCup p q ∘ X)` follows
by splitting into cases according to whether `p` and `q` lie on through strands or cups of `X`, and
`TauCeti.BrauerDiagram.capCup_induction_on` then gives the full loop rule on all pairs of diagrams,
feeding `TauCeti.BrauerAlgebra.lift`.

## Implementation notes

In `BrauerDiagram k`, the degenerate diagram `capCup a a` is the identity diagram `permToBrauer 1`
(`TauCeti.capCup_self`), whereas in concrete tensor-power actions the formula defining `e a b` at
`a = b` need not evaluate to `1` (for both `TauCeti.orthogonalCupCapAt` and
`TauCeti.symplecticCupCapAt` it is a degenerate rank-one operator). Accordingly,
`TauCeti.BrauerAlgebra.liftOfPermCapCup` neither reads `e a a` nor asks for any relation at
coincident strands.

## Main definitions

* `TauCeti.BrauerAlgebra.liftOfPermCapCup`: the `R`-algebra map `BrauerAlgebra R δ k →ₐ[R] A`
  extending a monoid homomorphism on `Equiv.Perm (Fin k)` and cap-cup elements satisfying the six
  Brauer relations.

## Main results

* `TauCeti.BrauerAlgebra.of_capCup_comm`,
  `TauCeti.BrauerAlgebra.commute_of_capCup_of_disjoint`,
  `TauCeti.BrauerAlgebra.of_permToBrauer_mul_of_capCup`,
  `TauCeti.BrauerAlgebra.of_capCup_mul_of_capCup_of_ne`,
  `TauCeti.BrauerAlgebra.of_capCup_mul_of_capCup_mul_of_capCup`: the remaining Brauer relations on
  the generators of `BrauerAlgebra R δ k`.
* `TauCeti.BrauerAlgebra.liftOfPermCapCup_of_permToBrauer`,
  `TauCeti.BrauerAlgebra.liftOfPermCapCup_comp_ofPerm`, and
  `TauCeti.BrauerAlgebra.liftOfPermCapCup_of_capCup`: the values of the lifted algebra map on
  permutation diagrams, on the group algebra of `Sₖ`, and on cap-cup diagrams at distinct strands.
* `TauCeti.BrauerAlgebra.algHom_ext_of_permToBrauer_of_capCup` and
  `TauCeti.BrauerAlgebra.eq_liftOfPermCapCup`: uniqueness of the lifted algebra map for every
  strand count `k : ℕ`.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

namespace TauCeti

/-! ### Diagram identities for reconnection and overlapping pairs -/

section DiagramLemmas

variable {k : ℕ}

/-- Reconnecting `a` to `b` is transporting along `Equiv.swap (D.val a) b`. -/
private theorem reconnect_eq_congr {α : Type*} [DecidableEq α] (D : PerfectMatching α) (a b : α) :
    D.reconnect a b = PerfectMatching.congr (Equiv.swap (D.val a) b) D :=
  Subtype.ext ((PerfectMatching.reconnect_val D a b).trans (PerfectMatching.congr_val _ D).symm)

/-- Two cap-cup diagrams sharing one point compose to a cap-cup diagram above a transposition. -/
private theorem composeDiagram_capCup_capCup_eq_composeDiagram_permToBrauer_swap
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

/-- Stacking a permutation diagram on top commutes with reconnecting a top point to a bottom
point. -/
private theorem reconnect_composeDiagram_permToBrauer_left (D : BrauerDiagram k)
    (σ : Equiv.Perm (Fin k)) (c a : Fin k) :
    (composeDiagram (permToBrauer σ) D).reconnect (Sum.inr (σ c)) (Sum.inl a) =
      composeDiagram (permToBrauer σ) (D.reconnect (Sum.inr c) (Sum.inl a)) := by
  rw [composeDiagram_permToBrauer_left, composeDiagram_permToBrauer_left,
    reconnect_eq_congr, BrauerDiagram.relabel_val_inr, σ.symm_apply_apply,
    BrauerDiagram.relabel_def, BrauerDiagram.relabel_def, reconnect_eq_congr,
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

/-- Swapping the two endpoints of a top cup fixes the diagram. -/
private theorem composeDiagram_permToBrauer_swap_of_cup {D : BrauerDiagram k} {c d : Fin k}
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
    ← reconnect_eq_congr]
  exact PerfectMatching.reconnect_self D (Sum.inr c)

/-- Reconnecting the other endpoint of the top cup is the same as reconnecting the other endpoint
of the bottom cap. -/
private theorem reconnect_swap_top {D : BrauerDiagram k} {a b c d : Fin k}
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

/-- Reconnecting the other endpoint of the bottom cap swaps the two endpoints of the top cup. -/
private theorem reconnect_swap_bottom {D : BrauerDiagram k} {a b c d : Fin k}
    (hcap : D.val (Sum.inl a) = Sum.inl b) (hcup : D.val (Sum.inr c) = Sum.inr d) :
    D.reconnect (Sum.inr c) (Sum.inl b) =
      composeDiagram (permToBrauer (Equiv.swap c d)) (D.reconnect (Sum.inr c) (Sum.inl a)) := by
  conv_lhs => rw [← reconnect_swap_top hcap hcup, ← Equiv.swap_apply_left c d]
  rw [← reconnect_composeDiagram_permToBrauer_left, composeDiagram_permToBrauer_swap_of_cup hcup]

/-- Reconnections on disjoint caps and disjoint cups commute. -/
private theorem reconnect_reconnect_comm {D : BrauerDiagram k}
    {a b a' b' c d c' d' : Fin k}
    (_hcap : D.val (Sum.inl a) = Sum.inl b) (_hcap' : D.val (Sum.inl a') = Sum.inl b')
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
  rw [reconnect_eq_congr, h₁, reconnect_eq_congr, hcup, PerfectMatching.congr_trans,
    reconnect_eq_congr, h₂, reconnect_eq_congr, hcup', PerfectMatching.congr_trans]
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

/-- Exchanging two disjoint top cups by `swap c c' * swap d d'` fixes the diagram. -/
private theorem composeDiagram_permToBrauer_swap_mul_swap_of_cups {D : BrauerDiagram k}
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

/-- Exchanging the bottom caps paired with two disjoint top cups renames those two top cups by
`swap c c' * swap d d'`. -/
private theorem reconnect_reconnect_swap_caps {D : BrauerDiagram k}
    {a b a' b' c d c' d' : Fin k}
    (hcap : D.val (Sum.inl a) = Sum.inl b) (hcap' : D.val (Sum.inl a') = Sum.inl b')
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
        reconnect_reconnect_comm hcap hcap' hcup' hcup haa' hcc'.symm hd'c.symm

/-- Stacking `capCup p q` above a diagram where `p` and `q` lie on through strands closes no loop,
and reconnecting the resulting cap and cup recovers the original diagram. -/
private theorem reconnect_composeDiagram_capCup_of_isThrough {X : BrauerDiagram k} {p q a b : Fin k}
    (hpq : p ≠ q) (hXp : X.val (Sum.inr p) = Sum.inl a) (hXq : X.val (Sum.inr q) = Sum.inl b) :
    middleLoopCount (capCup p q) X = 0 ∧
      (composeDiagram (capCup p q) X).val (Sum.inl a) = Sum.inl b ∧
      (composeDiagram (capCup p q) X).val (Sum.inr p) = Sum.inr q ∧
      (composeDiagram (capCup p q) X).reconnect (Sum.inr p) (Sum.inl a) = X := by
  have hXa : X.val (Sum.inl a) = Sum.inr p := X.apply_eq_of_apply_eq hXp
  have hXb : X.val (Sum.inl b) = Sum.inr q := X.apply_eq_of_apply_eq hXq
  have hloop : middleLoopCount (capCup p q) X = 0 := by
    refine middleLoopCount_eq_zero_iff.mpr fun m hm => ?_
    have hvert := (isMiddleVertex_def _ _ _).mp hm.isMiddleVertex
    rcases (BrauerDiagram.isCap_capCup_inl_iff hpq).mp hvert.1 with rfl | rfl
    · exact X.not_isThrough_of_isCup _ hvert.2 (by simp [BrauerDiagram.isThrough_def, hXp])
    · exact X.not_isThrough_of_isCup _ hvert.2 (by simp [BrauerDiagram.isThrough_def, hXq])
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
  refine ⟨hloop, hDcap, hDcup, Subtype.ext (Equiv.ext fun x => ?_)⟩
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

end DiagramLemmas

namespace BrauerAlgebra

/-! ### The remaining Brauer relations in `BrauerAlgebra` -/

section Relations

variable {R : Type*} [CommSemiring R] {δ : R} {k : ℕ}

/-- **A cap-cup element depends only on its unordered pair.** -/
theorem of_capCup_comm (a b : Fin k) :
    (of (capCup b a) : BrauerAlgebra R δ k) = of (capCup a b) := by
  rw [capCup_comm]

/-- **Cap-cup elements on disjoint pairs commute.** -/
theorem commute_of_capCup_of_disjoint {a b c d : Fin k}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Commute (of (capCup a b) : BrauerAlgebra R δ k) (of (capCup c d)) := by
  rw [Commute, SemiconjBy,
    of_mul_of_of_middleLoopCount_eq_zero
      (middleLoopCount_capCup_capCup_of_disjoint hac had hbc hbd),
    of_mul_of_of_middleLoopCount_eq_zero
      (middleLoopCount_capCup_capCup_of_disjoint hac.symm hbc.symm had.symm hbd.symm),
    composeDiagram_capCup_capCup_comm hac had hbc hbd]

/-- **Permutations rename cap-cup elements**: `σ * e_{a,b} = e_{σ a, σ b} * σ`. -/
theorem of_permToBrauer_mul_of_capCup (σ : Equiv.Perm (Fin k)) (a b : Fin k) :
    (of (permToBrauer σ) * of (capCup a b) : BrauerAlgebra R δ k) =
      of (capCup (σ a) (σ b)) * of (permToBrauer σ) := by
  rw [of_mul_of_of_middleLoopCount_eq_zero (middleLoopCount_permToBrauer_left _ _),
    of_mul_of_of_middleLoopCount_eq_zero (middleLoopCount_permToBrauer_right _ _),
    composeDiagram_permToBrauer_capCup]

/-- **Two cap-cup elements sharing one strand compose to a cap-cup element times a
transposition**: for `b ≠ c` and `a ≠ c`, `e_{a,c} * e_{a,b} = e_{a,c} * s_{b,c}`. -/
theorem of_capCup_mul_of_capCup_of_ne {a b c : Fin k} (hbc : b ≠ c) (hac : a ≠ c) :
    (of (capCup a c) * of (capCup a b) : BrauerAlgebra R δ k) =
      of (capCup a c) * of (permToBrauer (Equiv.swap b c)) := by
  have hloop : middleLoopCount (capCup a c) (capCup a b) = 0 := by
    rw [capCup_comm c a]
    exact middleLoopCount_capCup_capCup_right_of_ne hbc.symm a
  rw [of_mul_of_of_middleLoopCount_eq_zero hloop,
    of_mul_of_of_middleLoopCount_eq_zero (middleLoopCount_permToBrauer_right _ _),
    composeDiagram_capCup_capCup_eq_composeDiagram_permToBrauer_swap hac]

/-- **Overlapping cap-cup elements absorb**: for pairwise distinct `a, b, c`,
`e_{a,b} * e_{b,c} * e_{a,b} = e_{a,b}`. -/
theorem of_capCup_mul_of_capCup_mul_of_capCup {a b c : Fin k}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (of (capCup a b) * of (capCup b c) * of (capCup a b) : BrauerAlgebra R δ k) =
      of (capCup a b) := by
  rw [mul_assoc,
    of_mul_of_of_middleLoopCount_eq_zero (middleLoopCount_capCup_capCup_left_of_ne hac b),
    of_mul_of_of_middleLoopCount_eq_zero
      (middleLoopCount_capCup_composeDiagram_capCup_capCup hbc.symm hac.symm),
    composeDiagram_capCup_capCup_capCup hab]

end Relations

/-! ### Extending generators satisfying the Brauer relations to `BrauerAlgebra` -/

section LiftOfPermCapCup

variable {R : Type*} [CommSemiring R] {δ : R} {k : ℕ}
variable {A : Type*} [Semiring A] [Algebra R A]

/-- Recursive evaluation of a Brauer diagram in `A`: peel off the least capped bottom point and
the least cupped top point by reconnecting them, until a permutation diagram is reached. -/
private noncomputable def evalDiagram (s : Equiv.Perm (Fin k) →* A) (e : Fin k → Fin k → A)
    (D : BrauerDiagram k) : A :=
  if h : D.bottomCap.Nonempty then
    let a := D.bottomCap.min' h
    have htop : D.topCup.Nonempty := by
      rw [← Finset.card_pos, ← D.card_bottomCap_eq_card_topCup]
      exact Finset.card_pos.mpr h
    let c := D.topCup.min' htop
    let d := (D.cupMatching.val ⟨c, (D.mem_topCup).mp (Finset.min'_mem _ htop)⟩).1
    e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a))
  else
    s (D.throughPerm (D.forall_isThrough_iff_bottomCap_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp h)))
termination_by D.bottomCap.card
decreasing_by
  have ha : D.IsCap (Sum.inl (D.bottomCap.min' h)) :=
    (D.mem_bottomCap).mp (Finset.min'_mem _ h)
  obtain ⟨b, hcap⟩ := Sum.isLeft_iff.mp ((D.isCap_def _).mp ha).2
  have hc : D.IsCup (Sum.inr (D.topCup.min' htop)) :=
    (D.mem_topCup).mp (Finset.min'_mem _ htop)
  have hcup : D.val (Sum.inr (D.topCup.min' htop)) =
      Sum.inr (D.cupMatching.val ⟨D.topCup.min' htop, hc⟩).1 :=
    (D.inr_cupMatching ⟨_, hc⟩).symm
  rw [← D.card_bottomCap_reconnect hcap hcup]
  omega

private theorem evalDiagram_permToBrauer (s : Equiv.Perm (Fin k) →* A) (e : Fin k → Fin k → A)
    (σ : Equiv.Perm (Fin k)) : evalDiagram s e (permToBrauer σ) = s σ := by
  have hempty : (permToBrauer σ).bottomCap = ∅ :=
    (BrauerDiagram.exists_eq_permToBrauer_iff_bottomCap_eq_empty (D := permToBrauer σ)).mp ⟨σ, rfl⟩
  have hne : ¬(permToBrauer σ).bottomCap.Nonempty := by simp [hempty]
  rw [evalDiagram.eq_1]
  split_ifs
  exact congrArg s (BrauerDiagram.throughPerm_permToBrauer σ)

private theorem exists_evalDiagram_eq_of_nonempty (s : Equiv.Perm (Fin k) →* A)
    (e : Fin k → Fin k → A) {D : BrauerDiagram k} (h : D.bottomCap.Nonempty) :
    ∃ a b c d : Fin k, D.val (Sum.inl a) = Sum.inl b ∧ D.val (Sum.inr c) = Sum.inr d ∧
      evalDiagram s e D = e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a)) := by
  have htop : D.topCup.Nonempty := by
    rw [← Finset.card_pos, ← D.card_bottomCap_eq_card_topCup]
    exact Finset.card_pos.mpr h
  set a := D.bottomCap.min' h
  set c := D.topCup.min' htop
  have ha : D.IsCap (Sum.inl a) := (D.mem_bottomCap).mp (Finset.min'_mem _ h)
  obtain ⟨b, hcap⟩ := Sum.isLeft_iff.mp ((D.isCap_def _).mp ha).2
  have hc : D.IsCup (Sum.inr c) := (D.mem_topCup).mp (Finset.min'_mem _ htop)
  set d := (D.cupMatching.val ⟨c, hc⟩).1
  have hcup : D.val (Sum.inr c) = Sum.inr d := (D.inr_cupMatching ⟨c, hc⟩).symm
  refine ⟨a, b, c, d, hcap, hcup, ?_⟩
  conv_lhs => rw [evalDiagram.eq_1]
  split_ifs
  rfl

section InductionSteps

variable {s : Equiv.Perm (Fin k) →* A} {e : Fin k → Fin k → A}

/-- Right absorption `e a b * s (swap a b) = e a b` from left absorption, renaming, and symmetry. -/
private theorem mul_swap_eq_self_of_relations
    (he_comm : ∀ a b : Fin k, e a b = e b a)
    (hs_conj : ∀ (σ : Equiv.Perm (Fin k)) {a b : Fin k}, a ≠ b → s σ * e a b = e (σ a) (σ b) * s σ)
    (hs_swap : ∀ {a b : Fin k}, a ≠ b → s (Equiv.swap a b) * e a b = e a b)
    {a b : Fin k} (hab : a ≠ b) :
    e a b * s (Equiv.swap a b) = e a b := by
  have h := hs_conj (Equiv.swap a b) hab
  rw [hs_swap hab, Equiv.swap_apply_left, Equiv.swap_apply_right, he_comm b a] at h
  exact h.symm

/-- Two disjoint arcs absorb the simultaneous swap `swap a c * swap b d` of their endpoints. -/
private theorem disj_mul_swap_mul_swap_eq_of_relations
    (he_comm : ∀ a b : Fin k, e a b = e b a)
    (he_disj : ∀ {a b c d : Fin k}, a ≠ c → a ≠ d → b ≠ c → b ≠ d → Commute (e a b) (e c d))
    (he_overlap : ∀ {a b c : Fin k}, a ≠ b → b ≠ c → a ≠ c →
      e a c * e a b = e a c * s (Equiv.swap b c))
    {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    e a b * (e c d * s (Equiv.swap a c * Equiv.swap b d)) = e a b * e c d := by
  have h₁ : e a b * e c d * e b c = e a b * e c d * s (Equiv.swap a c) := by
    calc e a b * e c d * e b c
        = e c d * (e b a * e b c) := by
          rw [(he_disj hac had hbc hbd).eq, mul_assoc, he_comm a b]
      _ = e c d * (e b a * s (Equiv.swap c a)) := by
          rw [he_overlap hbc hac.symm hab.symm]
      _ = e a b * e c d * s (Equiv.swap a c) := by
          rw [he_comm b a, ← mul_assoc, (he_disj hac had hbc hbd).symm.eq, Equiv.swap_comm c a]
  have h₂ : e a b * e c d * e b c = e a b * e c d * s (Equiv.swap b d) := by
    rw [mul_assoc, he_comm b c, he_overlap hbc.symm hbd hcd, ← mul_assoc]
  have h₃ := congrArg (· * s (Equiv.swap b d)) (h₁.symm.trans h₂)
  simpa only [mul_assoc, ← s.map_mul, Equiv.swap_mul_self, map_one, mul_one] using h₃

/-- Changing the reconnected bottom cap of `D` while keeping the top cup fixed leaves
`e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a))` unchanged, given the inductive
hypotheses on diagrams with strictly fewer caps. -/
private theorem evalDiagram_move_cap
    (he_comm : ∀ a b : Fin k, e a b = e b a)
    (he_disj : ∀ {a b c d : Fin k}, a ≠ c → a ≠ d → b ≠ c → b ≠ d → Commute (e a b) (e c d))
    (hs_conj : ∀ (σ : Equiv.Perm (Fin k)) {a b : Fin k}, a ≠ b → s σ * e a b = e (σ a) (σ b) * s σ)
    (hs_swap : ∀ {a b : Fin k}, a ≠ b → s (Equiv.swap a b) * e a b = e a b)
    (he_overlap : ∀ {a b c : Fin k}, a ≠ b → b ≠ c → a ≠ c →
      e a c * e a b = e a c * s (Equiv.swap b c))
    {D : BrauerDiagram k}
    (ih_rec : ∀ E : BrauerDiagram k, E.bottomCap.card < D.bottomCap.card →
      ∀ {a b c d : Fin k}, E.val (Sum.inl a) = Sum.inl b → E.val (Sum.inr c) = Sum.inr d →
      evalDiagram s e E = e c d * evalDiagram s e (E.reconnect (Sum.inr c) (Sum.inl a)))
    (ih_perm : ∀ E : BrauerDiagram k, E.bottomCap.card < D.bottomCap.card →
      ∀ σ : Equiv.Perm (Fin k),
      s σ * evalDiagram s e E = evalDiagram s e (composeDiagram (permToBrauer σ) E))
    {a b a' b' c d : Fin k}
    (hcap : D.val (Sum.inl a) = Sum.inl b) (hcap' : D.val (Sum.inl a') = Sum.inl b')
    (hcup : D.val (Sum.inr c) = Sum.inr d) :
    e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a)) =
      e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a')) := by
  have hcd : c ≠ d := fun h => D.apply_ne (Sum.inr c) (by rw [hcup, h])
  rcases eq_or_ne a' a with rfl | ha'a
  · rfl
  rcases eq_or_ne a' b with rfl | ha'b
  · have hcard := D.card_bottomCap_reconnect hcap hcup
    rw [reconnect_swap_bottom hcap hcup, ← ih_perm _ (by omega) (Equiv.swap c d), ← mul_assoc,
      mul_swap_eq_self_of_relations he_comm hs_conj hs_swap hcd]
  have hab : b ≠ a := fun h => D.apply_ne (Sum.inl a) (by rw [hcap, h])
  have ha_mem : a ∈ D.bottomCap := by simp [BrauerDiagram.isCap_def, hcap]
  have hb_mem : b ∈ D.bottomCap.erase a := by
    simp [hab, BrauerDiagram.isCap_def, D.apply_eq_of_apply_eq hcap]
  have ha'_mem : a' ∈ (D.bottomCap.erase a).erase b := by
    simp [ha'a, ha'b, BrauerDiagram.isCap_def, hcap']
  have hc_mem : c ∈ D.topCup := by simp [BrauerDiagram.isCup_def, hcup]
  have hd_mem : d ∈ D.topCup.erase c := by
    simp [hcd.symm, BrauerDiagram.isCup_def, D.apply_eq_of_apply_eq hcup]
  have hcup_pos : ((D.topCup.erase c).erase d).Nonempty := by
    rw [← Finset.card_pos]
    have h₁ : 0 < ((D.bottomCap.erase a).erase b).card := Finset.card_pos.mpr ⟨a', ha'_mem⟩
    rw [Finset.card_erase_of_mem hb_mem, Finset.card_erase_of_mem ha_mem,
      D.card_bottomCap_eq_card_topCup] at h₁
    rwa [Finset.card_erase_of_mem hd_mem, Finset.card_erase_of_mem hc_mem]
  obtain ⟨c', hc'_mem⟩ := hcup_pos
  have hc'd : c' ≠ d := (Finset.mem_erase.mp hc'_mem).1
  have hc'c : c' ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hc'_mem).2).1
  obtain ⟨d', hcup'⟩ := Sum.isRight_iff.mp ((D.isCup_def _).mp
    ((D.mem_topCup).mp (Finset.mem_erase.mp (Finset.mem_erase.mp hc'_mem).2).2)).2
  have hc'd' : c' ≠ d' := fun h => D.apply_ne (Sum.inr c') (by rw [hcup', h])
  have hd'c : d' ≠ c := fun h => hc'd (Sum.inr.inj
    ((D.apply_eq_of_apply_eq hcup').symm.trans (h ▸ hcup)))
  have hd'd : d' ≠ d := fun h => hc'c (Sum.inr.inj
    (D.val.injective (hcup'.trans (h ▸ hcup.symm))))
  have hb'a : b' ≠ a := fun h => ha'b (Sum.inl.inj
    ((D.apply_eq_of_apply_eq hcap').symm.trans (h ▸ hcap)))
  set X₁ : BrauerDiagram k := D.reconnect (Sum.inr c) (Sum.inl a)
  set X₂ : BrauerDiagram k := D.reconnect (Sum.inr c) (Sum.inl a')
  have hX₁_card : X₁.bottomCap.card + 2 = D.bottomCap.card := D.card_bottomCap_reconnect hcap hcup
  have hX₂_card : X₂.bottomCap.card + 2 = D.bottomCap.card := D.card_bottomCap_reconnect hcap' hcup
  have hX₁_cap' : X₁.val (Sum.inl a') = Sum.inl b' :=
    PerfectMatching.reconnect_val_of_val_eq hcap' Sum.inl_ne_inr (by simpa using ha'a)
      Sum.inl_ne_inr (by simpa using hb'a)
  have hX₁_cup' : X₁.val (Sum.inr c') = Sum.inr d' :=
    PerfectMatching.reconnect_val_of_val_eq hcup' (by simpa using hc'c) Sum.inr_ne_inl
      (by simpa using hd'c) Sum.inr_ne_inl
  have hX₂_cap : X₂.val (Sum.inl a) = Sum.inl b :=
    PerfectMatching.reconnect_val_of_val_eq hcap Sum.inl_ne_inr (by simpa using ha'a.symm)
      Sum.inl_ne_inr (by simpa using ha'b.symm)
  have hX₂_cup' : X₂.val (Sum.inr c') = Sum.inr d' :=
    PerfectMatching.reconnect_val_of_val_eq hcup' (by simpa using hc'c) Sum.inr_ne_inl
      (by simpa using hd'c) Sum.inr_ne_inl
  set Z₁ : BrauerDiagram k := X₁.reconnect (Sum.inr c') (Sum.inl a')
  have hZ₁_card : Z₁.bottomCap.card + 2 = X₁.bottomCap.card :=
    X₁.card_bottomCap_reconnect hX₁_cap' hX₁_cup'
  have hswap_caps : X₂.reconnect (Sum.inr c') (Sum.inl a) =
      composeDiagram (permToBrauer (Equiv.swap c c' * Equiv.swap d d')) Z₁ :=
    reconnect_reconnect_swap_caps hcap hcap' hcup hcup' ha'a hc'c hc'd
  symm
  calc e c d * evalDiagram s e X₂
      = e c d * (e c' d' * (s (Equiv.swap c c' * Equiv.swap d d') * evalDiagram s e Z₁)) := by
        rw [ih_rec X₂ (by omega) hX₂_cap hX₂_cup', hswap_caps,
          ← ih_perm Z₁ (by omega) (Equiv.swap c c' * Equiv.swap d d')]
    _ = (e c d * (e c' d' * s (Equiv.swap c c' * Equiv.swap d d'))) * evalDiagram s e Z₁ := by
        rw [← mul_assoc (e c' d'), ← mul_assoc (e c d)]
    _ = e c d * evalDiagram s e X₁ := by
        rw [disj_mul_swap_mul_swap_eq_of_relations he_comm he_disj he_overlap
          hcd hc'd' hc'c.symm hd'c.symm hc'd.symm hd'd.symm, mul_assoc,
          ← ih_rec X₁ (by omega) hX₁_cap' hX₁_cup']

/-- Changing the reconnected top cup of `D` while keeping the bottom cap fixed leaves
`e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a))` unchanged. -/
private theorem evalDiagram_move_cup
    (he_comm : ∀ a b : Fin k, e a b = e b a)
    (he_disj : ∀ {a b c d : Fin k}, a ≠ c → a ≠ d → b ≠ c → b ≠ d → Commute (e a b) (e c d))
    {D : BrauerDiagram k}
    (hmove_cap : ∀ {a b a' b' c d : Fin k},
      D.val (Sum.inl a) = Sum.inl b → D.val (Sum.inl a') = Sum.inl b' →
      D.val (Sum.inr c) = Sum.inr d →
      e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a)) =
        e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a')))
    (ih_rec : ∀ E : BrauerDiagram k, E.bottomCap.card < D.bottomCap.card →
      ∀ {a b c d : Fin k}, E.val (Sum.inl a) = Sum.inl b → E.val (Sum.inr c) = Sum.inr d →
      evalDiagram s e E = e c d * evalDiagram s e (E.reconnect (Sum.inr c) (Sum.inl a)))
    {a b c d c' d' : Fin k}
    (hcap : D.val (Sum.inl a) = Sum.inl b)
    (hcup : D.val (Sum.inr c) = Sum.inr d) (hcup' : D.val (Sum.inr c') = Sum.inr d') :
    e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a)) =
      e c' d' * evalDiagram s e (D.reconnect (Sum.inr c') (Sum.inl a)) := by
  by_cases hc'c : c' = c
  · subst c'
    have hd' : d' = d := Sum.inr.inj (hcup'.symm.trans hcup)
    subst d'
    rfl
  by_cases hc'd : c' = d
  · subst c'
    have hd' : d' = c := Sum.inr.inj (hcup'.symm.trans (D.apply_eq_of_apply_eq hcup))
    subst d'
    rw [he_comm d c, reconnect_swap_top hcap hcup,
      hmove_cap hcap (D.apply_eq_of_apply_eq hcap) hcup]
  have hab : b ≠ a := fun h => D.apply_ne (Sum.inl a) (by rw [hcap, h])
  have hcd : d ≠ c := fun h => D.apply_ne (Sum.inr c) (by rw [hcup, h])
  have ha_mem : a ∈ D.bottomCap := by simp [BrauerDiagram.isCap_def, hcap]
  have hb_mem : b ∈ D.bottomCap.erase a := by
    simp [hab, BrauerDiagram.isCap_def, D.apply_eq_of_apply_eq hcap]
  have hc_mem : c ∈ D.topCup := by simp [BrauerDiagram.isCup_def, hcup]
  have hd_mem : d ∈ D.topCup.erase c := by
    simp [hcd, BrauerDiagram.isCup_def, D.apply_eq_of_apply_eq hcup]
  have hc'_mem : c' ∈ (D.topCup.erase c).erase d := by
    simp [hc'c, hc'd, BrauerDiagram.isCup_def, hcup']
  have hcap_pos : ((D.bottomCap.erase a).erase b).Nonempty := by
    rw [← Finset.card_pos]
    have h₁ : 0 < ((D.topCup.erase c).erase d).card := Finset.card_pos.mpr ⟨c', hc'_mem⟩
    rw [Finset.card_erase_of_mem hd_mem, Finset.card_erase_of_mem hc_mem,
      ← D.card_bottomCap_eq_card_topCup] at h₁
    rwa [Finset.card_erase_of_mem hb_mem, Finset.card_erase_of_mem ha_mem]
  obtain ⟨a', ha'_mem⟩ := hcap_pos
  have ha'b : a' ≠ b := (Finset.mem_erase.mp ha'_mem).1
  have ha'a : a' ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp ha'_mem).2).1
  obtain ⟨b', hcap'⟩ := Sum.isLeft_iff.mp ((D.isCap_def _).mp
    ((D.mem_bottomCap).mp (Finset.mem_erase.mp (Finset.mem_erase.mp ha'_mem).2).2)).2
  have hb'a : b' ≠ a := fun h => ha'b (Sum.inl.inj
    ((D.apply_eq_of_apply_eq hcap').symm.trans (h ▸ hcap)))
  have hd'c : d' ≠ c := fun h => hc'd (Sum.inr.inj
    ((D.apply_eq_of_apply_eq hcup').symm.trans (h ▸ hcup)))
  have hd'd : d' ≠ d := fun h => hc'c (Sum.inr.inj
    (D.val.injective (hcup'.trans (h ▸ hcup.symm))))
  set X₁ : BrauerDiagram k := D.reconnect (Sum.inr c) (Sum.inl a)
  set X₂ : BrauerDiagram k := D.reconnect (Sum.inr c') (Sum.inl a')
  have hX₁_card : X₁.bottomCap.card + 2 = D.bottomCap.card := D.card_bottomCap_reconnect hcap hcup
  have hX₂_card : X₂.bottomCap.card + 2 = D.bottomCap.card := D.card_bottomCap_reconnect hcap' hcup'
  have hX₁_cap' : X₁.val (Sum.inl a') = Sum.inl b' :=
    PerfectMatching.reconnect_val_of_val_eq hcap' Sum.inl_ne_inr (by simpa using ha'a)
      Sum.inl_ne_inr (by simpa using hb'a)
  have hX₁_cup' : X₁.val (Sum.inr c') = Sum.inr d' :=
    PerfectMatching.reconnect_val_of_val_eq hcup' (by simpa using hc'c) Sum.inr_ne_inl
      (by simpa using hd'c) Sum.inr_ne_inl
  have hX₂_cap : X₂.val (Sum.inl a) = Sum.inl b :=
    PerfectMatching.reconnect_val_of_val_eq hcap Sum.inl_ne_inr (by simpa using Ne.symm ha'a)
      Sum.inl_ne_inr (by simpa using Ne.symm ha'b)
  have hX₂_cup : X₂.val (Sum.inr c) = Sum.inr d :=
    PerfectMatching.reconnect_val_of_val_eq hcup (by simpa using Ne.symm hc'c) Sum.inr_ne_inl
      (by simpa using Ne.symm hc'd) Sum.inr_ne_inl
  rw [hmove_cap hcap hcap' hcup', ih_rec X₁ (by omega) hX₁_cap' hX₁_cup',
    ih_rec X₂ (by omega) hX₂_cap hX₂_cup,
    reconnect_reconnect_comm hcap hcap' hcup hcup' ha'a hc'c hc'd,
    ← mul_assoc, (he_disj (Ne.symm hc'c) hd'c.symm (Ne.symm hc'd) hd'd.symm).eq, mul_assoc]

/-- Inductive step for left permutation action at cap-cardinality `m`, given reconnection
independence at cap-cardinality `m` and left permutation action below `m`. -/
private theorem evalDiagram_perm_left_step
    (hs_conj : ∀ (σ : Equiv.Perm (Fin k)) {a b : Fin k}, a ≠ b → s σ * e a b = e (σ a) (σ b) * s σ)
    {m : ℕ}
    (hP₂ : ∀ E : BrauerDiagram k, E.bottomCap.card = m →
      ∀ {a b c d : Fin k}, E.val (Sum.inl a) = Sum.inl b → E.val (Sum.inr c) = Sum.inr d →
      evalDiagram s e E = e c d * evalDiagram s e (E.reconnect (Sum.inr c) (Sum.inl a)))
    (ih_perm : ∀ E : BrauerDiagram k, E.bottomCap.card < m →
      ∀ σ : Equiv.Perm (Fin k),
      s σ * evalDiagram s e E = evalDiagram s e (composeDiagram (permToBrauer σ) E))
    (D : BrauerDiagram k) (hm : D.bottomCap.card = m) (σ : Equiv.Perm (Fin k)) :
    s σ * evalDiagram s e D = evalDiagram s e (composeDiagram (permToBrauer σ) D) := by
  rcases D.bottomCap.eq_empty_or_nonempty with hempty | hne
  · obtain ⟨τ, rfl⟩ := (BrauerDiagram.exists_eq_permToBrauer_iff_bottomCap_eq_empty (D := D)).mpr
      hempty
    rw [composeDiagram_permToBrauer, evalDiagram_permToBrauer, evalDiagram_permToBrauer, s.map_mul]
  obtain ⟨a, b, c, d, hcap, hcup, -⟩ := exists_evalDiagram_eq_of_nonempty s e hne
  have hcd : c ≠ d := fun h => D.apply_ne (Sum.inr c) (by rw [hcup, h])
  have hD'_card : (composeDiagram (permToBrauer σ) D).bottomCap.card = m := by
    rw [composeDiagram_permToBrauer_left, BrauerDiagram.card_bottomCap_relabel, hm]
  have hD'_cap : (composeDiagram (permToBrauer σ) D).val (Sum.inl a) = Sum.inl b := by
    rw [composeDiagram_permToBrauer_left, BrauerDiagram.relabel_val_inl, Equiv.Perm.one_def,
      Equiv.refl_symm, Equiv.refl_apply, hcap, Sum.map_inl, Equiv.refl_apply]
  have hD'_cup : (composeDiagram (permToBrauer σ) D).val (Sum.inr (σ c)) = Sum.inr (σ d) := by
    rw [composeDiagram_permToBrauer_left, BrauerDiagram.relabel_val_inr, σ.symm_apply_apply, hcup,
      Sum.map_inr]
  have hX_card := D.card_bottomCap_reconnect hcap hcup
  rw [hP₂ D hm hcap hcup, hP₂ _ hD'_card hD'_cap hD'_cup,
    reconnect_composeDiagram_permToBrauer_left, ← ih_perm _ (by omega) σ, ← mul_assoc,
    hs_conj σ hcd, mul_assoc]

/-- Reconnection independence and left permutation equivariance for `evalDiagram`. -/
private theorem evalDiagram_reconnect_and_perm_left
    (he_comm : ∀ a b : Fin k, e a b = e b a)
    (he_disj : ∀ {a b c d : Fin k}, a ≠ c → a ≠ d → b ≠ c → b ≠ d → Commute (e a b) (e c d))
    (hs_conj : ∀ (σ : Equiv.Perm (Fin k)) {a b : Fin k}, a ≠ b → s σ * e a b = e (σ a) (σ b) * s σ)
    (hs_swap : ∀ {a b : Fin k}, a ≠ b → s (Equiv.swap a b) * e a b = e a b)
    (he_overlap : ∀ {a b c : Fin k}, a ≠ b → b ≠ c → a ≠ c →
      e a c * e a b = e a c * s (Equiv.swap b c)) :
    (∀ (D : BrauerDiagram k) {a b c d : Fin k},
      D.val (Sum.inl a) = Sum.inl b → D.val (Sum.inr c) = Sum.inr d →
      evalDiagram s e D = e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a))) ∧
    (∀ (D : BrauerDiagram k) (σ : Equiv.Perm (Fin k)),
      s σ * evalDiagram s e D = evalDiagram s e (composeDiagram (permToBrauer σ) D)) := by
  have hall : ∀ m : ℕ,
      (∀ (D : BrauerDiagram k), D.bottomCap.card = m →
        ∀ {a b c d : Fin k}, D.val (Sum.inl a) = Sum.inl b → D.val (Sum.inr c) = Sum.inr d →
        evalDiagram s e D = e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a))) ∧
      (∀ (D : BrauerDiagram k), D.bottomCap.card = m → ∀ σ : Equiv.Perm (Fin k),
        s σ * evalDiagram s e D = evalDiagram s e (composeDiagram (permToBrauer σ) D)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      have hP₂ : ∀ (D : BrauerDiagram k), D.bottomCap.card = m →
          ∀ {a b c d : Fin k}, D.val (Sum.inl a) = Sum.inl b → D.val (Sum.inr c) = Sum.inr d →
          evalDiagram s e D = e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a)) := by
        intro D hm a b c d hcap hcup
        have hne : D.bottomCap.Nonempty := ⟨a, by simp [BrauerDiagram.isCap_def, hcap]⟩
        obtain ⟨a₀, b₀, c₀, d₀, hcap₀, hcup₀, heval⟩ := exists_evalDiagram_eq_of_nonempty s e hne
        have ih_rec : ∀ E : BrauerDiagram k, E.bottomCap.card < D.bottomCap.card →
            ∀ {a b c d : Fin k}, E.val (Sum.inl a) = Sum.inl b → E.val (Sum.inr c) = Sum.inr d →
            evalDiagram s e E = e c d * evalDiagram s e (E.reconnect (Sum.inr c) (Sum.inl a)) :=
          fun E hlt => (ih E.bottomCap.card (hm ▸ hlt)).1 E rfl
        have ih_perm : ∀ E : BrauerDiagram k, E.bottomCap.card < D.bottomCap.card →
            ∀ σ : Equiv.Perm (Fin k),
            s σ * evalDiagram s e E = evalDiagram s e (composeDiagram (permToBrauer σ) E) :=
          fun E hlt => (ih E.bottomCap.card (hm ▸ hlt)).2 E rfl
        have hmc : ∀ {a b a' b' c d : Fin k},
            D.val (Sum.inl a) = Sum.inl b → D.val (Sum.inl a') = Sum.inl b' →
            D.val (Sum.inr c) = Sum.inr d →
            e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a)) =
              e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a')) :=
          evalDiagram_move_cap he_comm he_disj hs_conj hs_swap he_overlap ih_rec ih_perm
        rw [heval, hmc hcap₀ hcap hcup₀, evalDiagram_move_cup he_comm he_disj hmc ih_rec hcap hcup₀
          hcup]
      exact ⟨hP₂, evalDiagram_perm_left_step hs_conj hP₂
        (fun E hlt => (ih E.bottomCap.card hlt).2 E rfl)⟩
  exact ⟨fun D => (hall D.bottomCap.card).1 D rfl, fun D => (hall D.bottomCap.card).2 D rfl⟩

/-- Case of the cap-cup loop rule where both `p` and `q` lie on through strands of `X`. -/
private theorem evalDiagram_capCup_mul_of_isThrough
    (hrec : ∀ (D : BrauerDiagram k) {a b c d : Fin k},
      D.val (Sum.inl a) = Sum.inl b → D.val (Sum.inr c) = Sum.inr d →
      evalDiagram s e D = e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a)))
    {p q : Fin k} (hpq : p ≠ q) {X : BrauerDiagram k}
    (hp : X.IsThrough (Sum.inr p)) (hq : X.IsThrough (Sum.inr q)) :
    e p q * evalDiagram s e X =
      (δ : R) ^ middleLoopCount (capCup p q) X •
        evalDiagram s e (composeDiagram (capCup p q) X) := by
  obtain ⟨a, hXp⟩ := Sum.isLeft_iff.mp (X.isLeft_val_inr hp)
  obtain ⟨b, hXq⟩ := Sum.isLeft_iff.mp (X.isLeft_val_inr hq)
  obtain ⟨hloop, hDcap, hDcup, hDrec⟩ := reconnect_composeDiagram_capCup_of_isThrough hpq hXp hXq
  rw [hloop, pow_zero, one_smul, hrec _ hDcap hDcup, hDrec]

/-- Case of the cap-cup loop rule where `q` lies on a cup `(q, q')` of `X` with `q' ≠ p`. -/
private theorem evalDiagram_capCup_mul_of_cup_ne
    (he_comm : ∀ a b : Fin k, e a b = e b a)
    (he_overlap : ∀ {a b c : Fin k}, a ≠ b → b ≠ c → a ≠ c →
      e a c * e a b = e a c * s (Equiv.swap b c))
    (hrec : ∀ (D : BrauerDiagram k) {a b c d : Fin k},
      D.val (Sum.inl a) = Sum.inl b → D.val (Sum.inr c) = Sum.inr d →
      evalDiagram s e D = e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a)))
    (hperm : ∀ (D : BrauerDiagram k) (σ : Equiv.Perm (Fin k)),
      s σ * evalDiagram s e D = evalDiagram s e (composeDiagram (permToBrauer σ) D))
    {X : BrauerDiagram k} {p q q' : Fin k} (hpq : p ≠ q)
    (hcup_q : X.val (Sum.inr q) = Sum.inr q') (hq'p : q' ≠ p) :
    e p q * evalDiagram s e X =
      (δ : R) ^ middleLoopCount (capCup p q) X •
        evalDiagram s e (composeDiagram (capCup p q) X) := by
  have hqq' : q ≠ q' := fun h => X.apply_ne (Sum.inr q) (by rw [hcup_q, h])
  have hne_bot : X.bottomCap.Nonempty := by
    rw [← Finset.card_pos, X.card_bottomCap_eq_card_topCup, Finset.card_pos]
    exact ⟨q, by simp [BrauerDiagram.isCup_def, hcup_q]⟩
  obtain ⟨a, ha⟩ := hne_bot
  obtain ⟨b, hcap⟩ := Sum.isLeft_iff.mp ((X.isCap_def _).mp ((X.mem_bottomCap).mp ha)).2
  set Y : BrauerDiagram k := X.reconnect (Sum.inr q) (Sum.inl a)
  have hX : composeDiagram (capCup q q') Y = X := composeDiagram_capCup_reconnect hcap hcup_q
  have hloop_Y : middleLoopCount (capCup q q') Y = 0 := middleLoopCount_capCup_reconnect hcap hcup_q
  have hYq_val : Y.val (Sum.inr q) = Sum.inl a := PerfectMatching.reconnect_val_self Sum.inl_ne_inr
  have hYq'_val : Y.val (Sum.inr q') = Sum.inl b :=
    hcap ▸ hcup_q ▸ PerfectMatching.reconnect_val_val_self Sum.inl_ne_inr
  have hYq : Y.IsThrough (Sum.inr q) := by simp [BrauerDiagram.isThrough_def, hYq_val]
  have hYq' : Y.IsThrough (Sum.inr q') := by simp [BrauerDiagram.isThrough_def, hYq'_val]
  set Y' : BrauerDiagram k := composeDiagram (permToBrauer (Equiv.swap q' p)) Y
  have hY'p : Y'.IsThrough (Sum.inr p) := by
    dsimp only [Y']
    rw [composeDiagram_permToBrauer_left]
    simpa using (BrauerDiagram.isThrough_relabel_inr Y 1 (Equiv.swap q' p) q').mpr hYq'
  have hY'q : Y'.IsThrough (Sum.inr q) := by
    dsimp only [Y']
    rw [composeDiagram_permToBrauer_left]
    have hswap_q : Equiv.swap q' p q = q := Equiv.swap_apply_of_ne_of_ne hqq' hpq.symm
    simpa [hswap_q] using (BrauerDiagram.isThrough_relabel_inr Y 1 (Equiv.swap q' p) q).mpr hYq
  have hcomp_eq : composeDiagram (capCup p q) X = composeDiagram (capCup p q) Y' := by
    rw [← hX, ← composeDiagram_assoc, capCup_comm q p,
      composeDiagram_capCup_capCup_eq_composeDiagram_permToBrauer_swap hpq.symm, capCup_comm p q,
      composeDiagram_assoc]
  obtain ⟨a', hY'p_val⟩ := Sum.isLeft_iff.mp (Y'.isLeft_val_inr hY'p)
  obtain ⟨b', hY'q_val⟩ := Sum.isLeft_iff.mp (Y'.isLeft_val_inr hY'q)
  have hloop_Y' : middleLoopCount (capCup p q) Y' = 0 :=
    (reconnect_composeDiagram_capCup_of_isThrough hpq hY'p_val hY'q_val).1
  have hloop_X : middleLoopCount (capCup p q) X = 0 := by
    have h₁ := middleLoopCount_add_middleLoopCount_composeDiagram (capCup p q) (capCup q q') Y
    have h₂ := middleLoopCount_add_middleLoopCount_composeDiagram (capCup p q)
      (permToBrauer (Equiv.swap q' p)) Y
    have hloop_pq_qq' : middleLoopCount (capCup p q) (capCup q q') = 0 :=
      middleLoopCount_capCup_capCup_right_of_ne hq'p.symm q
    have hcomp_inner : composeDiagram (capCup p q) (capCup q q') =
        composeDiagram (capCup p q) (permToBrauer (Equiv.swap q' p)) := by
      rw [capCup_comm q p,
        composeDiagram_capCup_capCup_eq_composeDiagram_permToBrauer_swap hpq.symm, capCup_comm p q]
    rw [hX, hloop_pq_qq', hloop_Y, hcomp_inner] at h₁
    rw [middleLoopCount_permToBrauer_right, middleLoopCount_permToBrauer_left,
      show composeDiagram (permToBrauer (Equiv.swap q' p)) Y = Y' from rfl, hloop_Y'] at h₂
    omega
  rw [hrec X hcap hcup_q, ← mul_assoc, he_comm p q, he_overlap hqq' hq'p hpq.symm, he_comm q p,
    mul_assoc, hperm Y (Equiv.swap q' p),
    evalDiagram_capCup_mul_of_isThrough (δ := δ) hrec hpq hY'p hY'q,
    hloop_Y', pow_zero, one_smul, ← hcomp_eq, hloop_X, pow_zero, one_smul]

/-- Left multiplication by `e p q` (`p ≠ q`) obeys the loop rule against any diagram `X`. -/
private theorem evalDiagram_capCup_mul
    (he_comm : ∀ a b : Fin k, e a b = e b a)
    (he_mul_self : ∀ {a b : Fin k}, a ≠ b → e a b * e a b = δ • e a b)
    (he_overlap : ∀ {a b c : Fin k}, a ≠ b → b ≠ c → a ≠ c →
      e a c * e a b = e a c * s (Equiv.swap b c))
    (hrec : ∀ (D : BrauerDiagram k) {a b c d : Fin k},
      D.val (Sum.inl a) = Sum.inl b → D.val (Sum.inr c) = Sum.inr d →
      evalDiagram s e D = e c d * evalDiagram s e (D.reconnect (Sum.inr c) (Sum.inl a)))
    (hperm : ∀ (D : BrauerDiagram k) (σ : Equiv.Perm (Fin k)),
      s σ * evalDiagram s e D = evalDiagram s e (composeDiagram (permToBrauer σ) D))
    {p q : Fin k} (hpq : p ≠ q) (X : BrauerDiagram k) :
    e p q * evalDiagram s e X =
      δ ^ middleLoopCount (capCup p q) X • evalDiagram s e (composeDiagram (capCup p q) X) := by
  by_cases hsame : X.val (Sum.inr p) = Sum.inr q
  · -- `p` and `q` form a single cup of `X`, closing exactly one loop.
    have hne_bot : X.bottomCap.Nonempty := by
      rw [← Finset.card_pos, X.card_bottomCap_eq_card_topCup, Finset.card_pos]
      exact ⟨p, by simp [BrauerDiagram.isCup_def, hsame]⟩
    obtain ⟨a, ha⟩ := hne_bot
    obtain ⟨b, hcap⟩ := Sum.isLeft_iff.mp ((X.isCap_def _).mp ((X.mem_bottomCap).mp ha)).2
    set Y : BrauerDiagram k := X.reconnect (Sum.inr p) (Sum.inl a)
    have hX : composeDiagram (capCup p q) Y = X := composeDiagram_capCup_reconnect hcap hsame
    have hloop_Y : middleLoopCount (capCup p q) Y = 0 := middleLoopCount_capCup_reconnect hcap hsame
    have hcomp_X : composeDiagram (capCup p q) X = X := by
      rw [← hX, ← composeDiagram_assoc, composeDiagram_capCup_capCup]
    have hloop_X : middleLoopCount (capCup p q) X = 1 := by
      have h := middleLoopCount_add_middleLoopCount_composeDiagram (capCup p q) (capCup p q) Y
      rw [middleLoopCount_capCup_capCup hpq, composeDiagram_capCup_capCup, hloop_Y, hX] at h
      omega
    rw [hrec X hcap hsame, ← mul_assoc, he_mul_self hpq, Algebra.smul_mul_assoc,
      ← hrec X hcap hsame, hloop_X, pow_one, hcomp_X]
  by_cases hcup_q : X.IsCup (Sum.inr q)
  · obtain ⟨q', hq'⟩ := Sum.isRight_iff.mp ((X.isCup_def _).mp hcup_q).2
    have hq'p : q' ≠ p := fun h => hsame (X.apply_eq_of_apply_eq (h ▸ hq'))
    exact evalDiagram_capCup_mul_of_cup_ne he_comm he_overlap hrec hperm hpq hq' hq'p
  by_cases hcup_p : X.IsCup (Sum.inr p)
  · obtain ⟨p', hp'⟩ := Sum.isRight_iff.mp ((X.isCup_def _).mp hcup_p).2
    have hp'q : p' ≠ q := fun h => hsame (h ▸ hp')
    rw [he_comm p q, capCup_comm q p]
    exact evalDiagram_capCup_mul_of_cup_ne he_comm he_overlap hrec hperm hpq.symm hp' hp'q
  exact evalDiagram_capCup_mul_of_isThrough hrec hpq
    ((X.isCup_inr_iff p).not_left.mp hcup_p) ((X.isCup_inr_iff q).not_left.mp hcup_q)

/-- Full loop rule `evalDiagram D₁ * evalDiagram D₂ = δ ^ middleLoopCount D₁ D₂ • ...`. -/
private theorem evalDiagram_mul
    (he_comm : ∀ a b : Fin k, e a b = e b a)
    (he_mul_self : ∀ {a b : Fin k}, a ≠ b → e a b * e a b = δ • e a b)
    (he_disj : ∀ {a b c d : Fin k}, a ≠ c → a ≠ d → b ≠ c → b ≠ d → Commute (e a b) (e c d))
    (hs_conj : ∀ (σ : Equiv.Perm (Fin k)) {a b : Fin k}, a ≠ b → s σ * e a b = e (σ a) (σ b) * s σ)
    (hs_swap : ∀ {a b : Fin k}, a ≠ b → s (Equiv.swap a b) * e a b = e a b)
    (he_overlap : ∀ {a b c : Fin k}, a ≠ b → b ≠ c → a ≠ c →
      e a c * e a b = e a c * s (Equiv.swap b c))
    (D₁ D₂ : BrauerDiagram k) :
    evalDiagram s e D₁ * evalDiagram s e D₂ =
      δ ^ middleLoopCount D₁ D₂ • evalDiagram s e (composeDiagram D₁ D₂) := by
  obtain ⟨hrec, hperm⟩ :=
    evalDiagram_reconnect_and_perm_left (s := s) (e := e) he_comm he_disj hs_conj hs_swap he_overlap
  have hcapCup {p q : Fin k} (hpq : p ≠ q) (X : BrauerDiagram k) :=
    evalDiagram_capCup_mul (δ := δ) he_comm he_mul_self he_overlap hrec hperm hpq X
  induction D₁ using BrauerDiagram.capCup_induction_on with
  | permToBrauer σ =>
    rw [evalDiagram_permToBrauer, middleLoopCount_permToBrauer_left, pow_zero, one_smul, hperm]
  | capCup_compose a b X hab hloop ih =>
    have h₁ := hcapCup hab X
    rw [hloop, pow_zero, one_smul] at h₁
    rw [← h₁, mul_assoc, ih, Algebra.mul_smul_comm, hcapCup hab (composeDiagram X D₂), smul_smul,
      ← pow_add, ← composeDiagram_assoc]
    have hcount := middleLoopCount_add_middleLoopCount_composeDiagram (capCup a b) X D₂
    rw [hloop, zero_add] at hcount
    rw [← hcount]

private theorem evalDiagram_capCup
    (he_comm : ∀ a b : Fin k, e a b = e b a)
    (he_disj : ∀ {a b c d : Fin k}, a ≠ c → a ≠ d → b ≠ c → b ≠ d → Commute (e a b) (e c d))
    (hs_conj : ∀ (σ : Equiv.Perm (Fin k)) {a b : Fin k}, a ≠ b → s σ * e a b = e (σ a) (σ b) * s σ)
    (hs_swap : ∀ {a b : Fin k}, a ≠ b → s (Equiv.swap a b) * e a b = e a b)
    (he_overlap : ∀ {a b c : Fin k}, a ≠ b → b ≠ c → a ≠ c →
      e a c * e a b = e a c * s (Equiv.swap b c))
    {a b : Fin k} (hab : a ≠ b) :
    evalDiagram s e (capCup a b) = e a b := by
  obtain ⟨hrec, -⟩ :=
    evalDiagram_reconnect_and_perm_left (s := s) (e := e) he_comm he_disj hs_conj hs_swap he_overlap
  have hrec_one : (capCup a b).reconnect (Sum.inr a) (Sum.inl a) = permToBrauer 1 := by
    have hcap := capCup_val_inl_left hab
    have hcup := capCup_val_inr_left hab
    set Y : BrauerDiagram k := (capCup a b).reconnect (Sum.inr a) (Sum.inl a)
    have hYa : Y.val (Sum.inl a) = Sum.inr a :=
      PerfectMatching.reconnect_val_right Sum.inl_ne_inr
    have hYb : Y.val (Sum.inl b) = Sum.inr b :=
      hcap ▸ hcup ▸ PerfectMatching.reconnect_val_val_right Sum.inl_ne_inr
    have hYc : Y.val (Sum.inr a) = Sum.inl a :=
      PerfectMatching.reconnect_val_self Sum.inl_ne_inr
    have hYd : Y.val (Sum.inr b) = Sum.inl b :=
      hcap ▸ hcup ▸ PerfectMatching.reconnect_val_val_self Sum.inl_ne_inr
    refine Subtype.ext (Equiv.ext fun x => ?_)
    by_cases hxa : x = Sum.inl a
    · subst x; simp [hYa, Equiv.Perm.one_def]
    by_cases hxb : x = Sum.inl b
    · subst x; simp [hYb, Equiv.Perm.one_def]
    by_cases hxc : x = Sum.inr a
    · subst x; simp [hYc, Equiv.Perm.one_def]
    by_cases hxd : x = Sum.inr b
    · subst x; simp [hYd, Equiv.Perm.one_def]
    rw [PerfectMatching.reconnect_val_of_ne hxc hxa (hcup ▸ hxd) (hcap ▸ hxb)]
    rcases x with i | j
    · simp [capCup_val_inl_of_ne (by simpa using hxa) (by simpa using hxb), Equiv.Perm.one_def]
    · simp [capCup_val_inr_of_ne (by simpa using hxc) (by simpa using hxd), Equiv.Perm.one_def]
  rw [hrec (capCup a b) (capCup_val_inl_left hab) (capCup_val_inr_left hab), hrec_one,
    evalDiagram_permToBrauer, s.map_one, mul_one]

end InductionSteps

/-- **An algebra map out of `B_k(δ)` is determined by its values on all permutation diagrams and on
cap-cup diagrams at distinct strands**, uniformly in `k : ℕ` (including `k < 2`, where no pair of
distinct strands exists). -/
theorem algHom_ext_of_permToBrauer_of_capCup {f g : BrauerAlgebra R δ k →ₐ[R] A}
    (hperm : ∀ σ : Equiv.Perm (Fin k), f (of (permToBrauer σ)) = g (of (permToBrauer σ)))
    (hcapCup : ∀ {a b : Fin k}, a ≠ b → f (of (capCup a b)) = g (of (capCup a b))) :
    f = g := by
  refine AlgHom.ext_of_adjoin_eq_top
    (adjoin_range_of_permToBrauer_union_range_of_capCup R δ k) ?_
  rintro _ (⟨σ, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
  · exact hperm σ
  · rcases eq_or_ne a b with rfl | hab
    · simpa only [capCup_self] using hperm 1
    · exact hcapCup hab

section LiftAPI

variable (s : Equiv.Perm (Fin k) →* A) (e : Fin k → Fin k → A)
  (he_comm : ∀ a b : Fin k, e a b = e b a)
  (he_mul_self : ∀ {a b : Fin k}, a ≠ b → e a b * e a b = δ • e a b)
  (he_disj : ∀ {a b c d : Fin k}, a ≠ c → a ≠ d → b ≠ c → b ≠ d → Commute (e a b) (e c d))
  (hs_conj : ∀ (σ : Equiv.Perm (Fin k)) {a b : Fin k}, a ≠ b → s σ * e a b = e (σ a) (σ b) * s σ)
  (hs_swap : ∀ {a b : Fin k}, a ≠ b → s (Equiv.swap a b) * e a b = e a b)
  (he_overlap : ∀ {a b c : Fin k}, a ≠ b → b ≠ c → a ≠ c →
    e a c * e a b = e a c * s (Equiv.swap b c))

/-- **Universal property of the Brauer algebra on permutations and cap-cup generators.**

Given a monoid homomorphism `s : Equiv.Perm (Fin k) →* A` into an `R`-algebra `A` and elements
`e a b : A` for distinct strands `a ≠ b` satisfying the six Brauer relations at loop value `δ`,
`liftOfPermCapCup` constructs the unique `R`-algebra homomorphism `BrauerAlgebra R δ k →ₐ[R] A`
sending `of (permToBrauer σ)` to `s σ` and `of (capCup a b)` (`a ≠ b`) to `e a b`. Values of `e` on
the diagonal `a = b` are never read. -/
noncomputable def liftOfPermCapCup : BrauerAlgebra R δ k →ₐ[R] A :=
  lift (evalDiagram s e) (by rw [evalDiagram_permToBrauer, s.map_one])
    (evalDiagram_mul he_comm he_mul_self he_disj hs_conj hs_swap he_overlap)

/-- `liftOfPermCapCup` sends the diagram of a permutation `σ` to `s σ`. -/
@[simp]
theorem liftOfPermCapCup_of_permToBrauer (σ : Equiv.Perm (Fin k)) :
    liftOfPermCapCup s e he_comm he_mul_self he_disj hs_conj hs_swap he_overlap
      (of (permToBrauer σ) : BrauerAlgebra R δ k) = s σ := by
  rw [liftOfPermCapCup, lift_of, evalDiagram_permToBrauer]

/-- Along `ofPerm`, `liftOfPermCapCup` restricts to `MonoidAlgebra.lift R A _ s`. -/
theorem liftOfPermCapCup_comp_ofPerm :
    (liftOfPermCapCup s e he_comm he_mul_self he_disj hs_conj hs_swap he_overlap).comp
        (ofPerm R δ k) =
      MonoidAlgebra.lift R A (Equiv.Perm (Fin k)) s := by
  ext σ
  rw [AlgHom.comp_apply, ofPerm_single, one_smul, liftOfPermCapCup_of_permToBrauer,
    MonoidAlgebra.lift_single, one_smul]

/-- `liftOfPermCapCup` sends the cap-cup diagram on two distinct strands `a ≠ b` to `e a b`. -/
@[simp]
theorem liftOfPermCapCup_of_capCup {a b : Fin k} (hab : a ≠ b) :
    liftOfPermCapCup s e he_comm he_mul_self he_disj hs_conj hs_swap he_overlap
      (of (capCup a b) : BrauerAlgebra R δ k) = e a b := by
  rw [liftOfPermCapCup, lift_of, evalDiagram_capCup he_comm he_disj hs_conj hs_swap he_overlap hab]

/-- **Uniqueness of `liftOfPermCapCup`**: any `R`-algebra map agreeing with `s` on the permutation
diagrams and with `e` on the cap-cup diagrams at distinct strands equals `liftOfPermCapCup`. -/
theorem eq_liftOfPermCapCup {f : BrauerAlgebra R δ k →ₐ[R] A}
    (hperm : ∀ σ : Equiv.Perm (Fin k), f (of (permToBrauer σ)) = s σ)
    (hcapCup : ∀ {a b : Fin k}, a ≠ b → f (of (capCup a b)) = e a b) :
    f = liftOfPermCapCup s e he_comm he_mul_self he_disj hs_conj hs_swap he_overlap :=
  algHom_ext_of_permToBrauer_of_capCup (fun σ => by simp [hperm σ])
    (fun hab => by simp [hcapCup hab, hab])

end LiftAPI

end LiftOfPermCapCup

end BrauerAlgebra

end TauCeti
