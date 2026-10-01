/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Kauffman
public import TauCeti.KnotTheory.PDCode.Planar
import Mathlib.Tactic.LinearCombination
import TauCeti.GroupTheory.Perm.SumCongr
import TauCeti.GroupTheory.Perm.SwapFactors

/-!
# Algebraic clasp insertion in PD-codes

The code-level tangle replacement underlying the second Reidemeister move creates two crossings
at which the same strand is over. On a PD-code with `n` crossings,
`TauCeti.PDCode.insertClasp D p q b hqp hqe` performs this algebraic clasp insertion on two
distinct arcs: the arc `P` ending at the half-edge `p` and the arc `Q` ending at the half-edge
`q`. Both arcs are cut open and routed through the two new crossings. These are the last two,
`(Fin.last n).castSucc` (the first crossing, reached from `p` and `q`) and `Fin.last (n + 1)`
(the second crossing, reached from the other ends of the two arcs).

With the slots of a crossing in counterclockwise order, the strand along `P` occupies slots `0`
and `2` of the first crossing and slots `1` and `3` of the second, and the strand along `Q`
occupies slots `1` and `3` of the first crossing and slots `0` and `2` of the second. The arcs are:
`p` to slot `0` and `q` to slot `1` of the first crossing; slot `3` of the second crossing to the
other end of `P` and slot `2` to the other end of `Q`; and the two short arcs of the clasp, from
slot `2` of the first crossing to slot `1` of the second (along `P`) and from slot `3` of the
first crossing to slot `0` of the second (along `Q`). The Boolean `b` is the over-pair indicator
of the first crossing, and the second crossing gets `!b`, so that the same strand is over at both:
with `b = false` it is the strand along `P`.

Of the four ways to smooth the two new crossings, one smooths them back into the two original
arcs. The other three all reconnect the cut ends instead, `p` to `q` and the other end of `P` to
the other end of `Q`, and one of these three also cuts off the circle through the two short arcs
of the clasp. The first state and the circle-cutting one carry weight `1` in the Kauffman
bracket, and the other two weights `a ^ 2` and `a⁻¹ ^ 2`; since `a ^ 2 + a⁻¹ ^ 2 + δ = 0` for the
loop value `δ = -(a ^ 2 + a⁻¹ ^ 2)`, the reconnected terms cancel, so the clasp insertion leaves
the **Kauffman bracket invariant**. The insertion also keeps the number of components.

On its own the insertion is an algebraic operation on the code: nothing forces the two arcs to
border a common region of the diagram. An arc borders a face of `TauCeti.PDCode.face` on each
side, the face at each of its two ends: `P` borders the faces at `p` and at `D.edgePair.val p`.
Going round the clasp counterclockwise, its four outer ends are met in the order `p`, `q`,
`D.edgePair.val q`, `D.edgePair.val p`, so it can be drawn inside a face bordered by both arcs
when the face at the far end `D.edgePair.val p` of `P` is the face at `q`, that is, when `P` and
`Q` border a common face on the side of `D.edgePair.val p` and of `q` respectively. Every common
face of the two arcs is of this form for a suitable choice of the ends passed as `p` and `q`; for
instance, passing `D.edgePair.val q` instead of `q` uses the other side of `Q`. Under this face
condition the insertion is the **second Reidemeister move**: the clasp cuts that face in two and
adds the bigon between its two crossings, so the code gets two more faces
(`TauCeti.PDCode.faceCount_insertClasp_of_face_eq`), its underlying graph keeps its connected
components, and it is planar exactly when `D` is (`TauCeti.PDCode.isPlanar_insertClasp_iff`). The
face condition cannot be dropped: if the two arcs lie in one connected component but the face at
`D.edgePair.val p` is not the face at `q`, the clasp joins two faces into one, which its bigon
only makes up for, and the new code is never planar
(`TauCeti.PDCode.not_isPlanar_insertClasp_of_face_ne`). The insertion applies only to codes with a
crossing; an insertion involving a crossing-free circle is not treated here.

## Main definitions

* `TauCeti.PDCode.insertClasp`: algebraically insert a two-crossing clasp into two arcs.

## Main results

* `TauCeti.PDCode.crossingComponentCount_insertClasp`: the insertion keeps the number of
  components.
* `TauCeti.PDCode.kauffmanBracket_insertClasp`: the insertion leaves the Kauffman bracket
  unchanged.
* `TauCeti.PDCode.mirror_insertClasp`: mirroring the new code inserts the clasp with the other
  strand over into the mirror code.
* `TauCeti.PDCode.faceCount_insertClasp_of_face_eq` and
  `TauCeti.PDCode.faceCount_insertClasp_of_face_ne`: the insertion adds two faces when the face
  at `D.edgePair.val p` is the face at `q`, and none otherwise.
* `TauCeti.PDCode.card_monodromyOrbit_insertClasp`: the insertion keeps the connected components
  of the underlying graph when the two arcs lie in one of them.
* `TauCeti.PDCode.isPlanar_insertClasp_iff`: when the face at `D.edgePair.val p` is the face at
  `q`, the clasp keeps the code planar, and `TauCeti.PDCode.not_isPlanar_insertClasp_of_face_ne`:
  otherwise, between arcs of one component, it never yields a planar code.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1 (the
  Reidemeister moves) and Chapter 3, Lemma 3.3 (the bracket under the second move).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2-3 (the PD convention).
-/

public section

namespace TauCeti

open Equiv Equiv.Perm TemperleyLieb

namespace PDCode

variable {n : ℕ}

section Clasp

/-! ### The arcs of a clasp, on the old half-edges and the slots of two new crossings

A clasp's arcs are built as an involution of `(α ⊕ Fin 4) ⊕ Fin 4`: `α` holds the old half-edges,
the middle `Fin 4` the slots of the first new crossing, and the last `Fin 4` those of the second.
With `e` the old arcs, the arcs from `p` to `e p` and from `q` to `e q` are cut and routed through
the slots. These helpers serve only the proofs in this file. -/

variable {α : Type*} [DecidableEq α] {e : Perm α} {p q : α}

/-- The arcs of the code with a clasp at the arcs ending at `p` and `q`: `p` is joined to slot `0`
and `q` to slot `1` of the first new crossing, `e p` to slot `3` and `e q` to slot `2` of the
second, slots `2` and `3` of the first crossing to slots `1` and `0` of the second, and every
other half-edge to its old partner. -/
private def claspFun (e : Perm α) (p q : α) : (α ⊕ Fin 4) ⊕ Fin 4 → (α ⊕ Fin 4) ⊕ Fin 4
  | .inl (.inl x) =>
    if x = p then .inl (.inr 0) else if x = e p then .inr 3
    else if x = q then .inl (.inr 1) else if x = e q then .inr 2 else .inl (.inl (e x))
  | .inl (.inr i) => ![.inl (.inl p), .inl (.inl q), .inr 1, .inr 0] i
  | .inr i => ![.inl (.inr 3), .inl (.inr 2), .inl (.inl (e q)), .inl (.inl (e p))] i

omit [DecidableEq α] in
private theorem apply_ne_self_of_ne (he : IsPerfectMatching e) (hqe : q ≠ e p) : e q ≠ p := fun h =>
  hqe (by rw [← h, he.apply_apply])

omit [DecidableEq α] in
private theorem apply_ne_apply_of_ne (hqp : q ≠ p) : e q ≠ e p := fun h =>
  hqp (e.injective h)

private theorem claspFun_self : claspFun e p q (.inl (.inl p)) = .inl (.inr 0) := by
  simp [claspFun]

private theorem claspFun_apply_self (he : IsPerfectMatching e) :
    claspFun e p q (.inl (.inl (e p))) = .inr 3 := by
  simp [claspFun, he.apply_ne p]

private theorem claspFun_right (hqp : q ≠ p) (hqe : q ≠ e p) :
    claspFun e p q (.inl (.inl q)) = .inl (.inr 1) := by
  simp [claspFun, hqp, hqe]

private theorem claspFun_apply_right (he : IsPerfectMatching e) (hqp : q ≠ p) (hqe : q ≠ e p) :
    claspFun e p q (.inl (.inl (e q))) = .inr 2 := by
  simp [claspFun, apply_ne_self_of_ne he hqe, apply_ne_apply_of_ne hqp, he.apply_ne q]

private theorem claspFun_of_ne {x : α} (hxp : x ≠ p) (hxe : x ≠ e p) (hxq : x ≠ q)
    (hxe' : x ≠ e q) : claspFun e p q (.inl (.inl x)) = .inl (.inl (e x)) := by
  simp [claspFun, hxp, hxe, hxq, hxe']

private theorem claspFun_involutive (he : IsPerfectMatching e) (hqp : q ≠ p) (hqe : q ≠ e p) :
    Function.Involutive (claspFun e p q) := by
  intro y
  have hvals := And.intro (claspFun_right (e := e) hqp hqe) (claspFun_apply_right he hqp hqe)
  rcases y with (x | i) | i
  · by_cases hxp : x = p
    · subst hxp; rw [claspFun_self]; rfl
    by_cases hxe : x = e p
    · subst hxe; rw [claspFun_apply_self he]; rfl
    by_cases hxq : x = q
    · subst hxq; rw [hvals.1]; rfl
    by_cases hxe' : x = e q
    · subst hxe'; rw [hvals.2]; rfl
    rw [claspFun_of_ne hxp hxe hxq hxe', claspFun_of_ne, he.apply_apply]
    · exact fun h => hxe (by rw [← h, he.apply_apply])
    · exact fun h => hxp (e.injective h)
    · exact fun h => hxe' (by rw [← h, he.apply_apply])
    · exact fun h => hxq (e.injective h)
  · fin_cases i
    · exact claspFun_self
    · exact hvals.1
    · rfl
    · rfl
  · fin_cases i
    · rfl
    · rfl
    · exact hvals.2
    · exact claspFun_apply_self he

private theorem claspFun_ne (he : IsPerfectMatching e) (hqp : q ≠ p) (hqe : q ≠ e p)
    (y : (α ⊕ Fin 4) ⊕ Fin 4) :
    claspFun e p q y ≠ y := by
  rcases y with (x | i) | i
  · by_cases hxp : x = p
    · subst hxp; simp [claspFun_self]
    by_cases hxe : x = e p
    · subst hxe; simp [claspFun_apply_self he]
    by_cases hxq : x = q
    · subst hxq; simp [claspFun_right hqp hqe]
    by_cases hxe' : x = e q
    · subst hxe'; simp [claspFun_apply_right he hqp hqe]
    simp [claspFun_of_ne hxp hxe hxq hxe', he.apply_ne x]
  · fin_cases i <;> simp [claspFun]
  · fin_cases i <;> simp [claspFun]

/-- The arcs of the code with a clasp at the arcs ending at `p` and `q`, as a perfect matching
of the old half-edges and the eight new slots. -/
private def claspMatching (e : Perm α) (he : IsPerfectMatching e) (p q : α) (hqp : q ≠ p)
    (hqe : q ≠ e p) : PerfectMatching ((α ⊕ Fin 4) ⊕ Fin 4) :=
  PerfectMatching.mk (Function.Involutive.toPerm _ (claspFun_involutive he hqp hqe))
    (claspFun_involutive he hqp hqe) (claspFun_ne he hqp hqe)

private theorem claspMatching_val_apply (he : IsPerfectMatching e) (hqp : q ≠ p) (hqe : q ≠ e p)
    (y : (α ⊕ Fin 4) ⊕ Fin 4) : (claspMatching e he p q hqp hqe).val y = claspFun e p q y := by
  have h : (claspMatching e he p q hqp hqe).val =
      Function.Involutive.toPerm _ (claspFun_involutive he hqp hqe) :=
    PerfectMatching.val_mk _ _ _
  rw [h, Function.Involutive.coe_toPerm]

/-- The old arcs reconnected as the clasp's reconnecting smoothings leave them: `p` is joined to
`q`, `e p` to `e q`, and every other half-edge to its old partner. -/
private def reconnect (e : Perm α) (p q : α) : Perm α :=
  (swap (e p) q).permCongr e

private theorem isPerfectMatching_reconnect (he : IsPerfectMatching e) (p q : α) :
    IsPerfectMatching (reconnect e p q) :=
  PerfectMatching.isPerfectMatching_permCongr _ he

section Reconnect

variable (he : IsPerfectMatching e)
include he

omit he in
private theorem reconnect_apply (x : α) :
    reconnect e p q x = swap (e p) q (e (swap (e p) q x)) := by
  rw [reconnect, Equiv.permCongr_apply, symm_swap]

private theorem reconnect_self (hqp : q ≠ p) : reconnect e p q p = q := by
  rw [reconnect_apply, swap_apply_of_ne_of_ne (he.apply_ne p).symm hqp.symm, swap_apply_left]

private theorem reconnect_right (hqp : q ≠ p) : reconnect e p q q = p := by
  rw [reconnect_apply, swap_apply_right, he.apply_apply,
    swap_apply_of_ne_of_ne (he.apply_ne p).symm hqp.symm]

private theorem reconnect_apply_self (hqp : q ≠ p) :
    reconnect e p q (e p) = e q := by
  rw [reconnect_apply, swap_apply_left,
    swap_apply_of_ne_of_ne (apply_ne_apply_of_ne hqp) (he.apply_ne q)]

private theorem reconnect_apply_right (hqp : q ≠ p) :
    reconnect e p q (e q) = e p := by
  rw [reconnect_apply, swap_apply_of_ne_of_ne (apply_ne_apply_of_ne hqp) (he.apply_ne q),
    he.apply_apply, swap_apply_right]

private theorem reconnect_of_ne {x : α} (hxp : x ≠ p) (hxe : x ≠ e p) (hxq : x ≠ q)
    (hxe' : x ≠ e q) : reconnect e p q x = e x := by
  have h₁ : e x ≠ e p := fun h => hxp (e.injective h)
  have h₂ : e x ≠ q := fun h => hxe' (by rw [← h, he.apply_apply])
  rw [reconnect_apply, swap_apply_of_ne_of_ne hxe hxq, swap_apply_of_ne_of_ne h₁ h₂]

end Reconnect

section Smoothing

/-! ### Following the new crossings

Each way of reconnecting the eight new slots, after the arcs of the clasp, is an old traversal
with the new slots spliced in. Written as a product of transpositions, each splice removes one
orbit, which is how the orbits are counted below. -/

variable (he : IsPerfectMatching e) (hqp : q ≠ p) (hqe : q ≠ e p)

omit [DecidableEq α] in
/-- Two permutations of the half-edges of a clasp agree once they agree at the four ends of the
two cut arcs, at every other old half-edge, and at the eight new slots. -/
private theorem clasp_ext {F G : Perm ((α ⊕ Fin 4) ⊕ Fin 4)}
    (hp : F (.inl (.inl p)) = G (.inl (.inl p)))
    (hep : F (.inl (.inl (e p))) = G (.inl (.inl (e p))))
    (hq : F (.inl (.inl q)) = G (.inl (.inl q)))
    (heq : F (.inl (.inl (e q))) = G (.inl (.inl (e q))))
    (hx : ∀ x, x ≠ p → x ≠ e p → x ≠ q → x ≠ e q → F (.inl (.inl x)) = G (.inl (.inl x)))
    (hu : ∀ i, F (.inl (.inr i)) = G (.inl (.inr i))) (hv : ∀ i, F (.inr i) = G (.inr i)) :
    F = G := by
  ext y
  rcases y with (x | i) | i
  · by_cases hxp : x = p
    · subst hxp; exact hp
    by_cases hxe : x = e p
    · subst hxe; exact hep
    by_cases hxq : x = q
    · subst hxq; exact hq
    by_cases hxe' : x = e q
    · subst hxe'; exact heq
    exact hx x hxp hxe hxq hxe'
  · exact hu i
  · exact hv i

include he hqp hqe in
/-- Smoothing both new crossings by `slotSmoothing false` restores the two cut arcs: it is the
old traversal `T * e` with each end of the cut arcs followed by two new slots. -/
private theorem sumCongr_false_false_mul_claspMatching (T : Perm α) :
    Perm.sumCongr (Perm.sumCongr T (slotSmoothing false)) (slotSmoothing false) *
        (claspMatching e he p q hqp hqe).val =
      Perm.sumCongr (Perm.sumCongr (T * e) 1) 1 *
        swap (.inl (.inl p)) (.inr 3) * swap (.inl (.inl p)) (.inl (.inr 3)) *
        swap (.inl (.inl (e p))) (.inl (.inr 0)) * swap (.inl (.inl (e p))) (.inr 0) *
        swap (.inl (.inl q)) (.inr 2) * swap (.inl (.inl q)) (.inl (.inr 2)) *
        swap (.inl (.inl (e q))) (.inl (.inr 1)) * swap (.inl (.inl (e q))) (.inr 1) := by
  have hinv := he.apply_apply
  have hne := he.apply_ne
  have h₁ := apply_ne_self_of_ne he hqe
  have h₂ := apply_ne_apply_of_ne (e := e) hqp
  refine clasp_ext (e := e) (p := p) (q := q) ?_ ?_ ?_ ?_ (fun x hxp hxe hxq hxe' => ?_)
    (fun i => ?_) (fun i => ?_)
  all_goals (try fin_cases i) <;> simp [claspMatching_val_apply, claspFun, swap_apply_def,
    hqp.symm, hqe.symm, h₁.symm, h₂.symm, (hne p).symm, (hne q).symm, *]
include he hqp hqe in
/-- Following the strands through both new crossings restores the two cut arcs as well. -/
private theorem sumCongr_opposite_mul_claspMatching (T : Perm α) :
    Perm.sumCongr (Perm.sumCongr T oppositeCrossingSlot) oppositeCrossingSlot *
        (claspMatching e he p q hqp hqe).val =
      Perm.sumCongr (Perm.sumCongr (T * e) 1) 1 *
        swap (.inl (.inl p)) (.inr 3) * swap (.inl (.inl p)) (.inl (.inr 2)) *
        swap (.inl (.inl (e p))) (.inl (.inr 0)) * swap (.inl (.inl (e p))) (.inr 1) *
        swap (.inl (.inl q)) (.inr 2) * swap (.inl (.inl q)) (.inl (.inr 3)) *
        swap (.inl (.inl (e q))) (.inl (.inr 1)) * swap (.inl (.inl (e q))) (.inr 0) := by
  rw [oppositeCrossingSlot_eq_swap_mul_swap]
  have hinv := he.apply_apply
  have hne := he.apply_ne
  have h₁ := apply_ne_self_of_ne he hqe
  have h₂ := apply_ne_apply_of_ne (e := e) hqp
  refine clasp_ext (e := e) (p := p) (q := q) ?_ ?_ ?_ ?_ (fun x hxp hxe hxq hxe' => ?_)
    (fun i => ?_) (fun i => ?_)
  all_goals (try fin_cases i) <;> simp [claspMatching_val_apply, claspFun, swap_apply_def,
    hqp.symm, hqe.symm, h₁.symm, h₂.symm, (hne p).symm, (hne q).symm, *]
include he hqp hqe in
/-- Smoothing the first new crossing by `slotSmoothing true` and the second by
`slotSmoothing false` joins `p` to `q` and `e p` to `e q`. -/
private theorem sumCongr_true_false_mul_claspMatching (T : Perm α) :
    Perm.sumCongr (Perm.sumCongr T (slotSmoothing true)) (slotSmoothing false) *
        (claspMatching e he p q hqp hqe).val =
      Perm.sumCongr (Perm.sumCongr (T * reconnect e p q) 1) 1 *
        swap (.inl (.inl p)) (.inl (.inr 1)) * swap (.inl (.inl q)) (.inl (.inr 0)) *
        swap (.inl (.inl (e p))) (.inr 2) * swap (.inl (.inl (e p))) (.inl (.inr 2)) *
        swap (.inl (.inl (e p))) (.inr 0) *
        swap (.inl (.inl (e q))) (.inr 3) * swap (.inl (.inl (e q))) (.inl (.inr 3)) *
        swap (.inl (.inl (e q))) (.inr 1) := by
  have hinv := he.apply_apply
  have hne := he.apply_ne
  have h₁ := apply_ne_self_of_ne he hqe
  have h₂ := apply_ne_apply_of_ne (e := e) hqp
  refine clasp_ext (e := e) (p := p) (q := q) ?_ ?_ ?_ ?_ (fun x hxp hxe hxq hxe' => ?_)
    (fun i => ?_) (fun i => ?_)
  all_goals (try fin_cases i) <;> simp [claspMatching_val_apply, claspFun, swap_apply_def,
    reconnect_self he hqp, reconnect_right he hqp, reconnect_apply_self he hqp,
    reconnect_apply_right he hqp, reconnect_of_ne he, hqp.symm, hqe.symm, h₁.symm, h₂.symm,
    (hne p).symm, (hne q).symm, *]
include he hqp hqe in
/-- Smoothing the first new crossing by `slotSmoothing false` and the second by
`slotSmoothing true` also joins `p` to `q` and `e p` to `e q`. -/
private theorem sumCongr_false_true_mul_claspMatching (T : Perm α) :
    Perm.sumCongr (Perm.sumCongr T (slotSmoothing false)) (slotSmoothing true) *
        (claspMatching e he p q hqp hqe).val =
      Perm.sumCongr (Perm.sumCongr (T * reconnect e p q) 1) 1 *
        swap (.inl (.inl p)) (.inl (.inr 1)) * swap (.inl (.inl p)) (.inr 1) *
        swap (.inl (.inl p)) (.inl (.inr 3)) *
        swap (.inl (.inl q)) (.inl (.inr 0)) * swap (.inl (.inl q)) (.inr 0) *
        swap (.inl (.inl q)) (.inl (.inr 2)) *
        swap (.inl (.inl (e p))) (.inr 2) * swap (.inl (.inl (e q))) (.inr 3) := by
  have hinv := he.apply_apply
  have hne := he.apply_ne
  have h₁ := apply_ne_self_of_ne he hqe
  have h₂ := apply_ne_apply_of_ne (e := e) hqp
  refine clasp_ext (e := e) (p := p) (q := q) ?_ ?_ ?_ ?_ (fun x hxp hxe hxq hxe' => ?_)
    (fun i => ?_) (fun i => ?_)
  all_goals (try fin_cases i) <;> simp [claspMatching_val_apply, claspFun, swap_apply_def,
    reconnect_self he hqp, reconnect_right he hqp, reconnect_apply_self he hqp,
    reconnect_apply_right he hqp, reconnect_of_ne he, hqp.symm, hqe.symm, h₁.symm, h₂.symm,
    (hne p).symm, (hne q).symm, *]
include he hqp hqe in
/-- Smoothing both new crossings by `slotSmoothing true` joins `p` to `q` and `e p` to `e q`, and
cuts off the circle through the two short arcs of the clasp. -/
private theorem sumCongr_true_true_mul_claspMatching (T : Perm α) :
    Perm.sumCongr (Perm.sumCongr T (slotSmoothing true)) (slotSmoothing true) *
        (claspMatching e he p q hqp hqe).val =
      Perm.sumCongr (Perm.sumCongr (T * reconnect e p q) 1) 1 *
        swap (.inl (.inl p)) (.inl (.inr 1)) * swap (.inl (.inl q)) (.inl (.inr 0)) *
        swap (.inl (.inl (e p))) (.inr 2) * swap (.inl (.inl (e q))) (.inr 3) *
        swap (.inl (.inr 2)) (.inr 0) * swap (.inl (.inr 3)) (.inr 1) := by
  have hinv := he.apply_apply
  have hne := he.apply_ne
  have h₁ := apply_ne_self_of_ne he hqe
  have h₂ := apply_ne_apply_of_ne (e := e) hqp
  refine clasp_ext (e := e) (p := p) (q := q) ?_ ?_ ?_ ?_ (fun x hxp hxe hxq hxe' => ?_)
    (fun i => ?_) (fun i => ?_)
  all_goals (try fin_cases i) <;> simp [claspMatching_val_apply, claspFun, swap_apply_def,
    reconnect_self he hqp, reconnect_right he hqp, reconnect_apply_self he hqp,
    reconnect_apply_right he hqp, reconnect_of_ne he, hqp.symm, hqe.symm, h₁.symm, h₂.symm,
    (hne p).symm, (hne q).symm, *]
omit [DecidableEq α] in
private theorem orbitCount_sumCongr_sumCongr_one [Finite α] (σ : Perm α) :
    orbitCount (Perm.sumCongr (Perm.sumCongr σ (1 : Perm (Fin 4))) (1 : Perm (Fin 4))) =
      orbitCount σ + 8 := by
  rw [Perm.orbitCount_sumCongr, Perm.orbitCount_sumCongr, orbitCount_one]
  simp

/-- Splicing a fixed point `b` into the orbit of `a` removes one orbit; this is
`TauCeti.orbitCount_mul_swap_add_one` in the form used to rewrite. -/
private theorem orbitCount_mul_swap_eq_sub_one {β : Type*} [DecidableEq β] [Finite β]
    {τ : Perm β} {a b : β} (hb : τ b = b) (hab : a ≠ b) :
    orbitCount (τ * swap a b) = orbitCount τ - 1 := by
  have := orbitCount_mul_swap_add_one hb hab
  omega

include he hqp hqe in
/-- **Orbits of a smoothed clasp.** Smoothing the two new crossings by `slotSmoothing x` and
`slotSmoothing y` leaves the orbits of the old traversal `T * e` when both are `false`, and
otherwise those of the reconnected traversal, two more when both are `true`. -/
private theorem orbitCount_slotSmoothing_mul_claspMatching [Finite α] (T : Perm α) (x y : Bool) :
    orbitCount (Perm.sumCongr (Perm.sumCongr T (slotSmoothing x)) (slotSmoothing y) *
        (claspMatching e he p q hqp hqe).val) =
      if x = false ∧ y = false then orbitCount (T * e)
      else orbitCount (T * reconnect e p q) + if x = true ∧ y = true then 2 else 0 := by
  cases x <;> cases y
  · rw [sumCongr_false_false_mul_claspMatching he hqp hqe]
    repeat rw [orbitCount_mul_swap_eq_sub_one]
    · rw [orbitCount_sumCongr_sumCongr_one]
      simp
    all_goals simp [swap_apply_def]
  · rw [sumCongr_false_true_mul_claspMatching he hqp hqe]
    repeat rw [orbitCount_mul_swap_eq_sub_one]
    · rw [orbitCount_sumCongr_sumCongr_one]
      simp
    all_goals simp [swap_apply_def]
  · rw [sumCongr_true_false_mul_claspMatching he hqp hqe]
    repeat rw [orbitCount_mul_swap_eq_sub_one]
    · rw [orbitCount_sumCongr_sumCongr_one]
      simp
    all_goals simp [swap_apply_def]
  · rw [sumCongr_true_true_mul_claspMatching he hqp hqe]
    repeat rw [orbitCount_mul_swap_eq_sub_one]
    · rw [orbitCount_sumCongr_sumCongr_one]
      simp
    all_goals simp [swap_apply_def]

include he hqp hqe in
/-- **Orbits of the clasp's strands.** Following the strands through the two new crossings leaves
the orbits of the old traversal `C * e`. -/
private theorem orbitCount_opposite_mul_claspMatching [Finite α] (C : Perm α) :
    orbitCount (Perm.sumCongr (Perm.sumCongr C oppositeCrossingSlot) oppositeCrossingSlot *
        (claspMatching e he p q hqp hqe).val) = orbitCount (C * e) := by
  rw [sumCongr_opposite_mul_claspMatching he hqp hqe]
  repeat rw [orbitCount_mul_swap_eq_sub_one]
  · rw [orbitCount_sumCongr_sumCongr_one]
    simp
  all_goals simp [swap_apply_def]

include he hqp hqe in
/-- Turning to the next slot counterclockwise at both new crossings restores the cut arcs up to
one exchange: it is the old traversal `T * e` with the images of `p` and `e q` exchanged and six
new slots spliced in, while the two remaining slots, `3` of the first crossing and `1` of the
second, form a cycle of their own. -/
private theorem sumCongr_finRotate_mul_claspMatching (T : Perm α) :
    Perm.sumCongr (Perm.sumCongr T (finRotate 4)) (finRotate 4) *
        (claspMatching e he p q hqp hqe).val =
      Perm.sumCongr (Perm.sumCongr (T * e) 1) 1 *
        swap (.inl (.inl p)) (.inl (.inl (e q))) * swap (.inl (.inl p)) (.inl (.inr 1)) *
        swap (.inl (.inl q)) (.inr 2) * swap (.inl (.inl q)) (.inl (.inr 2)) *
        swap (.inl (.inl (e q))) (.inr 3) *
        swap (.inl (.inl (e p))) (.inl (.inr 0)) * swap (.inl (.inl (e p))) (.inr 0) *
        swap (.inl (.inr 3)) (.inr 1) := by
  have hinv := he.apply_apply
  have hne := he.apply_ne
  have h₁ := apply_ne_self_of_ne he hqe
  have h₂ := apply_ne_apply_of_ne (e := e) hqp
  refine clasp_ext (e := e) (p := p) (q := q) ?_ ?_ ?_ ?_ (fun x hxp hxe hxq hxe' => ?_)
    (fun i => ?_) (fun i => ?_)
  all_goals (try fin_cases i) <;> simp [claspMatching_val_apply, claspFun, swap_apply_def,
    finRotate_apply, hqp.symm, hqe.symm, h₁.symm, h₂.symm, (hne p).symm, (hne q).symm, *]

include he hqp hqe in
/-- **Orbits of a rotated clasp.** Turning to the next slot at both new crossings, after the arcs
of the clasp, leaves the orbits of the old traversal `T * e`, two more when `p` and `e q` lie in
one of its orbits. -/
private theorem orbitCount_finRotate_mul_claspMatching [Finite α] (T : Perm α)
    [Decidable ((T * e).SameCycle p (e q))] :
    orbitCount (Perm.sumCongr (Perm.sumCongr T (finRotate 4)) (finRotate 4) *
        (claspMatching e he p q hqp hqe).val) =
      orbitCount (T * e) + if (T * e).SameCycle p (e q) then 2 else 0 := by
  rw [sumCongr_finRotate_mul_claspMatching he hqp hqe]
  rw [orbitCount_mul_swap_eq_sub_one, orbitCount_mul_swap_eq_sub_one,
    orbitCount_mul_swap_eq_sub_one, orbitCount_mul_swap_eq_sub_one,
    orbitCount_mul_swap_eq_sub_one, orbitCount_mul_swap_eq_sub_one,
    orbitCount_mul_swap_eq_sub_one]
  · have hcount := orbitCount_sumCongr_sumCongr_one (T * e)
    have hpq : (.inl (.inl p) : (α ⊕ Fin 4) ⊕ Fin 4) ≠ .inl (.inl (e q)) := by
      simpa using (apply_ne_self_of_ne he hqe).symm
    split_ifs with h
    · rw [orbitCount_mul_swap_of_sameCycle hpq
        (Perm.sameCycle_sumCongr_inl.mpr (Perm.sameCycle_sumCongr_inl.mpr h))]
      omega
    · have hn : ¬ (Perm.sumCongr (Perm.sumCongr (T * e) 1) 1).SameCycle
          (.inl (.inl p) : (α ⊕ Fin 4) ⊕ Fin 4) (.inl (.inl (e q))) := by
        rwa [Perm.sameCycle_sumCongr_inl, Perm.sameCycle_sumCongr_inl]
      have := orbitCount_mul_swap_add_one_of_not_sameCycle hn
      omega
  all_goals simp [swap_apply_def]

end Smoothing

end Clasp

/-- The half-edge positions of a code with two crossings more: the `4 * n` positions of the first
`n` crossings, followed by the slots of the two new crossings. -/
private def halfEdgeTwoSuccEquiv (n : ℕ) : (Fin (4 * n) ⊕ Fin 4) ⊕ Fin 4 ≃ Fin (4 * (n + 2)) :=
  (Equiv.sumCongr (halfEdgeSuccEquiv n) (Equiv.refl (Fin 4))).trans (halfEdgeSuccEquiv (n + 1))

private theorem halfEdgeTwoSuccEquiv_inl_inl (x : Fin (4 * n)) :
    halfEdgeTwoSuccEquiv n (.inl (.inl x)) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x))) := (rfl)

private theorem halfEdgeTwoSuccEquiv_inl_inr (slot : Fin 4) :
    halfEdgeTwoSuccEquiv n (.inl (.inr slot)) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr slot))) := (rfl)

private theorem halfEdgeTwoSuccEquiv_inr (slot : Fin 4) :
    halfEdgeTwoSuccEquiv n (.inr slot) = halfEdgeSuccEquiv (n + 1) (.inr slot) := (rfl)

/-- **Algebraic clasp insertion**: route the arc of `D` ending at the half-edge `p` and the
distinct arc ending at `q` through a two-crossing clasp. This operation carries no claim that the
two arcs border a common face. When the face at the far end `D.edgePair.val p` of the first arc is
the face at `q`, that is, `D.face (D.edgePair.val p) = D.face q`, it is the second Reidemeister
move (`TauCeti.PDCode.isPlanar_insertClasp_iff`); passing `D.edgePair.val q` instead of `q` uses
the other side of the second arc.
The two new crossings are `(Fin.last n).castSucc`, whose slots `0`
and `1` are joined to `p` and `q`, and `Fin.last (n + 1)`, whose slots `3` and `2` are joined to
the other ends `D.edgePair.val p` and `D.edgePair.val q` of the two arcs. Slot `2` of the first
new crossing is joined to slot `1` of the second along the first strand, and slot `3` to slot `0`
along the second. The over-pair indicators of the two new crossings are `b` and `!b`: with
`b = false` the strand through `p` is over at both, with `b = true` the strand through `q`. -/
def insertClasp (D : PDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p)
    (hqe : q ≠ D.edgePair.val p) : PDCode (n + 2) where
  halfEdge := (halfEdgeTwoSuccEquiv n).permCongr (Perm.sumCongr (Perm.sumCongr D.halfEdge 1) 1)
  edgePair := PerfectMatching.congr (halfEdgeTwoSuccEquiv n)
    (claspMatching D.edgePair.val D.edgePair.prop p q hqp hqe)
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := Fin.snoc (α := fun _ => Bool) (Fin.snoc (α := fun _ => Bool) D.overPair b) !b

variable (D : PDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p)

/-- The old crossings keep their half-edges. -/
@[simp] theorem insertClasp_crossing_castSucc_castSucc (i : Fin n) (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).halfEdge
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n
          (.inl (crossingSlotEquiv n (i, slot)))))) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.crossing i slot)))) := by
  rw [← halfEdgeTwoSuccEquiv_inl_inl, ← halfEdgeTwoSuccEquiv_inl_inl]
  simp [insertClasp, Equiv.permCongr_apply]

/-- The slots of the first new crossing are four of the new half-edges. -/
@[simp] theorem insertClasp_crossing_castSucc_last (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).halfEdge
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr slot)))) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr slot))) := by
  rw [← halfEdgeTwoSuccEquiv_inl_inr]
  simp [insertClasp, Equiv.permCongr_apply]

/-- The slots of the second new crossing are the last four half-edges. -/
@[simp] theorem insertClasp_crossing_last (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).halfEdge (halfEdgeSuccEquiv (n + 1) (.inr slot)) =
      halfEdgeSuccEquiv (n + 1) (.inr slot) := by
  rw [← halfEdgeTwoSuccEquiv_inr]
  simp [insertClasp, Equiv.permCongr_apply]

/-- The old crossings keep their over-strands. -/
@[simp] theorem insertClasp_overPair_castSucc_castSucc (i : Fin n) :
    (D.insertClasp p q b hqp hqe).overPair i.castSucc.castSucc = D.overPair i := by
  simp [insertClasp]

/-- The over-pair indicator of the first new crossing is `b`. -/
@[simp] theorem insertClasp_overPair_castSucc_last :
    (D.insertClasp p q b hqp hqe).overPair (Fin.last n).castSucc = b := by
  simp [insertClasp]

/-- The over-pair indicator of the second new crossing is `!b`, so the same strand is over at both
new crossings. -/
@[simp] theorem insertClasp_overPair_last :
    (D.insertClasp p q b hqp hqe).overPair (Fin.last (n + 1)) = !b := by
  simp [insertClasp]

/-- The insertion keeps the crossing-free circles. -/
@[simp] theorem insertClasp_crossinglessComponentCount :
    (D.insertClasp p q b hqp hqe).crossinglessComponentCount =
      D.crossinglessComponentCount := by
  simp [insertClasp]

private theorem insertClasp_edgePair_val :
    (D.insertClasp p q b hqp hqe).edgePair.val = (halfEdgeTwoSuccEquiv n).permCongr
      (claspMatching D.edgePair.val D.edgePair.prop p q hqp hqe).val := by
  simp [insertClasp, PerfectMatching.congr_val]

private theorem insertClasp_edgePair_apply (y : (Fin (4 * n) ⊕ Fin 4) ⊕ Fin 4) :
    (D.insertClasp p q b hqp hqe).edgePair.val (halfEdgeTwoSuccEquiv n y) =
      halfEdgeTwoSuccEquiv n (claspFun D.edgePair.val p q y) := by
  rw [insertClasp_edgePair_val, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    claspMatching_val_apply]

/-- Slot `0` of the first new crossing is joined to the half-edge `p`. -/
@[simp] theorem insertClasp_edgePair_inl_inr_zero :
    (D.insertClasp p q b hqp hqe).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 0)))) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl p))) := by
  rw [← halfEdgeTwoSuccEquiv_inl_inr, insertClasp_edgePair_apply]
  rfl

/-- Slot `1` of the first new crossing is joined to the half-edge `q`. -/
@[simp] theorem insertClasp_edgePair_inl_inr_one :
    (D.insertClasp p q b hqp hqe).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1)))) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl q))) := by
  rw [← halfEdgeTwoSuccEquiv_inl_inr, insertClasp_edgePair_apply]
  rfl

/-- Slot `2` of the first new crossing is joined to slot `1` of the second, along the strand
through `p`. -/
@[simp] theorem insertClasp_edgePair_inl_inr_two :
    (D.insertClasp p q b hqp hqe).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 2)))) =
      halfEdgeSuccEquiv (n + 1) (.inr 1) := by
  rw [← halfEdgeTwoSuccEquiv_inl_inr, insertClasp_edgePair_apply]
  rfl

/-- Slot `3` of the first new crossing is joined to slot `0` of the second, along the strand
through `q`. -/
@[simp] theorem insertClasp_edgePair_inl_inr_three :
    (D.insertClasp p q b hqp hqe).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 3)))) =
      halfEdgeSuccEquiv (n + 1) (.inr 0) := by
  rw [← halfEdgeTwoSuccEquiv_inl_inr, insertClasp_edgePair_apply]
  rfl

/-- Slot `0` of the second new crossing is joined to slot `3` of the first. -/
@[simp] theorem insertClasp_edgePair_inr_zero :
    (D.insertClasp p q b hqp hqe).edgePair.val (halfEdgeSuccEquiv (n + 1) (.inr 0)) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 3))) := by
  rw [← halfEdgeTwoSuccEquiv_inr, insertClasp_edgePair_apply]
  rfl

/-- Slot `1` of the second new crossing is joined to slot `2` of the first. -/
@[simp] theorem insertClasp_edgePair_inr_one :
    (D.insertClasp p q b hqp hqe).edgePair.val (halfEdgeSuccEquiv (n + 1) (.inr 1)) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 2))) := by
  rw [← halfEdgeTwoSuccEquiv_inr, insertClasp_edgePair_apply]
  rfl

/-- Slot `2` of the second new crossing is joined to the other end of the arc at `q`. -/
@[simp] theorem insertClasp_edgePair_inr_two :
    (D.insertClasp p q b hqp hqe).edgePair.val (halfEdgeSuccEquiv (n + 1) (.inr 2)) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.edgePair.val q)))) := by
  rw [← halfEdgeTwoSuccEquiv_inr, insertClasp_edgePair_apply]
  rfl

/-- Slot `3` of the second new crossing is joined to the other end of the arc at `p`. -/
@[simp] theorem insertClasp_edgePair_inr_three :
    (D.insertClasp p q b hqp hqe).edgePair.val (halfEdgeSuccEquiv (n + 1) (.inr 3)) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.edgePair.val p)))) := by
  rw [← halfEdgeTwoSuccEquiv_inr, insertClasp_edgePair_apply]
  rfl

/-- The half-edge `p` is joined to slot `0` of the first new crossing. -/
@[simp] theorem insertClasp_edgePair_inl_inl_self :
    (D.insertClasp p q b hqp hqe).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl p)))) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 0))) := by
  rw [← halfEdgeTwoSuccEquiv_inl_inl, insertClasp_edgePair_apply, claspFun_self]
  rfl

/-- The half-edge `q` is joined to slot `1` of the first new crossing. -/
@[simp] theorem insertClasp_edgePair_inl_inl_right :
    (D.insertClasp p q b hqp hqe).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl q)))) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1))) := by
  rw [← halfEdgeTwoSuccEquiv_inl_inl, insertClasp_edgePair_apply, claspFun_right hqp hqe]
  rfl

/-- The other end of the arc at `p` is joined to slot `3` of the second new crossing. -/
@[simp] theorem insertClasp_edgePair_inl_inl_apply_self :
    (D.insertClasp p q b hqp hqe).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.edgePair.val p))))) =
      halfEdgeSuccEquiv (n + 1) (.inr 3) := by
  rw [← halfEdgeTwoSuccEquiv_inl_inl, insertClasp_edgePair_apply,
    claspFun_apply_self D.edgePair.prop]
  rfl

/-- The other end of the arc at `q` is joined to slot `2` of the second new crossing. -/
@[simp] theorem insertClasp_edgePair_inl_inl_apply_right :
    (D.insertClasp p q b hqp hqe).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.edgePair.val q))))) =
      halfEdgeSuccEquiv (n + 1) (.inr 2) := by
  rw [← halfEdgeTwoSuccEquiv_inl_inl, insertClasp_edgePair_apply,
    claspFun_apply_right D.edgePair.prop hqp hqe]
  rfl

/-- Every half-edge off the two cut arcs keeps its old partner. -/
@[simp] theorem insertClasp_edgePair_inl_inl_of_ne {x : Fin (4 * n)} (hxp : x ≠ p)
    (hxe : x ≠ D.edgePair.val p) (hxq : x ≠ q) (hxe' : x ≠ D.edgePair.val q) :
    (D.insertClasp p q b hqp hqe).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.edgePair.val x)))) := by
  rw [← halfEdgeTwoSuccEquiv_inl_inl, insertClasp_edgePair_apply,
    claspFun_of_ne hxp hxe hxq hxe', halfEdgeTwoSuccEquiv_inl_inl]

/-- Mirroring the new code inserts the clasp with the other strand over into the mirror code. -/
@[simp] theorem mirror_insertClasp :
    (D.insertClasp p q b hqp hqe).mirror =
      D.mirror.insertClasp p q (!b) hqp (by rwa [mirror_edgePair]) := by
  apply PDCode.ext
  · simp [insertClasp]
  · simp [insertClasp]
  · simp [insertClasp]
  · funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => induction i using Fin.lastCases <;> simp

private theorem crossingwisePerm_insertClasp
    (oldTurn : Perm (Fin (4 * n))) (newTurn : Perm (Fin (4 * (n + 2))))
    (r : Fin (n + 2) → Perm (Fin 4))
    (oldTurn_crossing : ∀ i slot,
      oldTurn (D.halfEdge (crossingSlotEquiv n (i, slot))) =
        D.crossing i (r i.castSucc.castSucc slot))
    (newTurn_crossing : ∀ i slot,
      newTurn ((D.insertClasp p q b hqp hqe).halfEdge (crossingSlotEquiv (n + 2) (i, slot))) =
        (D.insertClasp p q b hqp hqe).crossing i (r i slot)) :
    newTurn = (halfEdgeTwoSuccEquiv n).permCongr (Perm.sumCongr
      (Perm.sumCongr oldTurn (r (Fin.last n).castSucc)) (r (Fin.last (n + 1)))) := by
  refine Equiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (halfEdgeTwoSuccEquiv n).surjective x
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rcases y with (y | slot) | slot
  · obtain ⟨z, rfl⟩ := D.halfEdge.surjective y
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective z
    have hx := D.insertClasp_crossing_castSucc_castSucc p q b hqp hqe i slot
    rw [crossing_apply, ← crossingSlotEquiv_succ_castSucc,
      ← crossingSlotEquiv_succ_castSucc] at hx
    rw [Perm.sumCongr_apply, Sum.map_inl, Perm.sumCongr_apply, Sum.map_inl, oldTurn_crossing,
      halfEdgeTwoSuccEquiv_inl_inl, halfEdgeTwoSuccEquiv_inl_inl, ← hx,
      newTurn_crossing, crossing_apply, crossingSlotEquiv_succ_castSucc,
      crossingSlotEquiv_succ_castSucc, insertClasp_crossing_castSucc_castSucc]
  · have hx : (D.insertClasp p q b hqp hqe).halfEdge
        (crossingSlotEquiv (n + 2) ((Fin.last n).castSucc, slot)) =
        halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr slot))) := by
      simpa only [crossingSlotEquiv_succ_castSucc, crossingSlotEquiv_succ_last] using
        D.insertClasp_crossing_castSucc_last p q b hqp hqe slot
    rw [Perm.sumCongr_apply, Sum.map_inl, Perm.sumCongr_apply, Sum.map_inr,
      halfEdgeTwoSuccEquiv_inl_inr, halfEdgeTwoSuccEquiv_inl_inr, ← hx,
      newTurn_crossing, crossing_apply, crossingSlotEquiv_succ_castSucc,
      crossingSlotEquiv_succ_last, insertClasp_crossing_castSucc_last]
  · have hx : (D.insertClasp p q b hqp hqe).halfEdge
        (crossingSlotEquiv (n + 2) (Fin.last (n + 1), slot)) =
        halfEdgeSuccEquiv (n + 1) (.inr slot) := by
      simpa only [crossingSlotEquiv_succ_last] using
        D.insertClasp_crossing_last p q b hqp hqe slot
    rw [Perm.sumCongr_apply, Sum.map_inr, halfEdgeTwoSuccEquiv_inr, halfEdgeTwoSuccEquiv_inr,
      ← hx, newTurn_crossing, crossing_apply, crossingSlotEquiv_succ_last,
      insertClasp_crossing_last]

private theorem smoothingTurn_insertClasp (c : Fin (n + 2) → Bool) :
    (D.insertClasp p q b hqp hqe).smoothingTurn c = (halfEdgeTwoSuccEquiv n).permCongr
      (Perm.sumCongr (Perm.sumCongr (D.smoothingTurn (Fin.init (Fin.init c)))
        (slotSmoothing (c (Fin.last n).castSucc))) (slotSmoothing (c (Fin.last (n + 1))))) := by
  apply crossingwisePerm_insertClasp D p q b hqp hqe _ _ (fun i => slotSmoothing (c i))
  · intro i slot
    simpa only [Fin.init_def] using D.smoothingTurn_crossing (Fin.init (Fin.init c)) i slot
  · exact (D.insertClasp p q b hqp hqe).smoothingTurn_crossing c

private theorem crossingTurn_insertClasp :
    (D.insertClasp p q b hqp hqe).crossingTurn = (halfEdgeTwoSuccEquiv n).permCongr
      (Perm.sumCongr (Perm.sumCongr D.crossingTurn oppositeCrossingSlot) oppositeCrossingSlot) := by
  apply crossingwisePerm_insertClasp D p q b hqp hqe _ _ (fun _ => oppositeCrossingSlot)
  · exact D.crossingTurn_crossing
  · exact (D.insertClasp p q b hqp hqe).crossingTurn_crossing

private theorem init_init_smoothingChoice_insertClasp (s : Fin (n + 2) → Bool) :
    Fin.init (Fin.init ((D.insertClasp p q b hqp hqe).smoothingChoice s)) =
      D.smoothingChoice (Fin.init (Fin.init s)) := by
  funext i
  cases hs : s i.castSucc.castSucc <;> simp [Fin.init, hs]

private theorem smoothingChoice_insertClasp_castSucc_last (s : Fin (n + 2) → Bool) :
    (D.insertClasp p q b hqp hqe).smoothingChoice s (Fin.last n).castSucc =
      (s (Fin.last n).castSucc == b) := by
  cases hs : s (Fin.last n).castSucc <;> cases b <;> simp [hs]

private theorem smoothingChoice_insertClasp_last (s : Fin (n + 2) → Bool) :
    (D.insertClasp p q b hqp hqe).smoothingChoice s (Fin.last (n + 1)) =
      (s (Fin.last (n + 1)) == !b) := by
  cases hs : s (Fin.last (n + 1)) <;> cases b <;> simp [hs]

/-- The number of circles left by a state of the old crossings once the two cut arcs are
reconnected, `p` to `q` and the other end of one to the other end of the other. -/
private noncomputable def claspLoopCount (s : Fin n → Bool) : ℕ :=
  orbitCount (D.smoothingTurn (D.smoothingChoice s) * reconnect D.edgePair.val p q) / 2 +
    D.crossinglessComponentCount

private theorem one_le_claspLoopCount (s : Fin n → Bool) : 1 ≤ claspLoopCount D p q s := by
  have hpos : 0 < orbitCount (D.smoothingTurn (D.smoothingChoice s) *
      reconnect D.edgePair.val p q) := by
    let _ : Nonempty (Fin (4 * n)) := ⟨p⟩
    exact Equiv.Perm.orbitCount_pos _
  obtain ⟨k, hk⟩ := (D.isPerfectMatching_smoothingTurn (D.smoothingChoice s)).even_orbitCount_mul
    (isPerfectMatching_reconnect D.edgePair.prop p q)
  rw [claspLoopCount]
  omega

/-- **Circles after clasp insertion.** A state of the new code whose choices at the
two new crossings smooth them back into the two cut arcs leaves as many circles as its restriction
to the old crossings. Every other state leaves the circles of the reconnected arcs, one more when
it also cuts off the circle through the two short arcs of the clasp. -/
private theorem stateLoopCount_insertClasp (s : Fin (n + 2) → Bool) :
    (D.insertClasp p q b hqp hqe).stateLoopCount s =
      if (s (Fin.last n).castSucc == b) = false ∧ (s (Fin.last (n + 1)) == !b) = false then
        D.stateLoopCount (Fin.init (Fin.init s))
      else claspLoopCount D p q (Fin.init (Fin.init s)) +
        if (s (Fin.last n).castSucc == b) = true ∧ (s (Fin.last (n + 1)) == !b) = true then 1
        else 0 := by
  rw [stateLoopCount_def, statePerm_def, smoothingTurn_insertClasp,
    init_init_smoothingChoice_insertClasp, smoothingChoice_insertClasp_castSucc_last,
    smoothingChoice_insertClasp_last, insertClasp_edgePair_val, ← Equiv.permCongr_mul,
    Equiv.orbitCount_permCongr, orbitCount_slotSmoothing_mul_claspMatching,
    insertClasp_crossinglessComponentCount]
  split_ifs <;> simp_all [stateLoopCount_def, statePerm_def, claspLoopCount]
  omega

/-- **Algebraic clasp insertion keeps the number of components.** -/
@[simp] theorem crossingComponentCount_insertClasp :
    (D.insertClasp p q b hqp hqe).crossingComponentCount = D.crossingComponentCount := by
  rw [crossingComponentCount_def, crossingComponentCount_def, componentPerm_def,
    componentPerm_def, crossingTurn_insertClasp, insertClasp_edgePair_val,
    ← Equiv.permCongr_mul, Equiv.orbitCount_permCongr, orbitCount_opposite_mul_claspMatching]

/-- **The Kauffman bracket is invariant under algebraic clasp insertion.** -/
@[simp] theorem kauffmanBracket_insertClasp {R : Type*} [CommRing R] (a : Rˣ) :
    (D.insertClasp p q b hqp hqe).kauffmanBracket a = D.kauffmanBracket a := by
  -- Split each state of the new code into a state of the old code and the choices at the two
  -- new crossings, and compare the four resulting terms with one term of the old bracket.
  rw [kauffmanBracket_def, kauffmanBracket_def,
    ← ((Equiv.prodCongr (Equiv.refl Bool) (Fin.snocEquiv fun _ => Bool)).trans
      (Fin.snocEquiv fun _ => Bool)).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨k, hk⟩ : ∃ k, claspLoopCount D p q s = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (one_le_claspLoopCount D p q s)).symm⟩
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map_apply,
    Fin.snocEquiv, Equiv.coe_fn_mk, stateLoopCount_insertClasp, Fin.init_snoc,
    Fin.snoc_castSucc, Fin.snoc_last, stateWeight_snoc, hk]
  cases b <;> simp only [Bool.cond_true, Bool.cond_false, Bool.not_true, Bool.not_false,
    Bool.true_beq, Bool.false_beq, Bool.true_eq_false, Bool.false_eq_true, and_self, and_false,
    and_true, ↓reduceIte, Nat.add_sub_cancel, add_zero, Units.val_mul, pow_succ, jonesDelta_def] <;>
  linear_combination ((stateWeight s a : R) * (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)) ^
    (D.stateLoopCount s - 1) - (stateWeight s a : R) * ((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2) *
      (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)) ^ k) * a.mul_inv

/-! ### Faces after clasp insertion -/

private theorem crossingRotation_insertClasp :
    (D.insertClasp p q b hqp hqe).crossingRotation = (halfEdgeTwoSuccEquiv n).permCongr
      (Perm.sumCongr (Perm.sumCongr D.crossingRotation (finRotate 4)) (finRotate 4)) := by
  apply crossingwisePerm_insertClasp D p q b hqp hqe _ _ (fun _ => finRotate 4)
  · intro i slot
    rw [crossingRotation_crossing, finRotate_apply]
  · intro i slot
    rw [crossingRotation_crossing, finRotate_apply]

private theorem faceCount_insertClasp_eq_ite
    [Decidable ((D.crossingRotation * D.edgePair.val).SameCycle p (D.edgePair.val q))] :
    (D.insertClasp p q b hqp hqe).faceCount = D.faceCount +
      if (D.crossingRotation * D.edgePair.val).SameCycle p (D.edgePair.val q) then 2 else 0 := by
  rw [faceCount_def, facePerm_def, crossingRotation_insertClasp, insertClasp_edgePair_val,
    ← Equiv.permCongr_mul, Equiv.orbitCount_permCongr, ← orbitCount_conj
      (Perm.sumCongr (Perm.sumCongr D.crossingRotation (finRotate 4)) (finRotate 4)),
    mul_assoc, mul_assoc, mul_inv_cancel, mul_one, orbitCount_finRotate_mul_claspMatching,
    faceCount_eq_orbitCount_crossingRotation_mul_edgePair]

/-- **Clasp insertion inside a face adds two faces.** When the face at the far end
`D.edgePair.val p` of the arc ending at `p` is the face at `q`, the clasp can be drawn inside that
face: it cuts the face in two and adds the bigon between its two crossings. -/
theorem faceCount_insertClasp_of_face_eq (hface : D.face (D.edgePair.val p) = D.face q) :
    (D.insertClasp p q b hqp hqe).faceCount = D.faceCount + 2 := by
  classical
  have h : (D.crossingRotation * D.edgePair.val).SameCycle p (D.edgePair.val q) := by
    rwa [D.sameCycle_crossingRotation_mul_edgePair_iff, D.edgePair.prop.apply_apply]
  simp only [faceCount_insertClasp_eq_ite, h, ↓reduceIte]

/-- When the face at the far end `D.edgePair.val p` of the arc ending at `p` is not the face at
`q`, inserting the clasp joins two faces into one, which the bigon between the two new crossings
makes up for: the number of faces is unchanged. -/
theorem faceCount_insertClasp_of_face_ne (hface : D.face (D.edgePair.val p) ≠ D.face q) :
    (D.insertClasp p q b hqp hqe).faceCount = D.faceCount := by
  classical
  have h : ¬ (D.crossingRotation * D.edgePair.val).SameCycle p (D.edgePair.val q) := by
    rwa [D.sameCycle_crossingRotation_mul_edgePair_iff, D.edgePair.prop.apply_apply]
  simp only [faceCount_insertClasp_eq_ite, h, ↓reduceIte, add_zero]

/-! ### Connected components after clasp insertion -/

private theorem crossingRotation_insertClasp_apply (z : (Fin (4 * n) ⊕ Fin 4) ⊕ Fin 4) :
    (D.insertClasp p q b hqp hqe).crossingRotation (halfEdgeTwoSuccEquiv n z) =
      halfEdgeTwoSuccEquiv n
        (Perm.sumCongr (Perm.sumCongr D.crossingRotation (finRotate 4)) (finRotate 4) z) := by
  rw [crossingRotation_insertClasp, Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- The connected component of the new code containing a half-edge, given as an old half-edge or
a slot of a new crossing. -/
private def claspOrbit (z : (Fin (4 * n) ⊕ Fin 4) ⊕ Fin 4) :
    (D.insertClasp p q b hqp hqe).toPermutationTriple.MonodromyOrbit :=
  Quotient.mk _ (halfEdgeTwoSuccEquiv n z)

private theorem claspOrbit_sumCongr (z : (Fin (4 * n) ⊕ Fin 4) ⊕ Fin 4) :
    claspOrbit D p q b hqp hqe
        (Perm.sumCongr (Perm.sumCongr D.crossingRotation (finRotate 4)) (finRotate 4) z) =
      claspOrbit D p q b hqp hqe z := by
  unfold claspOrbit
  rw [← crossingRotation_insertClasp_apply, ← toPermutationTriple_σ0]
  exact PermutationTriple.mk_σ0_apply _ _

private theorem claspOrbit_claspFun (z : (Fin (4 * n) ⊕ Fin 4) ⊕ Fin 4) :
    claspOrbit D p q b hqp hqe (claspFun D.edgePair.val p q z) = claspOrbit D p q b hqp hqe z := by
  unfold claspOrbit
  rw [← insertClasp_edgePair_apply, ← toPermutationTriple_σ1]
  exact PermutationTriple.mk_σ1_apply _ _

/-- A function on the slots of a crossing unchanged by turning to the next slot is constant. -/
private theorem apply_eq_apply_zero_of_add_one {β : Type*} {f : Fin 4 → β}
    (h : ∀ i, f (i + 1) = f i) (i : Fin 4) : f i = f 0 := by
  have h1 : f 1 = f 0 := h 0
  have h2 : f 2 = f 0 := (h 1).trans h1
  have h3 : f 3 = f 0 := (h 2).trans h2
  fin_cases i
  · rfl
  · exact h1
  · exact h2
  · exact h3

/-- The two new crossings and the ends of the two cut arcs all lie in one connected component of
the new code. -/
private theorem claspOrbit_eq_inl_inr_zero :
    (∀ i, claspOrbit D p q b hqp hqe (.inl (.inr i)) =
      claspOrbit D p q b hqp hqe (.inl (.inr 0))) ∧
    (∀ i, claspOrbit D p q b hqp hqe (.inr i) = claspOrbit D p q b hqp hqe (.inl (.inr 0))) ∧
    (∀ x, x = p ∨ x = D.edgePair.val p ∨ x = q ∨ x = D.edgePair.val q →
      claspOrbit D p q b hqp hqe (.inl (.inl x)) = claspOrbit D p q b hqp hqe (.inl (.inr 0))) := by
  have hR := claspOrbit_sumCongr D p q b hqp hqe
  have hE := claspOrbit_claspFun D p q b hqp hqe
  have hu : ∀ i : Fin 4, claspOrbit D p q b hqp hqe (.inl (.inr (i + 1))) =
      claspOrbit D p q b hqp hqe (.inl (.inr i)) := fun i => by
    simpa [finRotate_apply] using hR (.inl (.inr i))
  have hv : ∀ i : Fin 4, claspOrbit D p q b hqp hqe (.inr (i + 1)) =
      claspOrbit D p q b hqp hqe (.inr i) := fun i => by
    simpa [finRotate_apply] using hR (.inr i)
  have hu' : ∀ i, claspOrbit D p q b hqp hqe (.inl (.inr i)) =
      claspOrbit D p q b hqp hqe (.inl (.inr 0)) :=
    apply_eq_apply_zero_of_add_one (f := fun i => claspOrbit D p q b hqp hqe (.inl (.inr i))) hu
  have hv0 : claspOrbit D p q b hqp hqe (.inr 0) = claspOrbit D p q b hqp hqe (.inl (.inr 0)) := by
    rw [← hu' 3]
    simpa [claspFun] using (hE (.inr 0)).symm
  have hv' : ∀ i, claspOrbit D p q b hqp hqe (.inr i) =
      claspOrbit D p q b hqp hqe (.inl (.inr 0)) := fun i =>
    (apply_eq_apply_zero_of_add_one (f := fun i => claspOrbit D p q b hqp hqe (.inr i)) hv i).trans
      hv0
  refine ⟨hu', hv', ?_⟩
  rintro x (rfl | rfl | rfl | rfl)
  · simpa [claspFun] using hE (.inl (.inr 0))
  · rw [← hv' 3]
    simpa [claspFun] using hE (.inr 3)
  · rw [← hu' 1]
    simpa [claspFun] using hE (.inl (.inr 1))
  · rw [← hv' 2]
    simpa [claspFun] using hE (.inr 2)

/-- The connected component of `D` containing an old half-edge, or that of `p` for a slot of a
new crossing. -/
private def oldOrbit : (Fin (4 * n) ⊕ Fin 4) ⊕ Fin 4 → D.toPermutationTriple.MonodromyOrbit :=
  Sum.elim (Sum.elim (Quotient.mk _) fun _ => Quotient.mk _ p) fun _ => Quotient.mk _ p

private theorem oldOrbit_inl_inl (x : Fin (4 * n)) :
    oldOrbit D p (.inl (.inl x)) = Quotient.mk _ x := (rfl)

private theorem oldOrbit_inl_inr (i : Fin 4) : oldOrbit D p (.inl (.inr i)) = Quotient.mk _ p :=
  (rfl)

private theorem oldOrbit_inr (i : Fin 4) : oldOrbit D p (.inr i) = Quotient.mk _ p := (rfl)

private theorem oldOrbit_sumCongr (z : (Fin (4 * n) ⊕ Fin 4) ⊕ Fin 4) :
    oldOrbit D p
        (Perm.sumCongr (Perm.sumCongr D.crossingRotation (finRotate 4)) (finRotate 4) z) =
      oldOrbit D p z := by
  rcases z with (x | i) | i
  · rw [Perm.sumCongr_apply, Sum.map_inl, Perm.sumCongr_apply, Sum.map_inl, oldOrbit_inl_inl,
      oldOrbit_inl_inl, ← toPermutationTriple_σ0, PermutationTriple.mk_σ0_apply]
  · rw [Perm.sumCongr_apply, Sum.map_inl, Perm.sumCongr_apply, Sum.map_inr, oldOrbit_inl_inr,
      oldOrbit_inl_inr]
  · rw [Perm.sumCongr_apply, Sum.map_inr, oldOrbit_inr, oldOrbit_inr]

include hqp hqe in
private theorem oldOrbit_claspFun
    (hpq : q ∈ MulAction.orbit D.toPermutationTriple.monodromyGroup p)
    (z : (Fin (4 * n) ⊕ Fin 4) ⊕ Fin 4) :
    oldOrbit D p (claspFun D.edgePair.val p q z) = oldOrbit D p z := by
  have hq : (Quotient.mk _ q : D.toPermutationTriple.MonodromyOrbit) = Quotient.mk _ p :=
    Quotient.sound hpq
  have he (x : Fin (4 * n)) :
      (Quotient.mk _ (D.edgePair.val x) : D.toPermutationTriple.MonodromyOrbit) =
        Quotient.mk _ x := by
    simpa only [toPermutationTriple_σ1] using D.toPermutationTriple.mk_σ1_apply x
  rcases z with (x | i) | i
  · by_cases hxp : x = p
    · subst hxp
      rw [claspFun_self, oldOrbit_inl_inr, oldOrbit_inl_inl]
    by_cases hxe : x = D.edgePair.val p
    · subst hxe
      rw [claspFun_apply_self D.edgePair.prop, oldOrbit_inr, oldOrbit_inl_inl, he]
    by_cases hxq : x = q
    · subst hxq
      rw [claspFun_right hqp hqe, oldOrbit_inl_inr, oldOrbit_inl_inl, hq]
    by_cases hxe' : x = D.edgePair.val q
    · subst hxe'
      rw [claspFun_apply_right D.edgePair.prop hqp hqe, oldOrbit_inr, oldOrbit_inl_inl, he, hq]
    rw [claspFun_of_ne hxp hxe hxq hxe', oldOrbit_inl_inl, oldOrbit_inl_inl, he]
  · fin_cases i <;> simp [claspFun, oldOrbit_inl_inl, oldOrbit_inl_inr, oldOrbit_inr, hq]
  · fin_cases i <;> simp [claspFun, oldOrbit_inl_inl, oldOrbit_inl_inr, oldOrbit_inr, hq, he]

/-- **Clasp insertion keeps the connected components** of the underlying graph when the two cut
arcs already lie in one component. -/
theorem card_monodromyOrbit_insertClasp
    (hpq : q ∈ MulAction.orbit D.toPermutationTriple.monodromyGroup p) :
    Nat.card (D.insertClasp p q b hqp hqe).toPermutationTriple.MonodromyOrbit =
      Nat.card D.toPermutationTriple.MonodromyOrbit := by
  -- The components correspond: a component of the new code containing an old half-edge goes to
  -- the component of `D` containing it, and the component of the clasp to that of `p`. Both maps
  -- are constant along the crossing rotation and the arc matching, which is checked on old
  -- half-edges and new slots, and they are inverse to each other.
  obtain ⟨hu, hv, hends⟩ := claspOrbit_eq_inl_inr_zero D p q b hqp hqe
  refine Nat.card_congr
    { toFun := Quotient.lift (fun y => oldOrbit D p ((halfEdgeTwoSuccEquiv n).symm y)) ?_
      invFun := Quotient.lift (fun x => claspOrbit D p q b hqp hqe (.inl (.inl x))) ?_
      left_inv := Quotient.ind fun y => ?_
      right_inv := Quotient.ind fun x => ?_ }
  · rintro _ y ⟨⟨σ, hσ⟩, rfl⟩
    refine PermutationTriple.apply_eq_of_mem_monodromyGroup _
      (f := fun y => oldOrbit D p ((halfEdgeTwoSuccEquiv n).symm y)) (fun y => ?_) (fun y => ?_) hσ
      y
    · obtain ⟨z, rfl⟩ := (halfEdgeTwoSuccEquiv n).surjective y
      rw [toPermutationTriple_σ0, crossingRotation_insertClasp_apply, symm_apply_apply,
        symm_apply_apply, oldOrbit_sumCongr]
    · obtain ⟨z, rfl⟩ := (halfEdgeTwoSuccEquiv n).surjective y
      rw [toPermutationTriple_σ1, insertClasp_edgePair_apply, symm_apply_apply,
        symm_apply_apply, oldOrbit_claspFun D p q hqp hqe hpq]
  · rintro _ x ⟨⟨σ, hσ⟩, rfl⟩
    refine PermutationTriple.apply_eq_of_mem_monodromyGroup _
      (f := fun x => claspOrbit D p q b hqp hqe (.inl (.inl x))) (fun x => ?_) (fun x => ?_) hσ x
    · simpa [toPermutationTriple_σ0] using claspOrbit_sumCongr D p q b hqp hqe (.inl (.inl x))
    · rw [toPermutationTriple_σ1]
      by_cases hx : x = p ∨ x = D.edgePair.val p ∨ x = q ∨ x = D.edgePair.val q
      · rw [hends x hx, hends]
        rcases hx with rfl | rfl | rfl | rfl
        · simp
        · simp [D.edgePair.prop.apply_apply]
        · simp
        · simp [D.edgePair.prop.apply_apply]
      · simp only [not_or] at hx
        obtain ⟨hxp, hxe, hxq, hxe'⟩ := hx
        have h := claspOrbit_claspFun D p q b hqp hqe (.inl (.inl x))
        rwa [claspFun_of_ne hxp hxe hxq hxe'] at h
  · obtain ⟨z, rfl⟩ := (halfEdgeTwoSuccEquiv n).surjective y
    simp only [Quotient.lift_mk, symm_apply_apply]
    rcases z with (x | i) | i
    · rw [oldOrbit_inl_inl, Quotient.lift_mk, claspOrbit]
    · rw [oldOrbit_inl_inr, Quotient.lift_mk]
      exact (hends p (.inl rfl)).trans (hu i).symm
    · rw [oldOrbit_inr, Quotient.lift_mk]
      exact (hends p (.inl rfl)).trans (hv i).symm
  · simp only [claspOrbit, Quotient.lift_mk, symm_apply_apply, oldOrbit_inl_inl]

/-- **Clasp insertion inside a face keeps planarity.** When the face at the far end
`D.edgePair.val p` of the arc ending at `p` is the face at `q`, the clasp insertion is the second
Reidemeister move drawn inside that face, and the new code is planar exactly when `D` is. -/
theorem isPlanar_insertClasp_iff (hface : D.face (D.edgePair.val p) = D.face q) :
    (D.insertClasp p q b hqp hqe).IsPlanar ↔ D.IsPlanar := by
  rw [isPlanar_iff_faceCount_eq, isPlanar_iff_faceCount_eq,
    faceCount_insertClasp_of_face_eq D p q b hqp hqe hface,
    card_monodromyOrbit_insertClasp D p q b hqp hqe (D.mem_orbit_of_face_edgePair_eq_face hface)]
  omega

/-- **The face condition is necessary.** When the two cut arcs lie in one connected component of
the underlying graph but the face at the far end `D.edgePair.val p` of the arc ending at `p` is not
the face at `q`, the clasp cannot be drawn in the plane: the new code is never planar. -/
theorem not_isPlanar_insertClasp_of_face_ne (hface : D.face (D.edgePair.val p) ≠ D.face q)
    (hpq : q ∈ MulAction.orbit D.toPermutationTriple.monodromyGroup p) :
    ¬ (D.insertClasp p q b hqp hqe).IsPlanar := by
  rw [isPlanar_iff_faceCount_eq, faceCount_insertClasp_of_face_ne D p q b hqp hqe hface,
    card_monodromyOrbit_insertClasp D p q b hqp hqe hpq]
  have := D.faceCount_le
  omega

end PDCode

end TauCeti
