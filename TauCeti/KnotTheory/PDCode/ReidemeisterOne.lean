/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Kauffman
import Mathlib.Tactic.LinearCombination
import TauCeti.GroupTheory.Perm.SumCongr

/-!
# The first Reidemeister move on PD-codes

The first Reidemeister move adds a kink to an arc of a diagram: the arc is cut open and a small
loop crossing itself once is spliced in. On a PD-code with `n` crossings,
`TauCeti.PDCode.reidemeisterOne D h b` adds this kink to the arc ending at the half-edge `h`. The
new crossing is the last one, `Fin.last n`, and its four slots take the last four half-edge
positions (`TauCeti.PDCode.halfEdgeSuccEquiv`). Slot `0` is joined to `h`, slot `1` to the other
end of the old arc, and slots `2` and `3` to each other. So the strand coming from `h` enters at
slot `0`, leaves through slot `2`, comes back round the loop into slot `3`, and leaves through
slot `1`. The Boolean `b` is the over-pair indicator of the new crossing. With `b = true` the
crossing looks like the one of `TauCeti.PDCode.kink`, which is the kink added to a crossing-free
circle instead.

The move keeps the number of components. A state of the new code leaves the circles of its
restriction to the old crossings, plus one more exactly when its smoothing at the new crossing joins
slot `2` to slot `3` and so cuts the loop off; the other smoothing runs along the kink. That first
smoothing is the `A`-smoothing when `b = true` and the `B`-smoothing when `b = false`, so the
Kauffman bracket gets multiplied by `a * δ + a⁻¹ = -a ^ 3` when `b = true` and by
`a + a⁻¹ * δ = -a⁻¹ ^ 3` when `b = false`, where `δ = -(a ^ 2 + a⁻¹ ^ 2)`. Up to this framing factor
the bracket is invariant under the first Reidemeister move. The writhe of an oriented code corrects
that factor, and the second and third moves leave the bracket unchanged; neither is treated here.

## Main definitions

* `TauCeti.PDCode.reidemeisterOne`: add a kink to an arc of a PD-code.

## Main results

* `TauCeti.PDCode.stateLoopCount_reidemeisterOne`: a state of the new code leaves one circle more
  than its restriction to the old crossings exactly when it cuts off the loop of the kink.
* `TauCeti.PDCode.crossingComponentCount_reidemeisterOne`: the move keeps the number of
  components.
* `TauCeti.PDCode.kauffmanBracket_reidemeisterOne`: the move multiplies the Kauffman bracket by
  `-a ^ 3` or `-a⁻¹ ^ 3`, depending on the crossing it adds.
* `TauCeti.PDCode.mirror_reidemeisterOne`: mirroring the new code adds the mirror kink to the
  mirror code.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1 (the
  Reidemeister moves) and Chapter 3 (the bracket under the Reidemeister moves).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2-3 (the PD convention).
-/

public section

namespace TauCeti

open Equiv Equiv.Perm TemperleyLieb

namespace PDCode

variable {n : ℕ}

section Kink

/-! ### The arcs of a kink, on the sum of the old half-edges and the new slots

A kink's arcs are built as a permutation of `α ⊕ Fin 4`: `α` holds the old half-edges and
`Fin 4` the four slots of the new crossing. With `e` the old arcs and `h` a half-edge, the
arc from `h` to `e h` is cut and spliced through the slots. This helper and the orbit counts
below serve only the proofs in this file. -/

variable {α : Type*} [DecidableEq α] {e : Perm α} {h : α}

/-- The arcs of the code with a kink added at `h`: slot `0` is joined to `h`, slot `1` to `e h`,
slot `2` to slot `3`, and every other half-edge to its old partner. It is `e` together with the
arcs `0`-`1` and `2`-`3` of `TauCeti.PDCode.kink`, conjugated by the transposition of `e h` with
slot `0`. -/
private def kinkPerm (e : Perm α) (h : α) : Perm (α ⊕ Fin 4) :=
  swap (.inl (e h)) (.inr 0) * Perm.sumCongr e (slotSmoothing true) * swap (.inl (e h)) (.inr 0)

private theorem kinkPerm_inl_self (hne : e h ≠ h) : kinkPerm e h (.inl h) = .inr 0 := by
  simp [kinkPerm, swap_apply_of_ne_of_ne, Ne.symm hne]

private theorem kinkPerm_inr_zero (he : e (e h) = h) (hne : e h ≠ h) :
    kinkPerm e h (.inr 0) = .inl h := by
  simp [kinkPerm, swap_apply_of_ne_of_ne, he, Ne.symm hne]

private theorem kinkPerm_inl_apply_self : kinkPerm e h (.inl (e h)) = .inr 1 := by
  simp [kinkPerm, swap_apply_of_ne_of_ne]

private theorem kinkPerm_inr_one : kinkPerm e h (.inr 1) = .inl (e h) := by
  simp [kinkPerm, swap_apply_of_ne_of_ne]

private theorem kinkPerm_inr_two : kinkPerm e h (.inr 2) = .inr 3 := by
  simp [kinkPerm, swap_apply_of_ne_of_ne]

private theorem kinkPerm_inr_three : kinkPerm e h (.inr 3) = .inr 2 := by
  simp [kinkPerm, swap_apply_of_ne_of_ne]

private theorem kinkPerm_inl_of_ne {x : α} (hx : x ≠ h) (hx' : x ≠ e h) :
    kinkPerm e h (.inl x) = .inl (e x) := by
  have h₁ : e x ≠ e h := fun hxh => hx (e.injective hxh)
  simp [kinkPerm, swap_apply_of_ne_of_ne, hx', h₁]

/-- The `A`-type smoothing `slotSmoothing true` at the new crossing, after the arcs of the kink,
is the old traversal `T * e` with slot `1` spliced in after `h`, slot `0` after `e h`, and slots
`2` and `3` left as fixed points: the loop has been cut off. -/
private theorem sumCongr_slotSmoothing_true_mul_kinkPerm (he : e (e h) = h) (hne : e h ≠ h)
    (T : Perm α) :
    Perm.sumCongr T (slotSmoothing true) * kinkPerm e h =
      Perm.sumCongr (T * e) 1 * swap (.inl h) (.inr 1) * swap (.inl (e h)) (.inr 0) := by
  ext x
  rcases x with x | t
  · by_cases hx : x = h
    · subst hx
      simp [kinkPerm_inl_self hne, swap_apply_of_ne_of_ne, Ne.symm hne]
    by_cases hx' : x = e h
    · subst hx'
      simp [kinkPerm_inl_apply_self, swap_apply_of_ne_of_ne]
    simp [kinkPerm_inl_of_ne hx hx', swap_apply_of_ne_of_ne, hx, hx']
  · fin_cases t
    · simp [kinkPerm_inr_zero he hne, swap_apply_of_ne_of_ne, hne, he]
    · simp [kinkPerm_inr_one, swap_apply_of_ne_of_ne]
    · simp [kinkPerm_inr_two, swap_apply_of_ne_of_ne]
    · simp [kinkPerm_inr_three, swap_apply_of_ne_of_ne]

/-- The other smoothing `slotSmoothing false` at the new crossing, after the arcs of the kink, is
the old traversal `T * e` with all four slots spliced in along it. -/
private theorem sumCongr_slotSmoothing_false_mul_kinkPerm (he : e (e h) = h) (hne : e h ≠ h)
    (T : Perm α) :
    Perm.sumCongr T (slotSmoothing false) * kinkPerm e h =
      Perm.sumCongr (T * e) 1 * swap (.inl h) (.inr 1) * swap (.inl h) (.inr 3) *
        swap (.inl (e h)) (.inr 0) * swap (.inl (e h)) (.inr 2) := by
  ext x
  rcases x with x | t
  · by_cases hx : x = h
    · subst hx
      simp [kinkPerm_inl_self hne, swap_apply_of_ne_of_ne, Ne.symm hne]
    by_cases hx' : x = e h
    · subst hx'
      simp [kinkPerm_inl_apply_self, swap_apply_of_ne_of_ne]
    simp [kinkPerm_inl_of_ne hx hx', swap_apply_of_ne_of_ne, hx, hx']
  · fin_cases t
    · simp [kinkPerm_inr_zero he hne, swap_apply_of_ne_of_ne, hne, he]
    · simp [kinkPerm_inr_one, swap_apply_of_ne_of_ne]
    · simp [kinkPerm_inr_two, swap_apply_of_ne_of_ne]
    · simp [kinkPerm_inr_three, swap_apply_of_ne_of_ne]

/-- Following the strands through the new crossing, after the arcs of the kink, is the old
component traversal `T * e` with all four slots spliced in along it. -/
private theorem sumCongr_oppositeCrossingSlot_mul_kinkPerm (he : e (e h) = h) (hne : e h ≠ h)
    (T : Perm α) :
    Perm.sumCongr T oppositeCrossingSlot * kinkPerm e h =
      Perm.sumCongr (T * e) 1 * swap (.inl h) (.inr 1) * swap (.inl h) (.inr 2) *
        swap (.inl (e h)) (.inr 0) * swap (.inl (e h)) (.inr 3) := by
  ext x
  rcases x with x | t
  · by_cases hx : x = h
    · subst hx
      simp [kinkPerm_inl_self hne, swap_apply_of_ne_of_ne, Ne.symm hne, Fin.ext_iff]
    by_cases hx' : x = e h
    · subst hx'
      simp [kinkPerm_inl_apply_self, swap_apply_of_ne_of_ne, Fin.ext_iff]
    simp [kinkPerm_inl_of_ne hx hx', swap_apply_of_ne_of_ne, hx, hx']
  · fin_cases t
    · simp [kinkPerm_inr_zero he hne, swap_apply_of_ne_of_ne, hne, he]
    · simp [kinkPerm_inr_one, swap_apply_of_ne_of_ne]
    · simp [kinkPerm_inr_two, swap_apply_of_ne_of_ne, Fin.ext_iff]
    · simp [kinkPerm_inr_three, swap_apply_of_ne_of_ne, Fin.ext_iff]

omit [DecidableEq α] in
private theorem orbitCount_sumCongr_one [Finite α] (σ : Perm α) :
    orbitCount (Perm.sumCongr σ (1 : Perm (Fin 4))) = orbitCount σ + 4 := by
  rw [Perm.orbitCount_sumCongr, orbitCount_one, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Splicing two of four adjoined fixed points into the orbits of `σ` leaves two orbits more
than `σ` has. -/
private theorem orbitCount_splice_two [Finite α] (σ : Perm α) (x y : α) :
    orbitCount (Perm.sumCongr σ (1 : Perm (Fin 4)) * swap (.inl x) (.inr 1) *
      swap (.inl y) (.inr 0)) = orbitCount σ + 2 := by
  have h₁ := orbitCount_mul_swap_add_one (τ := Perm.sumCongr σ (1 : Perm (Fin 4)))
    (p := .inr 1) (a := .inl x) (by simp) (by simp)
  have h₂ := orbitCount_mul_swap_add_one
    (τ := Perm.sumCongr σ (1 : Perm (Fin 4)) * swap (.inl x) (.inr 1))
    (p := .inr 0) (a := .inl y) (by simp [swap_apply_of_ne_of_ne]) (by simp)
  have h₀ := orbitCount_sumCongr_one σ
  omega

/-- Splicing all four adjoined fixed points into the orbits of `σ` leaves as many orbits as `σ`
has. -/
private theorem orbitCount_splice_four [Finite α] (σ : Perm α) (x y : α) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    orbitCount (Perm.sumCongr σ 1 * swap (.inl x) (.inr i) * swap (.inl x) (.inr j) *
      swap (.inl y) (.inr k) * swap (.inl y) (.inr l)) = orbitCount σ := by
  have h₁ := orbitCount_mul_swap_add_one (τ := Perm.sumCongr σ (1 : Perm (Fin 4)))
    (p := .inr i) (a := .inl x) (by simp) (by simp)
  have h₂ := orbitCount_mul_swap_add_one
    (τ := Perm.sumCongr σ (1 : Perm (Fin 4)) * swap (.inl x) (.inr i))
    (p := .inr j) (a := .inl x) (by simp [swap_apply_of_ne_of_ne, Ne.symm hij]) (by simp)
  have h₃ := orbitCount_mul_swap_add_one
    (τ := Perm.sumCongr σ (1 : Perm (Fin 4)) * swap (.inl x) (.inr i) * swap (.inl x) (.inr j))
    (p := .inr k) (a := .inl y)
    (by simp [swap_apply_of_ne_of_ne, Ne.symm hik, Ne.symm hjk]) (by simp)
  have h₄ := orbitCount_mul_swap_add_one
    (τ := Perm.sumCongr σ (1 : Perm (Fin 4)) * swap (.inl x) (.inr i) * swap (.inl x) (.inr j) *
      swap (.inl y) (.inr k))
    (p := .inr l) (a := .inl y)
    (by simp [swap_apply_of_ne_of_ne, Ne.symm hil, Ne.symm hjl, Ne.symm hkl]) (by simp)
  have h₀ := orbitCount_sumCongr_one σ
  omega

end Kink

/-- The arcs of a code with a kink added at `h`, as a perfect matching of the old half-edges and
the four new slots. -/
private def kinkMatching (e : PerfectMatching (Fin (4 * n))) (h : Fin (4 * n)) :
    PerfectMatching (Fin (4 * n) ⊕ Fin 4) :=
  PerfectMatching.mk (kinkPerm e.val h)
    (fun x => by
      have hQ : ∀ z, Perm.sumCongr e.val (slotSmoothing true)
          (Perm.sumCongr e.val (slotSmoothing true) z) = z := fun z => by
        rcases z with y | t <;> simp only [Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
          e.apply_apply, slotSmoothing_apply_apply]
      simp only [kinkPerm, Perm.mul_apply, swap_apply_self, hQ])
    (fun x hx => by
      rw [kinkPerm, Perm.mul_apply, Perm.mul_apply, swap_apply_eq_iff] at hx
      rcases hy : swap (.inl (e.val h)) (.inr 0) x with y | t
      · rw [hy, Perm.sumCongr_apply, Sum.map_inl] at hx
        exact e.apply_ne y (Sum.inl_injective hx)
      · rw [hy, Perm.sumCongr_apply, Sum.map_inr] at hx
        exact slotSmoothing_ne true t (Sum.inr_injective hx))

/-- **The first Reidemeister move**: add a kink, with over-pair indicator `b`, to the arc of `D`
ending at the half-edge `h`. The new crossing is `Fin.last n`. Its slot `0` is joined to `h`, its
slot `1` to the other end `D.edgePair.val h` of the old arc, and its slots `2` and `3` to each
other. -/
def reidemeisterOne (D : PDCode n) (h : Fin (4 * n)) (b : Bool) : PDCode (n + 1) where
  halfEdge := (halfEdgeSuccEquiv n).permCongr (Perm.sumCongr D.halfEdge 1)
  edgePair := PerfectMatching.congr (halfEdgeSuccEquiv n) (kinkMatching D.edgePair h)
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := Fin.snoc (α := fun _ => Bool) D.overPair b

variable (D : PDCode n) (h : Fin (4 * n)) (b : Bool)

/-- The old crossings keep their half-edges. -/
@[simp] theorem reidemeisterOne_crossing_castSucc (i : Fin n) (slot : Fin 4) :
    (D.reidemeisterOne h b).halfEdge
        (halfEdgeSuccEquiv n (.inl (crossingSlotEquiv n (i, slot)))) =
      halfEdgeSuccEquiv n (.inl (D.crossing i slot)) := by
  simp [reidemeisterOne, Equiv.permCongr_apply]

/-- The slots of the new crossing are the four new half-edges. -/
@[simp] theorem reidemeisterOne_crossing_last (slot : Fin 4) :
    (D.reidemeisterOne h b).halfEdge (halfEdgeSuccEquiv n (.inr slot)) =
      halfEdgeSuccEquiv n (.inr slot) := by
  simp [reidemeisterOne, Equiv.permCongr_apply]

/-- The old crossings keep their over-strands. -/
@[simp] theorem reidemeisterOne_overPair_castSucc (i : Fin n) :
    (D.reidemeisterOne h b).overPair i.castSucc = D.overPair i := by
  simp [reidemeisterOne]

/-- The over-pair indicator of the new crossing is `b`. -/
@[simp] theorem reidemeisterOne_overPair_last :
    (D.reidemeisterOne h b).overPair (Fin.last n) = b := by
  simp [reidemeisterOne]

/-- The move keeps the crossing-free circles. -/
@[simp] theorem reidemeisterOne_crossinglessComponentCount :
    (D.reidemeisterOne h b).crossinglessComponentCount = D.crossinglessComponentCount := by
  simp [reidemeisterOne]

private theorem reidemeisterOne_edgePair_val :
    (D.reidemeisterOne h b).edgePair.val =
      (halfEdgeSuccEquiv n).permCongr (kinkPerm D.edgePair.val h) := by
  simp [reidemeisterOne, kinkMatching, PerfectMatching.congr_val, PerfectMatching.val_mk]

/-- The half-edge `h` is joined to slot `0` of the new crossing. -/
@[simp] theorem reidemeisterOne_edgePair_inl_self :
    (D.reidemeisterOne h b).edgePair.val (halfEdgeSuccEquiv n (.inl h)) =
      halfEdgeSuccEquiv n (.inr 0) := by
  simp [reidemeisterOne_edgePair_val, Equiv.permCongr_apply,
    kinkPerm_inl_self (D.edgePair.apply_ne h)]

/-- Slot `0` of the new crossing is joined to the half-edge `h`. -/
@[simp] theorem reidemeisterOne_edgePair_inr_zero :
    (D.reidemeisterOne h b).edgePair.val (halfEdgeSuccEquiv n (.inr 0)) =
      halfEdgeSuccEquiv n (.inl h) := by
  simp [reidemeisterOne_edgePair_val, Equiv.permCongr_apply,
    kinkPerm_inr_zero (D.edgePair.apply_apply h) (D.edgePair.apply_ne h)]

/-- The other end of the old arc is joined to slot `1` of the new crossing. -/
@[simp] theorem reidemeisterOne_edgePair_inl_edgePair :
    (D.reidemeisterOne h b).edgePair.val (halfEdgeSuccEquiv n (.inl (D.edgePair.val h))) =
      halfEdgeSuccEquiv n (.inr 1) := by
  simp [reidemeisterOne_edgePair_val, Equiv.permCongr_apply, kinkPerm_inl_apply_self]

/-- Slot `1` of the new crossing is joined to the other end of the old arc. -/
@[simp] theorem reidemeisterOne_edgePair_inr_one :
    (D.reidemeisterOne h b).edgePair.val (halfEdgeSuccEquiv n (.inr 1)) =
      halfEdgeSuccEquiv n (.inl (D.edgePair.val h)) := by
  simp [reidemeisterOne_edgePair_val, Equiv.permCongr_apply, kinkPerm_inr_one]

/-- Slot `2` of the new crossing is joined to slot `3`: this arc is the loop of the kink. -/
@[simp] theorem reidemeisterOne_edgePair_inr_two :
    (D.reidemeisterOne h b).edgePair.val (halfEdgeSuccEquiv n (.inr 2)) =
      halfEdgeSuccEquiv n (.inr 3) := by
  simp [reidemeisterOne_edgePair_val, Equiv.permCongr_apply, kinkPerm_inr_two]

/-- Slot `3` of the new crossing is joined to slot `2`. -/
@[simp] theorem reidemeisterOne_edgePair_inr_three :
    (D.reidemeisterOne h b).edgePair.val (halfEdgeSuccEquiv n (.inr 3)) =
      halfEdgeSuccEquiv n (.inr 2) := by
  simp [reidemeisterOne_edgePair_val, Equiv.permCongr_apply, kinkPerm_inr_three]

/-- Every half-edge off the cut arc keeps its old partner. -/
@[simp] theorem reidemeisterOne_edgePair_inl_of_ne {x : Fin (4 * n)} (hx : x ≠ h)
    (hx' : x ≠ D.edgePair.val h) :
    (D.reidemeisterOne h b).edgePair.val (halfEdgeSuccEquiv n (.inl x)) =
      halfEdgeSuccEquiv n (.inl (D.edgePair.val x)) := by
  simp [reidemeisterOne_edgePair_val, Equiv.permCongr_apply, kinkPerm_inl_of_ne hx hx']

/-- Mirroring the new code adds the mirror kink to the mirror code. -/
@[simp] theorem mirror_reidemeisterOne :
    (D.reidemeisterOne h b).mirror = D.mirror.reidemeisterOne h !b := by
  apply PDCode.ext
  · simp [reidemeisterOne]
  · simp [reidemeisterOne]
  · simp [reidemeisterOne]
  · funext i
    induction i using Fin.lastCases <;> simp

private theorem smoothingTurn_reidemeisterOne (c : Fin (n + 1) → Bool) :
    (D.reidemeisterOne h b).smoothingTurn c = (halfEdgeSuccEquiv n).permCongr
      (Perm.sumCongr (D.smoothingTurn (Fin.init c)) (slotSmoothing (c (Fin.last n)))) := by
  ext x
  obtain ⟨y, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
  rcases y with y | slot
  · obtain ⟨z, rfl⟩ := D.halfEdge.surjective y
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective z
    have hx := D.reidemeisterOne_crossing_castSucc h b i slot
    rw [crossing_apply, ← crossingSlotEquiv_succ_castSucc] at hx
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, Perm.sumCongr_apply, Sum.map_inl,
      smoothingTurn_crossing, ← hx, smoothingTurn_crossing, crossing_apply,
      crossingSlotEquiv_succ_castSucc, reidemeisterOne_crossing_castSucc, Fin.init_def]
  · have hx : (D.reidemeisterOne h b).halfEdge
        (crossingSlotEquiv (n + 1) (Fin.last n, slot)) = halfEdgeSuccEquiv n (.inr slot) := by
      simpa only [crossingSlotEquiv_succ_last] using D.reidemeisterOne_crossing_last h b slot
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, Perm.sumCongr_apply, Sum.map_inr, ← hx,
      smoothingTurn_crossing, crossing_apply, crossingSlotEquiv_succ_last,
      reidemeisterOne_crossing_last]

private theorem crossingTurn_reidemeisterOne :
    (D.reidemeisterOne h b).crossingTurn = (halfEdgeSuccEquiv n).permCongr
      (Perm.sumCongr D.crossingTurn oppositeCrossingSlot) := by
  ext x
  obtain ⟨y, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
  rcases y with y | slot
  · obtain ⟨z, rfl⟩ := D.halfEdge.surjective y
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective z
    have hx := D.reidemeisterOne_crossing_castSucc h b i slot
    rw [crossing_apply, ← crossingSlotEquiv_succ_castSucc] at hx
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, Perm.sumCongr_apply, Sum.map_inl,
      crossingTurn_crossing, ← hx, crossingTurn_crossing, crossing_apply,
      crossingSlotEquiv_succ_castSucc, reidemeisterOne_crossing_castSucc]
  · have hx : (D.reidemeisterOne h b).halfEdge
        (crossingSlotEquiv (n + 1) (Fin.last n, slot)) = halfEdgeSuccEquiv n (.inr slot) := by
      simpa only [crossingSlotEquiv_succ_last] using D.reidemeisterOne_crossing_last h b slot
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, Perm.sumCongr_apply, Sum.map_inr, ← hx,
      crossingTurn_crossing, crossing_apply, crossingSlotEquiv_succ_last,
      reidemeisterOne_crossing_last]

private theorem init_smoothingChoice_reidemeisterOne (s : Fin (n + 1) → Bool) :
    Fin.init ((D.reidemeisterOne h b).smoothingChoice s) = D.smoothingChoice (Fin.init s) := by
  funext i
  cases hs : s i.castSucc <;> simp [Fin.init, hs]

private theorem smoothingChoice_reidemeisterOne_last (s : Fin (n + 1) → Bool) :
    (D.reidemeisterOne h b).smoothingChoice s (Fin.last n) = (s (Fin.last n) == b) := by
  cases hs : s (Fin.last n) <;> cases b <;> simp [hs]

/-- Smoothing the new code has two directed traversal orbits more than smoothing the old one,
namely the loop of the kink, exactly when the state cuts that loop off. -/
private theorem orbitCount_statePerm_reidemeisterOne (s : Fin (n + 1) → Bool) :
    orbitCount ((D.reidemeisterOne h b).statePerm s) =
      orbitCount (D.statePerm (Fin.init s)) + if s (Fin.last n) = b then 2 else 0 := by
  have he := D.edgePair.apply_apply h
  have hne := D.edgePair.apply_ne h
  rw [statePerm_def, statePerm_def, smoothingTurn_reidemeisterOne,
    init_smoothingChoice_reidemeisterOne, smoothingChoice_reidemeisterOne_last,
    reidemeisterOne_edgePair_val, ← Equiv.permCongr_mul, Equiv.orbitCount_permCongr]
  by_cases hs : s (Fin.last n) = b
  · simp only [hs, ↓reduceIte, beq_self_eq_true]
    rw [sumCongr_slotSmoothing_true_mul_kinkPerm he hne, orbitCount_splice_two]
  · have hbne : (s (Fin.last n) == b) = false := by simpa using hs
    rw [hbne]
    simp only [hs, ↓reduceIte, add_zero]
    rw [sumCongr_slotSmoothing_false_mul_kinkPerm he hne,
      orbitCount_splice_four _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]

/-- **Circles after the first Reidemeister move.** A state of the new code leaves one circle more
than its restriction to the old crossings when its choice at the new crossing is `b`, the
smoothing that cuts off the loop of the kink, and the same number of circles otherwise. -/
@[simp] theorem stateLoopCount_reidemeisterOne (s : Fin (n + 1) → Bool) :
    (D.reidemeisterOne h b).stateLoopCount s =
      D.stateLoopCount (Fin.init s) + if s (Fin.last n) = b then 1 else 0 := by
  rw [stateLoopCount_def, stateLoopCount_def, orbitCount_statePerm_reidemeisterOne,
    reidemeisterOne_crossinglessComponentCount]
  split_ifs <;> omega

/-- **The first Reidemeister move keeps the number of components.** -/
@[simp] theorem crossingComponentCount_reidemeisterOne :
    (D.reidemeisterOne h b).crossingComponentCount = D.crossingComponentCount := by
  have he := D.edgePair.apply_apply h
  have hne := D.edgePair.apply_ne h
  rw [crossingComponentCount_def, crossingComponentCount_def, componentPerm_def,
    componentPerm_def, crossingTurn_reidemeisterOne, reidemeisterOne_edgePair_val,
    ← Equiv.permCongr_mul, Equiv.orbitCount_permCongr,
    sumCongr_oppositeCrossingSlot_mul_kinkPerm he hne,
    orbitCount_splice_four _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]

/-- **The Kauffman bracket under the first Reidemeister move.** Adding a kink with over-pair
indicator `b` multiplies the bracket by `-a ^ 3` if `b = true` and by `-a⁻¹ ^ 3` if `b = false`. -/
@[simp] theorem kauffmanBracket_reidemeisterOne {R : Type*} [CommRing R] (a : Rˣ) :
    (D.reidemeisterOne h b).kauffmanBracket a =
      -(((bif b then a else a⁻¹ : Rˣ) : R) ^ 3) * D.kauffmanBracket a := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact h.elim0
  -- Split each state of the new code into a state of the old code and a choice at the new
  -- crossing, and compare the two resulting terms with one term of the old bracket.
  rw [kauffmanBracket_def, kauffmanBracket_def, ← (Fin.snocEquiv fun _ => Bool).sum_comp,
    Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨k, hk⟩ : ∃ k, D.stateLoopCount s = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (D.one_le_stateLoopCount hn s)).symm⟩
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, stateLoopCount_reidemeisterOne, Fin.init_snoc,
    Fin.snoc_last, stateWeight_snoc, hk]
  cases b <;> simp only [Bool.cond_true, Bool.cond_false, Bool.true_eq_false, Bool.false_eq_true,
    ↓reduceIte, add_zero, Nat.add_sub_cancel, pow_succ, jonesDelta_def, Units.val_mul]
  · linear_combination (-((stateWeight s a : R) * (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)) ^ k *
      (a : R))) * a.inv_mul
  · linear_combination (-((stateWeight s a : R) * (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)) ^ k *
      ((a⁻¹ : Rˣ) : R))) * a.mul_inv

end PDCode

end TauCeti
