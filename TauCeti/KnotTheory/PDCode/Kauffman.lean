/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Components
public import TauCeti.KnotTheory.TemperleyLieb
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.LinearCombination

/-!
# The Kauffman bracket of a PD-code

Smoothing every crossing of a diagram in one of its two ways turns the diagram into a disjoint
union of circles. A **state** of a PD-code with `n` crossings is such a choice at each crossing,
recorded as `s : Fin n → Bool`, with `s i = true` selecting the `A`-smoothing at crossing `i`:
the smoothing that turns left off the over-strand, equivalently the one joining the two regions
swept out when the over-strand is rotated counterclockwise. With the four slots of a crossing in
counterclockwise order that smoothing takes each over-slot to the preceding slot, which is
`TauCeti.PDCode.slotSmoothing` applied to the code's own over-pair indicator; the `B`-smoothing
is the same construction applied to the complementary indicator.

Reconnecting the half-edges accordingly gives `TauCeti.PDCode.statePerm`, the traversal of the
smoothed diagram: cross an arc, then follow the smoothing at the crossing reached. Exactly as for
`TauCeti.PDCode.componentPerm`, each circle of the smoothed diagram carries two of its orbits, one
for each direction of travel, so `TauCeti.PDCode.stateLoopCount` halves the orbit count and adds
the crossing-free circles that the code records separately.

The **Kauffman bracket** is the resulting state sum `∑ s, a ^ (A(s) - B(s)) * δ ^ (loops s - 1)`,
formed
over a commutative ring with a distinguished unit `a` at the loop value
`δ = -(a ^ 2 + a⁻¹ ^ 2)` (`TauCeti.TemperleyLieb.jonesDelta`), which is the value at which the
Kauffman-bracket expansion of a crossing is invertible. This is Kauffman's `⟨·⟩` with Lickorish's
normalisation `⟨unknot⟩ = 1`: a code with no crossings and `c ≥ 1` circles has bracket
`δ ^ (c - 1)`. The exponent is truncated subtraction, so the empty code has bracket `1`; every
code with a crossing has at least one circle in each state (`TauCeti.PDCode.one_le_stateLoopCount`),
so this affects only the empty code.

The bracket depends on a PD-code only through its relabelling class, and mirroring a code inverts
the unit `a`. On the one-crossing kink diagram `TauCeti.PDCode.kink` it takes the value
`-a ^ 3`, the framing factor of the first Reidemeister move. Whether the bracket descends from
diagrams to knots is the question of its behaviour under the Reidemeister moves, which are
separate constructions on PD-codes; the first move is in
`TauCeti/KnotTheory/PDCode/Reidemeister/One.lean`.

For an oriented PD-code, `TauCeti.OrientedPDCode.normalizedKauffmanBracket` multiplies the bracket
by the writhe correction `(-a ^ 3) ^ (-writhe)`. This is the normalization used to obtain the
Jones polynomial from the bracket.

## Main definitions

* `TauCeti.PDCode.smoothingTurn`: the reconnection of the half-edges smoothing every crossing.
* `TauCeti.PDCode.smoothingChoice`: the over-pair indicator a state selects at each crossing.
* `TauCeti.PDCode.statePerm`: the traversal of the smoothed diagram.
* `TauCeti.PDCode.stateLoopCount`: the number of circles of the smoothed diagram.
* `TauCeti.PDCode.stateWeight`: the weight `a ^ (A(s) - B(s))` of a state.
* `TauCeti.PDCode.kauffmanBracket`: the Kauffman bracket state sum.
* `TauCeti.OrientedPDCode.normalizedKauffmanBracket`: the writhe-normalized bracket.

## Main results

* `TauCeti.PDCode.even_orbitCount_statePerm`: the traversal orbits of a smoothed diagram come in
  pairs, and `TauCeti.PDCode.one_le_stateLoopCount`: a code with a crossing leaves at least one
  circle in every state.
* `TauCeti.PDCode.kauffmanBracket_relabel`: the bracket is invariant under relabelling.
* `TauCeti.PDCode.kauffmanBracket_mirror`: mirroring the code inverts the unit.
* `TauCeti.PDCode.kauffmanBracket_eq_jonesDelta_pow`: a code with no crossings and `c` circles has
  bracket `δ ^ (c - 1)`.
* `TauCeti.PDCode.stateLoopCount_kink_true`, `TauCeti.PDCode.stateLoopCount_kink_false`: the two
  smoothings of a kink leave two circles and one circle.
* `TauCeti.PDCode.kauffmanBracket_kink`: the kink diagram has bracket `-a ^ 3`.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3
  (the Kauffman bracket and the Jones polynomial).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2-3 (the PD convention).
-/


public section

namespace TauCeti

open Equiv Equiv.Perm TemperleyLieb

namespace PDCode

variable {n : ℕ}

/-- A local smoothing never joins a slot to the opposite slot: the two arcs of a smoothing cut
across the two local strands instead of following them, which is what distinguishes a smoothing
from `TauCeti.PDCode.crossingTurn`. -/
theorem slotSmoothing_ne_oppositeCrossingSlot (b : Bool) (slot : Fin 4) :
    slotSmoothing b slot ≠ oppositeCrossingSlot slot := by
  have key : ∀ (c : Bool) (t : Fin 4), (slotSmoothing c t).val ≠ (t + 2).val := by
    intro c
    cases c <;> simp only [slotSmoothing_false, slotSmoothing_true] <;> decide
  intro h
  exact key b slot (by rw [h, oppositeCrossingSlot_apply])

/-- The two local smoothings at a crossing are distinct. -/
theorem slotSmoothing_ne_slotSmoothing_not (b : Bool) : slotSmoothing b ≠ slotSmoothing !b := by
  cases b <;> simp only [Bool.not_false, Bool.not_true, slotSmoothing_false, slotSmoothing_true] <;>
    decide

/-- Smooth every crossing of a PD-code, using at crossing `i` the local smoothing
`slotSmoothing (b i)`. This is the smoothing counterpart of `TauCeti.PDCode.crossingTurn`, which
instead follows a local strand through a crossing. -/
def smoothingTurn (D : PDCode n) (b : Fin n → Bool) : Equiv.Perm (Fin (4 * n)) :=
  D.halfEdge.permCongr
    ((crossingSlotEquiv n).permCongr (Equiv.prodCongrRight fun i ↦ slotSmoothing (b i)))

/-- The defining equation for the smoothing traversal permutation. -/
theorem smoothingTurn_def (D : PDCode n) (b : Fin n → Bool) :
    D.smoothingTurn b = D.halfEdge.permCongr
      ((crossingSlotEquiv n).permCongr (Equiv.prodCongrRight fun i ↦ slotSmoothing (b i))) := (rfl)

/-- Smoothing reconnects the slots at a crossing by the chosen local smoothing. -/
@[simp] theorem smoothingTurn_crossing (D : PDCode n) (b : Fin n → Bool) (i : Fin n)
    (slot : Fin 4) :
    D.smoothingTurn b (D.halfEdge (crossingSlotEquiv n (i, slot))) =
      D.crossing i (slotSmoothing (b i) slot) := by
  simp [smoothingTurn]

/-- Smoothing is an involution of the half-edges. -/
@[simp] theorem smoothingTurn_apply_apply (D : PDCode n) (b : Fin n → Bool) (h : Fin (4 * n)) :
    D.smoothingTurn b (D.smoothingTurn b h) = h := by
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  simp [smoothingTurn]

/-- Mirroring a code does not change how a prescribed family of local smoothings reconnects its
half-edges; only which of them is the `A`-smoothing changes. -/
@[simp] theorem smoothingTurn_mirror (D : PDCode n) (b : Fin n → Bool) :
    D.mirror.smoothingTurn b = D.smoothingTurn b := by
  simp [smoothingTurn]

/-- Reconnecting arcs does not change how the crossings are smoothed. -/
@[simp] theorem smoothingTurn_reconnect (D : PDCode n) (p q : Fin (4 * n))
    (c : Fin n → Bool) :
    (D.reconnect p q).smoothingTurn c = D.smoothingTurn c := by
  rw [smoothingTurn_def, smoothingTurn_def, reconnect_halfEdge]

/-- Relabelling conjugates smoothing by the half-edge relabelling, after transporting the family
of local smoothings along the crossing relabelling. -/
@[simp] theorem smoothingTurn_relabel (D : PDCode n) (b : Fin n → Bool)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).smoothingTurn b = half.permCongr (D.smoothingTurn (b ∘ cross)) := by
  ext h
  obtain ⟨x, rfl⟩ := half.surjective h
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective x
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  have he : half (D.halfEdge (crossingSlotEquiv n (i, slot))) =
      (D.relabel half cross).halfEdge (crossingSlotEquiv n (cross i, slot)) := by
    rw [← D.crossing_apply, ← (D.relabel half cross).crossing_apply]
    simpa only [Equiv.symm_apply_apply] using (D.crossing_relabel half cross (cross i) slot).symm
  rw [he, smoothingTurn_crossing, crossing_relabel]
  simp

/-- The over-pair indicator of the local smoothing that a state selects at a crossing: the code's
own indicator where the state chooses the `A`-smoothing, and the complementary one where it
chooses the `B`-smoothing. -/
def smoothingChoice (D : PDCode n) (s : Fin n → Bool) (i : Fin n) : Bool :=
  bif s i then D.overPair i else !D.overPair i

/-- Where a state is `true` it selects the `A`-smoothing, the one built from the code's own
over-pair indicator. -/
@[simp] theorem smoothingChoice_of_true (D : PDCode n) {s : Fin n → Bool} {i : Fin n}
    (hs : s i = true) : D.smoothingChoice s i = D.overPair i := by
  simp [smoothingChoice, hs]

/-- Where a state is `false` it selects the `B`-smoothing, the one built from the complementary
over-pair indicator. -/
@[simp] theorem smoothingChoice_of_false (D : PDCode n) {s : Fin n → Bool} {i : Fin n}
    (hs : s i = false) : D.smoothingChoice s i = !D.overPair i := by
  simp [smoothingChoice, hs]

/-- Mirroring a code exchanges the `A`- and `B`-smoothings, so it acts on states by negation. -/
@[simp] theorem smoothingChoice_mirror (D : PDCode n) (s : Fin n → Bool) :
    D.mirror.smoothingChoice s = D.smoothingChoice fun j ↦ !(s j) := by
  funext i
  cases hs : s i <;> simp [smoothingChoice, hs]

/-- Reconnecting arcs does not change which smoothing a state selects. -/
@[simp] theorem smoothingChoice_reconnect (D : PDCode n) (p q : Fin (4 * n))
    (s : Fin n → Bool) :
    (D.reconnect p q).smoothingChoice s = D.smoothingChoice s := by
  funext i
  cases hs : s i <;> simp [hs]

/-- Relabelling reads a state's choice at the old crossing name. -/
@[simp] theorem smoothingChoice_relabel (D : PDCode n) (s : Fin n → Bool)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).smoothingChoice s = D.smoothingChoice (s ∘ cross) ∘ cross.symm := by
  funext i
  simp [smoothingChoice]

/-- The traversal of the diagram smoothed according to the state `s`: cross an arc, then follow
the chosen smoothing at the crossing reached. Its orbits are the two directed traversals of each
circle of the smoothed diagram. -/
def statePerm (D : PDCode n) (s : Fin n → Bool) : Equiv.Perm (Fin (4 * n)) :=
  D.smoothingTurn (D.smoothingChoice s) * D.edgePair.val

/-- The defining equation of smoothed traversal. -/
theorem statePerm_def (D : PDCode n) (s : Fin n → Bool) :
    D.statePerm s = D.smoothingTurn (D.smoothingChoice s) * D.edgePair.val := (rfl)

/-- Smoothed traversal pairs the arc first, then follows the chosen smoothing. -/
@[simp] theorem statePerm_apply (D : PDCode n) (s : Fin n → Bool) (h : Fin (4 * n)) :
    D.statePerm s h = D.smoothingTurn (D.smoothingChoice s) (D.edgePair.val h) := by
  simp [statePerm, Equiv.Perm.mul_def]

/-- Mirroring a code negates the state that produces a given smoothed diagram. -/
@[simp] theorem statePerm_mirror (D : PDCode n) (s : Fin n → Bool) :
    D.mirror.statePerm s = D.statePerm fun i ↦ !(s i) := by
  simp [statePerm]

/-- Relabelling conjugates smoothed traversal by the half-edge relabelling. -/
@[simp] theorem statePerm_relabel (D : PDCode n) (s : Fin n → Bool)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).statePerm s = half.permCongr (D.statePerm (s ∘ cross)) := by
  have hcomp : (D.smoothingChoice (s ∘ cross) ∘ cross.symm) ∘ cross
      = D.smoothingChoice (s ∘ cross) := by
    funext i
    simp
  rw [statePerm, statePerm, smoothingChoice_relabel, smoothingTurn_relabel, hcomp,
    relabel_edgePair, PerfectMatching.congr_val, ← Equiv.permCongr_mul]

section AddCrossing

/-! ### Codes with one crossing more

Let `D'` be a code with one crossing more than `D`, whose first `n` crossings keep the half-edges
and over-strands of `D`, and whose last crossing takes the four new half-edge positions and has
over-pair indicator `b`. Crossing insertion and the first Reidemeister move build such codes. A
state of `D'` is a state of `D` together with a choice at the new crossing, and the lemmas below
split its smoothing accordingly. -/

variable {D : PDCode n} {D' : PDCode (n + 1)}

/-- Smoothing `D'` is smoothing `D` together with the chosen local smoothing of the new
crossing. -/
theorem smoothingTurn_eq_permCongr_sumCongr
    (hD : D'.halfEdge = (halfEdgeSuccEquiv n).permCongr (Perm.sumCongr D.halfEdge 1))
    (c : Fin (n + 1) → Bool) :
    D'.smoothingTurn c = (halfEdgeSuccEquiv n).permCongr
      (Perm.sumCongr (D.smoothingTurn (Fin.init c)) (slotSmoothing (c (Fin.last n)))) :=
  eq_permCongr_sumCongr_of_halfEdge_eq hD (fun i => slotSmoothing (c i))
    (fun i slot => by simpa only [Fin.init_def] using D.smoothingTurn_crossing (Fin.init c) i slot)
    (D'.smoothingTurn_crossing c)

variable {b : Bool} (hO : D'.overPair = Fin.snoc (α := fun _ => Bool) D.overPair b)
include hO

/-- At the old crossings, a state of `D'` selects the smoothings its restriction selects
in `D`. -/
theorem init_smoothingChoice_of_overPair_eq (s : Fin (n + 1) → Bool) :
    Fin.init (D'.smoothingChoice s) = D.smoothingChoice (Fin.init s) := by
  funext i
  cases hs : s i.castSucc <;> simp [Fin.init, hs, hO]

/-- At the new crossing, a state of `D'` selects the local smoothing `slotSmoothing true` exactly
when its choice there is `b`. -/
theorem smoothingChoice_last_of_overPair_eq (s : Fin (n + 1) → Bool) :
    D'.smoothingChoice s (Fin.last n) = (s (Fin.last n) == b) := by
  cases hs : s (Fin.last n) <;> cases b <;> simp [hs, hO]

end AddCrossing

/-- The number of circles of the diagram smoothed according to the state `s`, the crossing-free
circles of the code included. Each circle meeting a crossing is represented by the two directed
orbits of `TauCeti.PDCode.statePerm`, one for each direction of travel, exactly as for
`TauCeti.PDCode.crossingComponentCount`. -/
noncomputable def stateLoopCount (D : PDCode n) (s : Fin n → Bool) : ℕ :=
  orbitCount (D.statePerm s) / 2 + D.crossinglessComponentCount

/-- The number of circles of a smoothed diagram is half the number of directed traversal orbits,
plus the crossing-free circles. -/
theorem stateLoopCount_def (D : PDCode n) (s : Fin n → Bool) :
    D.stateLoopCount s = orbitCount (D.statePerm s) / 2 + D.crossinglessComponentCount := (rfl)

/-- Smoothing every crossing of a code pairs off its half-edges. -/
theorem isPerfectMatching_smoothingTurn (D : PDCode n) (b : Fin n → Bool) :
    IsPerfectMatching (D.smoothingTurn b) := by
  refine isPerfectMatching_iff.mpr ⟨D.smoothingTurn_apply_apply b, fun h hh ↦ ?_⟩
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  rw [smoothingTurn_crossing, crossing_apply, D.halfEdge.apply_eq_iff_eq,
    (crossingSlotEquiv n).apply_eq_iff_eq, Prod.mk.injEq] at hh
  exact slotSmoothing_ne _ slot hh.2

/-- The directed traversal orbits of a smoothed diagram come in pairs, as the halving in
`TauCeti.PDCode.stateLoopCount` presumes: smoothed traversal is a product of two perfect
matchings. -/
theorem even_orbitCount_statePerm (D : PDCode n) (s : Fin n → Bool) :
    Even (orbitCount (D.statePerm s)) :=
  (D.isPerfectMatching_smoothingTurn _).even_orbitCount_mul D.edgePair.prop

/-- A code with no crossings has one circle per crossing-free component, in every state. -/
@[simp] theorem stateLoopCount_eq_crossinglessComponentCount (D : PDCode 0) (s : Fin 0 → Bool) :
    D.stateLoopCount s = D.crossinglessComponentCount := by
  have h := Equiv.Perm.orbitCount_le_card (D.statePerm s)
  simp at h
  simp [stateLoopCount_def, h]

/-- Every smoothing of a diagram with a component has at least one circle. -/
theorem one_le_stateLoopCount_of_componentCount_pos (D : PDCode n)
    (h : 0 < D.componentCount) (s : Fin n → Bool) : 1 ≤ D.stateLoopCount s := by
  by_cases hn : n = 0
  · subst n
    have hc : 0 < D.crossinglessComponentCount := by
      simpa [componentCount_eq, crossingComponentCount_eq_zero] using h
    rw [stateLoopCount_eq_crossinglessComponentCount]
    omega
  · have hpos : 0 < orbitCount (D.statePerm s) := by
      let _ : Nonempty (Fin (4 * n)) := ⟨⟨0, by omega⟩⟩
      exact Equiv.Perm.orbitCount_pos (D.statePerm s)
    obtain ⟨k, hk⟩ := D.even_orbitCount_statePerm s
    rw [stateLoopCount_def]
    omega

/-- A code with a crossing has at least one circle in every state. -/
theorem one_le_stateLoopCount (D : PDCode n) (hn : n ≠ 0) (s : Fin n → Bool) :
    1 ≤ D.stateLoopCount s :=
  D.one_le_stateLoopCount_of_componentCount_pos (D.componentCount_pos hn) s

/-- Mirroring a code negates the state producing a given circle count. -/
@[simp] theorem stateLoopCount_mirror (D : PDCode n) (s : Fin n → Bool) :
    D.mirror.stateLoopCount s = D.stateLoopCount fun i ↦ !(s i) := by
  simp [stateLoopCount_def]

/-- Relabelling preserves the circle count of every state. -/
@[simp] theorem stateLoopCount_relabel (D : PDCode n) (s : Fin n → Bool)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).stateLoopCount s = D.stateLoopCount (s ∘ cross) := by
  simp [stateLoopCount_def]

section StateWeight

variable {R : Type*} [CommMonoid R]

/-- The weight of a state: the unit `a` at each `A`-smoothing and `a⁻¹` at each `B`-smoothing, so
that a state with `p` of the former and `q` of the latter has weight `a ^ (p - q)`. -/
def stateWeight (s : Fin n → Bool) (a : Rˣ) : Rˣ :=
  ∏ i, bif s i then a else a⁻¹

/-- The defining equation of a state's Kauffman-bracket weight. -/
theorem stateWeight_def (s : Fin n → Bool) (a : Rˣ) :
    stateWeight s a = ∏ i, bif s i then a else a⁻¹ := (rfl)

/-- Concatenating states multiplies their weights. -/
@[simp]
theorem stateWeight_append {m : ℕ} (s : Fin n → Bool) (t : Fin m → Bool) (a : Rˣ) :
    stateWeight (Fin.append s t) a = stateWeight s a * stateWeight t a := by
  simp [stateWeight_def, Fin.prod_univ_add]

/-- Negating a state inverts its weight, since it exchanges the `A`- and `B`-smoothings. -/
@[simp] theorem stateWeight_not (s : Fin n → Bool) (a : Rˣ) :
    stateWeight (fun i ↦ !(s i)) a = (stateWeight s a)⁻¹ := by
  rw [stateWeight, stateWeight, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  cases hs : s i <;> simp

/-- Inverting the unit inverts every state weight. -/
@[simp] theorem stateWeight_inv (s : Fin n → Bool) (a : Rˣ) :
    stateWeight s a⁻¹ = (stateWeight s a)⁻¹ := by
  rw [stateWeight, stateWeight, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  cases hs : s i <;> simp

/-- Transporting a state along a relabelling of the crossings preserves its weight. -/
@[simp] theorem stateWeight_comp (s : Fin n → Bool) (a : Rˣ) (cross : Equiv.Perm (Fin n)) :
    stateWeight (s ∘ cross) a = stateWeight s a :=
  Equiv.prod_comp cross fun i ↦ bif s i then a else a⁻¹

/-- Extending a state by a choice at a new last crossing multiplies its weight by the weight of
that choice. -/
@[simp] theorem stateWeight_snoc (s : Fin n → Bool) (c : Bool) (a : Rˣ) :
    stateWeight (Fin.snoc (α := fun _ ↦ Bool) s c) a =
      stateWeight s a * bif c then a else a⁻¹ := by
  simp [stateWeight_def, Fin.prod_univ_castSucc]

end StateWeight

section Bracket

variable {R : Type*} [CommRing R]

/-- **The Kauffman bracket** of a PD-code at a unit `a`: the sum, over all `2 ^ n` states, of the
weight of the state times the loop value `TauCeti.TemperleyLieb.jonesDelta a` raised to one less
than the number of circles of the smoothed diagram. This is Lickorish's normalisation
`⟨unknot⟩ = 1`; with truncated subtraction the empty diagram also has bracket `1`. -/
noncomputable def kauffmanBracket (D : PDCode n) (a : Rˣ) : R :=
  ∑ s : Fin n → Bool, (stateWeight s a : R) * jonesDelta a ^ (D.stateLoopCount s - 1)

/-- The defining state-sum equation of the Kauffman bracket. -/
theorem kauffmanBracket_def (D : PDCode n) (a : Rˣ) :
    D.kauffmanBracket a =
      ∑ s : Fin n → Bool, (stateWeight s a : R) * jonesDelta a ^ (D.stateLoopCount s - 1) :=
    (rfl)

/-- The Kauffman bracket depends on a PD-code only through its relabelling class. -/
@[simp] theorem kauffmanBracket_relabel (D : PDCode n) (a : Rˣ)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).kauffmanBracket a = D.kauffmanBracket a := by
  let e := Equiv.piCongrLeft (fun _ : Fin n ↦ Bool) cross.symm
  have he : (fun s : Fin n → Bool ↦ s ∘ cross) = e := by
    funext s i
    simp [e, Equiv.piCongrLeft_apply]
  have hbij : Function.Bijective (fun s : Fin n → Bool ↦ s ∘ cross) := by
    rw [he]
    exact e.bijective
  refine Fintype.sum_bijective (fun s ↦ s ∘ cross)
    hbij _ _ fun s ↦ ?_
  rw [stateLoopCount_relabel, stateWeight_comp]

/-- Mirroring a PD-code inverts the unit in its Kauffman bracket. -/
@[simp] theorem kauffmanBracket_mirror (D : PDCode n) (a : Rˣ) :
    D.mirror.kauffmanBracket a = D.kauffmanBracket a⁻¹ := by
  refine Fintype.sum_bijective (fun s i ↦ !(s i))
    (Function.Involutive.bijective fun s ↦ by funext i; simp) _ _ fun s ↦ ?_
  rw [stateLoopCount_mirror, stateWeight_inv, stateWeight_not, inv_inv, jonesDelta_inv]

/-- A PD-code with no crossings and `c` crossing-free circles has Kauffman bracket `δ ^ (c - 1)`.
This pins the normalisation of `TauCeti.PDCode.kauffmanBracket`: the unknot has bracket `1`, and
each further circle contributes one factor of the loop value. -/
theorem kauffmanBracket_eq_jonesDelta_pow (D : PDCode 0) (a : Rˣ) :
    D.kauffmanBracket a = jonesDelta a ^ (D.crossinglessComponentCount - 1) := by
  rw [kauffmanBracket, Fintype.sum_unique]
  simp [stateWeight]

/-- Smoothing the kink reconnects its slots by the chosen local smoothing. -/
@[simp] theorem kink_smoothingTurn (b : Fin 1 → Bool) (i : Fin 1) (t : Fin 4) :
    kink.smoothingTurn b (crossingSlotEquiv 1 (i, t))
      = crossingSlotEquiv 1 (i, slotSmoothing (b i) t) := by
  have h := kink.smoothingTurn_crossing b i t
  rw [kink_halfEdge] at h
  simpa using h

/-- The `A`-smoothing of the kink undoes its arcs, separating the strand into two circles. -/
private theorem kink_statePerm_true : kink.statePerm (fun _ ↦ true) = 1 := by
  refine Equiv.ext fun h ↦ ?_
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv 1).surjective h
  rw [statePerm_apply, kink_edgePair_apply, kink_smoothingTurn]
  simp only [smoothingChoice, kink_overPair, Bool.cond_true, one_apply]
  exact congrArg (crossingSlotEquiv 1) (Prod.ext rfl (slotSmoothing_apply_apply true slot))

/-- The `B`-smoothing of the kink leaves a single circle. -/
private theorem kink_statePerm_false : kink.statePerm (fun _ ↦ false) =
    (crossingSlotEquiv 1).permCongr
      (Equiv.prodCongrRight fun _ : Fin 1 ↦ slotSmoothing false * slotSmoothing true) := by
  refine Equiv.ext fun h ↦ ?_
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv 1).surjective h
  rw [statePerm_apply, kink_edgePair_apply, kink_smoothingTurn]
  simp [Equiv.Perm.mul_apply]

/-- **The `A`-smoothing of the kink leaves two circles.** -/
theorem stateLoopCount_kink_true : kink.stateLoopCount (fun _ ↦ true) = 2 := by
  rw [stateLoopCount_def, kink_statePerm_true, orbitCount_one, kink_crossinglessComponentCount]
  simp

/-- **The `B`-smoothing of the kink leaves one circle.** -/
theorem stateLoopCount_kink_false : kink.stateLoopCount (fun _ ↦ false) = 1 := by
  rw [stateLoopCount_def, kink_statePerm_false, Equiv.orbitCount_permCongr,
    kink_crossinglessComponentCount]
  have hperm : (Equiv.prodCongrRight fun _ : Fin 1 ↦ slotSmoothing false * slotSmoothing true)
      = Equiv.swap ((0 : Fin 1), (1 : Fin 4)) (0, 3) * Equiv.swap ((0 : Fin 1), (0 : Fin 4))
        (0, 2) := by
    simp only [slotSmoothing_false, slotSmoothing_true]
    decide
  have hcard : Nat.card (Fin 1 × Fin 4) = 4 := by simp
  have h₁ := orbitCount_mul_swap_add_one
    (τ := (1 : Equiv.Perm (Fin 1 × Fin 4))) (p := ((0 : Fin 1), (3 : Fin 4)))
    (a := (0, 1)) rfl (by decide)
  have h₂ := orbitCount_mul_swap_add_one
    (τ := Equiv.swap ((0 : Fin 1), (1 : Fin 4)) (0, 3)) (p := ((0 : Fin 1), (2 : Fin 4)))
    (a := (0, 0)) (by decide) (by decide)
  rw [one_mul, orbitCount_one] at h₁
  rw [hperm]
  omega

/-- **The Kauffman bracket of the kink is `-a ^ 3`**, that is, `-a ^ 3` times that of the unknot.
The two smoothings of the single crossing contribute `a * δ` and `a⁻¹`, and the loop value
collapses their sum to `-a ^ 3`: this is the framing factor by which the bracket fails to be
invariant under the first Reidemeister move. -/
theorem kauffmanBracket_kink (a : Rˣ) :
    kink.kauffmanBracket a = -((a : R) ^ 3) := by
  have hbij : Function.Bijective (fun (b : Bool) (_ : Fin 1) ↦ b) :=
    (Equiv.funUnique (Fin 1) Bool).symm.bijective
  rw [kauffmanBracket, ← Fintype.sum_bijective _ hbij
    (fun b ↦ (stateWeight (fun _ : Fin 1 ↦ b) a : R) * jonesDelta a ^
      (kink.stateLoopCount (fun _ ↦ b) - 1)) _ fun b ↦ rfl, Fintype.sum_bool]
  simp only [stateLoopCount_kink_true, stateLoopCount_kink_false, stateWeight,
    Fin.prod_univ_one, Bool.cond_true, Bool.cond_false, Nat.add_one_sub_one, Nat.sub_self,
    pow_one, pow_zero, mul_one, jonesDelta_def]
  linear_combination (-((a⁻¹ : Rˣ) : R)) * a.mul_inv

end Bracket

end PDCode

namespace OrientedPDCode

variable {n : ℕ}

/-- The writhe-normalized Kauffman bracket.  Its correction factor is a unit, so the definition
makes sense over every commutative ring and does not require the bracket value itself to be
invertible. -/
noncomputable def normalizedKauffmanBracket {R : Type*} [CommRing R]
    (D : OrientedPDCode n) (a : Rˣ) : R :=
  (((-a ^ 3) ^ (-D.writhe) : Rˣ) : R) * D.toPDCode.kauffmanBracket a

/-- The writhe-normalized Kauffman bracket is the bracket multiplied by its writhe
correction factor. -/
theorem normalizedKauffmanBracket_def {R : Type*} [CommRing R]
    (D : OrientedPDCode n) (a : Rˣ) :
    D.normalizedKauffmanBracket a =
      (((-a ^ 3) ^ (-D.writhe) : Rˣ) : R) * D.toPDCode.kauffmanBracket a :=
  by
    unfold normalizedKauffmanBracket
    rfl

end OrientedPDCode

end TauCeti
