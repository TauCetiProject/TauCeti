/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel

/-!
# Fox colourings of PD-codes

A Fox colouring of a link diagram with values in an abelian group `M` labels every arc of the
diagram by an element of `M` so that at each crossing twice the label of the over-arc is the sum
of the labels of the two under-arcs (Fox; Crowell–Fox, Chapter VI, Exercise 6; Lickorish,
Chapter 3). For `M = ZMod 3` these are the classical tricolourings, and for `M = ZMod n` they are
the colourings by the dihedral quandle of order `n`.

On a PD-code `D` the labels live on the half-edges and on the crossing-free components, so a
colouring is a family `v` indexed by `Fin (4 * n) ⊕ Fin D.crossinglessComponentCount`. The
conditions are linear, so for an `R`-module `M` the colourings form an `R`-submodule
`TauCeti.PDCode.foxColorings R M` of these families:

* the two half-edges of each arc carry the same label;
* the two half-edges of the over-strand at a crossing carry the same label;
* along the under-strand, with `s + 1` an over-slot, `v (s + 2) = 2 • v (s + 1) - v s`.

The relations do not involve orientations: they are the Alexander relations of an oriented code
evaluated at `t = -1`, where the weight `t ^ (±1)` of every under-slot becomes `-1`. This is how
`TauCeti.KnotTheory.PDCode.FoxColoring.Invariance` shows that the colouring module is an invariant
of Reidemeister equivalence. Constant families are always colourings, and a crossing-free diagram
of `c` circles has the product module `M ^ c` of colourings, one label for each circle.

## Main definitions

* `TauCeti.PDCode.foxColorings`: the `R`-module of Fox colourings of a PD-code with values in
  `M`.

## Main results

* `TauCeti.PDCode.mem_foxColorings_iff`: the defining conditions of a Fox colouring.
* `TauCeti.PDCode.apply_crossing_add_two_of_mem_foxColorings_of_isOver` and
  `TauCeti.PDCode.apply_crossing_add_two_of_mem_foxColorings_of_not_isOver`: the colouring relations
  at the over- and under-strands of a crossing.
* `TauCeti.PDCode.const_mem_foxColorings`: constant families are colourings.
* `TauCeti.PDCode.foxColorings_eq_top_of_zero_crossings`: every family colours a crossing-free code.
* `TauCeti.PDCode.natCard_foxColorings_of_zero_crossings`: a crossing-free code of `c` circles has
  `|M| ^ c` colourings.
* `TauCeti.OrientedPDCode.natCard_foxColorings_unknot`: the crossing-free unknot has `|M|`
  colourings.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Graduate Texts in Mathematics 57,
  Springer (1977), Chapter VI.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate Texts in Mathematics 175,
  Springer (1997), Chapter 3.
* J. H. Przytycki, *3-coloring and other elementary invariants of knots*, Banach Center
  Publications 42 (1998), 275–295.
-/

public section

namespace TauCeti

namespace PDCode

variable {n : ℕ} (D : PDCode n) (R M : Type*) [Semiring R] [AddCommGroup M] [Module R M]

/-- The **Fox colourings** of a PD-code with values in an `R`-module `M`: the families of elements
of `M` indexed by the half-edges and the crossing-free components that agree on the two half-edges
of each arc and, at each crossing, satisfy `v (s + 2) = v s` when `s` is an over-slot and
`v (s + 2) = 2 • v (s + 1) - v s` when `s` is an under-slot. So at every crossing the two
under-arcs have labels summing to twice the label of the over-arc. -/
def foxColorings : Submodule R (Fin (4 * n) ⊕ Fin D.crossinglessComponentCount → M) where
  carrier := {v | (∀ h, v (.inl (D.edgePair.val h)) = v (.inl h)) ∧
    ∀ i slot, v (.inl (D.crossing i (slot + 2))) =
      if D.isOver i slot then v (.inl (D.crossing i slot))
      else 2 • v (.inl (D.crossing i (slot + 1))) - v (.inl (D.crossing i slot))}
  add_mem' {v w} hv hw := by
    refine ⟨fun h ↦ by simp [hv.1 h, hw.1 h], fun i slot ↦ ?_⟩
    simp only [Pi.add_apply, hv.2 i slot, hw.2 i slot]
    split_ifs
    · rfl
    · rw [nsmul_add]
      abel
  zero_mem' := ⟨fun _ ↦ rfl, fun i slot ↦ by simp⟩
  smul_mem' c v hv := by
    refine ⟨fun h ↦ by simp [hv.1 h], fun i slot ↦ ?_⟩
    simp only [Pi.smul_apply, hv.2 i slot]
    split_ifs
    · rfl
    · rw [smul_sub, smul_comm]

variable {D R M}

/-- The defining conditions of a Fox colouring. -/
theorem mem_foxColorings_iff {v : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount → M} :
    v ∈ D.foxColorings R M ↔ (∀ h, v (.inl (D.edgePair.val h)) = v (.inl h)) ∧
      ∀ i slot, v (.inl (D.crossing i (slot + 2))) =
        if D.isOver i slot then v (.inl (D.crossing i slot))
        else 2 • v (.inl (D.crossing i (slot + 1))) - v (.inl (D.crossing i slot)) :=
  Iff.rfl

variable {v : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount → M}

/-- A Fox colouring gives the two half-edges of an arc the same label. -/
theorem apply_edgePair_of_mem_foxColorings (hv : v ∈ D.foxColorings R M) (h : Fin (4 * n)) :
    v (.inl (D.edgePair.val h)) = v (.inl h) :=
  (mem_foxColorings_iff.1 hv).1 h

/-- A Fox colouring gives the two half-edges of the over-strand at a crossing the same label. -/
theorem apply_crossing_add_two_of_mem_foxColorings_of_isOver
    (hv : v ∈ D.foxColorings R M) {i : Fin n}
    {slot : Fin 4} (h : D.isOver i slot = true) :
    v (.inl (D.crossing i (slot + 2))) = v (.inl (D.crossing i slot)) := by
  rw [(mem_foxColorings_iff.1 hv).2 i slot]
  simp only [h, ↓reduceIte]

/-- Along the under-strand at a crossing, a Fox colouring satisfies
`v (s + 2) = 2 • v (s + 1) - v s`, where `s + 1` is an over-slot. -/
theorem apply_crossing_add_two_of_mem_foxColorings_of_not_isOver
    (hv : v ∈ D.foxColorings R M) {i : Fin n}
    {slot : Fin 4} (h : D.isOver i slot = false) :
    v (.inl (D.crossing i (slot + 2))) =
      2 • v (.inl (D.crossing i (slot + 1))) - v (.inl (D.crossing i slot)) := by
  rw [(mem_foxColorings_iff.1 hv).2 i slot]
  simp only [h, Bool.false_eq_true, ↓reduceIte]

variable (D R) in
/-- Every constant family is a Fox colouring. -/
@[simp↓]
theorem const_mem_foxColorings (m : M) :
    Function.const (Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) m ∈ D.foxColorings R M := by
  refine mem_foxColorings_iff.2 ⟨fun _ ↦ rfl, fun i slot ↦ ?_⟩
  split_ifs
  · rfl
  · simp [two_nsmul]

variable (R M) in
/-- Every family is a Fox colouring of a crossing-free code: there are no arcs between crossings
and no crossings, so each circle carries an arbitrary label. -/
@[simp]
theorem foxColorings_eq_top_of_zero_crossings (D : PDCode 0) : D.foxColorings R M = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ ⟨fun h ↦ h.elim0, fun i ↦ i.elim0⟩

variable (R M) in
/-- A crossing-free code of `c` circles has `|M| ^ c` Fox colourings. -/
theorem natCard_foxColorings_of_zero_crossings (D : PDCode 0) :
    Nat.card (D.foxColorings R M) = Nat.card M ^ D.crossinglessComponentCount := by
  rw [foxColorings_eq_top_of_zero_crossings, Nat.card_congr Submodule.topEquiv.toEquiv,
    Nat.card_fun, Nat.card_sum,
    Nat.card_eq_fintype_card (α := Fin (4 * 0)), Nat.card_eq_fintype_card (α := Fin _),
    Fintype.card_fin, Fintype.card_fin, Nat.mul_zero, Nat.zero_add]

end PDCode

namespace OrientedPDCode

variable (R M : Type*) [Semiring R] [AddCommGroup M] [Module R M]

/-- The crossing-free unknot has `|M|` Fox colourings: a label for its single circle. -/
theorem natCard_foxColorings_unknot (o : Bool) :
    Nat.card ((unknot o).foxColorings R M) = Nat.card M := by
  rw [PDCode.natCard_foxColorings_of_zero_crossings, ← card_crossinglessComponents,
    crossinglessComponents_unknot, Multiset.card_singleton, pow_one]

end OrientedPDCode

end TauCeti
