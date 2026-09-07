/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Oriented PD-codes

An oriented PD-code records the finite combinatorial data at the crossings of a link.  The
`halfEdge` permutation lists the four visits at each crossing, `edgePair` joins the two visits
belonging to one arc, and `orientation` records the direction of every arc.  The two local
strands at a crossing are distinguished by `overPair`, while `crossingSign` fixes the usual
positive/negative crossing convention.

This is a code-level presentation: planarity and the realization in the plane are intentionally
separate predicates.  Keeping the code finite and explicit makes it the hub for later
Reidemeister moves and for the conversion to Gauss codes, without choosing a privileged geometric
embedding.  The code also carries orientation, as required for oriented knot invariants.

The encoding follows Lickorish, *An Introduction to Knot Theory*, GTM 175, Chapter 1.  No planar
realization theorem is asserted here; that is the subsequent geometric-to-combinatorial step.

## Main definitions

* `TauCeti.OrientedPDCode`: a signed, oriented PD-code with `n` crossings.
* `TauCeti.OrientedPDCode.mirror`: reflection, which reverses all crossing signs.
* `TauCeti.OrientedPDCode.relabel`: relabelling of the half-edge and crossing indices.

## Main results

* `TauCeti.OrientedPDCode.crossingSign_eq_one_or_neg_one` records that every crossing sign
  is genuinely positive or negative.
* `TauCeti.OrientedPDCode.mirror_mirror` and `relabel_relabel` show respectively that reflection
  is involutive and that relabelling is an action.
* `TauCeti.orientedPDCode_zero` is the empty oriented diagram, providing a nontrivial
  witness for the finite presentation at zero crossings.
-/

public section

namespace TauCeti

open Function

/-- A finite oriented PD-code with `n` crossings.

The `4 * n` half-edges are grouped into four slots for each crossing by `halfEdge`.  The
fixed-point-free involution `edgePair` joins the two visits of each arc.  `orientation` chooses a
direction on each arc, so its values are opposite at paired visits.  `overPair i = false` means
the first two slots at crossing `i` are the over-strand; `true` swaps the two pairs. -/
structure OrientedPDCode (n : ℕ) where
  /-- The half-edge labels occupying the four slots of each crossing. -/
  halfEdge : Equiv.Perm (Fin (4 * n))
  /-- The involution pairing the two visits of each arc. -/
  edgePair : Equiv.Perm (Fin (4 * n))
  /-- Pairing twice returns to the original visit. -/
  edgePair_sq : ∀ h, edgePair (edgePair h) = h
  /-- No visit is paired with itself. -/
  edgePair_ne : ∀ h, edgePair h ≠ h
  /-- The direction on an arc reverses at its paired visit. -/
  orientation : Fin (4 * n) → Bool
  orientation_pair : ∀ h, orientation (edgePair h) = !orientation h
  /-- Which pair of strands is over at each crossing. -/
  overPair : Fin n → Bool
  /-- The sign of each crossing. -/
  crossingSign : Fin n → ℤ
  crossingSign_mem : ∀ i, crossingSign i = 1 ∨ crossingSign i = -1

namespace OrientedPDCode

variable {n : ℕ}

/-- An oriented PD-code is determined by its crossing order, arc pairing, orientations, over-strand
choices, and crossing signs. -/
@[ext]
theorem ext {D E : OrientedPDCode n}
    (hhalf : D.halfEdge = E.halfEdge) (hedge : D.edgePair = E.edgePair)
    (horient : D.orientation = E.orientation) (hover : D.overPair = E.overPair)
    (hsign : D.crossingSign = E.crossingSign) : D = E := by
  cases D
  cases E
  simp_all

/-- The four half-edge labels at a crossing, in cyclic order. -/
@[expose] def crossing (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) : Fin (4 * n) :=
  D.halfEdge (⟨4 * i + slot, by omega⟩)

/-- The explicit formula for the half-edge in a specified crossing slot. -/
@[simp]
theorem crossing_apply (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) :
    D.crossing i slot = D.halfEdge (⟨4 * i + slot, by omega⟩) :=
  by simp [crossing]

/-- Every crossing sign is either positive or negative. -/
theorem crossingSign_eq_one_or_neg_one (D : OrientedPDCode n) (i : Fin n) :
    D.crossingSign i = 1 ∨ D.crossingSign i = -1 :=
  D.crossingSign_mem i

/-- Pairing an arc visit twice returns to that visit. -/
@[simp]
theorem edgePair_apply_edgePair (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.edgePair (D.edgePair h) = h :=
  D.edgePair_sq h

/-- The pairing of arc visits is injective. -/
theorem edgePair_injective (D : OrientedPDCode n) :
    Function.Injective D.edgePair := by
  intro a b hab
  rw [← D.edgePair_sq a, ← D.edgePair_sq b, hab]

/-- An arc visit is never paired with itself. -/
theorem edgePair_ne_self (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.edgePair h ≠ h :=
  D.edgePair_ne h

/-- The two visits of an oriented arc have opposite directions. -/
@[simp]
theorem orientation_edgePair (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.orientation (D.edgePair h) = !D.orientation h :=
  D.orientation_pair h

/-- Reflect a diagram, reversing every crossing sign while preserving its oriented arcs. -/
@[expose] def mirror (D : OrientedPDCode n) : OrientedPDCode n where
  halfEdge := D.halfEdge
  edgePair := D.edgePair
  edgePair_sq := D.edgePair_sq
  edgePair_ne := D.edgePair_ne
  orientation := D.orientation
  orientation_pair := D.orientation_pair
  overPair := D.overPair
  crossingSign := fun i => -D.crossingSign i
  crossingSign_mem := by
    intro i
    rcases D.crossingSign_mem i with h | h
    · right; simp [h]
    · left; simp [h]

/-- Reflection leaves the order of the half-edge labels unchanged. -/
@[simp]
theorem mirror_halfEdge (D : OrientedPDCode n) : D.mirror.halfEdge = D.halfEdge :=
  rfl

/-- Reflection reverses the sign of every crossing. -/
@[simp]
theorem mirror_crossingSign (D : OrientedPDCode n) (i : Fin n) :
    D.mirror.crossingSign i = -D.crossingSign i :=
  rfl

/-- Reflecting an oriented PD-code twice gives the original code. -/
@[simp]
theorem mirror_mirror (D : OrientedPDCode n) : D.mirror.mirror = D := by
  apply ext <;> simp [mirror]

/-- Relabel half-edge visits and crossings by permutations.

The relabelling is deliberately independent of the planar realization: it changes only the finite
names, so later equivalence relations can quotient out these bookkeeping choices. -/
@[expose] def relabel (D : OrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) : OrientedPDCode n where
  halfEdge := half * D.halfEdge
  edgePair := half * D.edgePair * half.symm
  edgePair_sq := by
    intro h
    simp [mul_assoc, D.edgePair_sq]
  edgePair_ne := by
    intro h hh
    have := D.edgePair_ne (half.symm h)
    apply this
    simpa [mul_assoc] using congrArg (fun x => half.symm x) hh
  orientation := D.orientation ∘ half.symm
  orientation_pair := by
    intro h
    simp [Function.comp_apply, mul_assoc, D.orientation_pair]
  overPair := D.overPair ∘ cross.symm
  crossingSign := D.crossingSign ∘ cross.symm
  crossingSign_mem := by
    intro i
    simpa [Function.comp_apply] using D.crossingSign_mem (cross.symm i)

/-- The crossing sign after relabelling is read at the old crossing name. -/
@[simp]
theorem relabel_crossingSign (D : OrientedPDCode n)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) (i : Fin n) :
    (D.relabel half cross).crossingSign i = D.crossingSign (cross.symm i) :=
  by simp [relabel]

/-- Relabelling by identity permutations does nothing. -/
@[simp]
theorem relabel_refl (D : OrientedPDCode n) :
    D.relabel (Equiv.refl _) (Equiv.refl _) = D := by
  apply ext
  · ext x
    rfl
  · ext x
    rfl
  · rfl
  · rfl
  · rfl

/-- Consecutive relabellings compose their half-edge and crossing permutations. -/
@[simp]
theorem relabel_relabel (D : OrientedPDCode n)
    (half₁ half₂ : Equiv.Perm (Fin (4 * n))) (cross₁ cross₂ : Equiv.Perm (Fin n)) :
    (D.relabel half₁ cross₁).relabel half₂ cross₂ =
      D.relabel (half₂ * half₁) (cross₂ * cross₁) := by
  apply ext
  · ext x
    rfl
  · ext x
    rfl
  · rfl
  · rfl
  · rfl

end OrientedPDCode

/-- The empty oriented PD-code. -/
@[expose] def orientedPDCode_zero : OrientedPDCode 0 where
  halfEdge := Equiv.refl _
  edgePair := Equiv.refl _
  edgePair_sq := by intro h; exact rfl
  edgePair_ne := by intro h; exact Fin.elim0 h
  orientation := fun h => nomatch h
  orientation_pair := by intro h; exact nomatch h
  overPair := fun h => nomatch h
  crossingSign := fun h => nomatch h
  crossingSign_mem := by intro h; exact nomatch h

/-- Reflection fixes the empty PD-code. -/
@[simp]
theorem orientedPDCode_zero_mirror :
    orientedPDCode_zero.mirror = orientedPDCode_zero := by
  refine OrientedPDCode.ext rfl rfl rfl rfl ?_
  funext i
  exact Fin.elim0 i

/-- A one-crossing positive PD-code, with two arcs paired across the crossing.

This concrete code is useful as a sanity check that the presentation permits genuine crossings,
not only the empty link. -/
@[expose] def orientedPDCode_one : OrientedPDCode 1 where
  halfEdge := Equiv.refl _
  edgePair := Equiv.swap 0 1 * Equiv.swap 2 3
  edgePair_sq := by
    intro h
    fin_cases h <;> simp [Equiv.swap_apply_def]
  edgePair_ne := by
    intro h
    fin_cases h <;> simp [Equiv.swap_apply_def]
  orientation := fun h => decide (h = 1 ∨ h = 3)
  orientation_pair := by
    intro h
    fin_cases h <;> simp [Equiv.swap_apply_def]
  overPair := fun _ => false
  crossingSign := fun _ => 1
  crossingSign_mem := by intro i; left; rfl

@[simp]
theorem orientedPDCode_one_crossingSign :
    orientedPDCode_one.crossingSign 0 = 1 :=
  rfl

@[simp]
theorem orientedPDCode_one_mirror_crossingSign :
    orientedPDCode_one.mirror.crossingSign 0 = -1 := by
  simp

end TauCeti
