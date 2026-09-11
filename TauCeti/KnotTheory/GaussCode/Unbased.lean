/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Basic
public import TauCeti.KnotTheory.GaussCode.Basic
import TauCeti.GroupTheory.Perm.Basic

/-!
# Unbased oriented Gauss codes

A based oriented Gauss code records a linear traversal beginning immediately after a chosen point
of the knot diagram. The underlying cyclic traversal has no preferred beginning. This file removes
that artificial choice by quotienting based codes by cyclic rotation of their visit indices.

The generator `BasedOrientedGaussCode.rotateBasepoint` moves the beginning forward by one visit.
The quotient `OrientedGaussCode` therefore identifies precisely the integral powers of this
rotation, while retaining the orientation, over/under data, crossing signs, and crossing labels.
It is the Gauss-code presentation appropriate for comparison with an oriented PD-code, whose
half-edge data likewise carries no base point.

As for the based presentation, no planarity condition is imposed: an unbased code is cyclic
combinatorial crossing data, not by itself a claim that the code is realised by a planar diagram.

Mirroring, reversing orientation, relabelling crossings, and writhe all descend to the quotient.
Reversal conjugates forward basepoint rotation to backward rotation; this is why it remains
well-defined even though it does not commute with the chosen generator.

The cyclic-word convention follows W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate
Texts in Mathematics 175, Chapter 1.

## Main definitions

* `TauCeti.BasedOrientedGaussCode.rotateBasepoint`: cyclically rotate the traversal by one visit.
* `TauCeti.OrientedGaussCode`: oriented Gauss codes with no chosen base point.
* `TauCeti.BasedOrientedGaussCode.forgetBasepoint`: forget the chosen beginning of the traversal.

## Main results

* `TauCeti.BasedOrientedGaussCode.forgetBasepoint_eq_iff`: two based codes determine the same
  unbased code exactly when one is an integral basepoint rotation of the other.
* `TauCeti.OrientedGaussCode.mirror`, `TauCeti.OrientedGaussCode.reverse`, and
  `TauCeti.OrientedGaussCode.relabel`: the structural operations on unbased codes.
* `TauCeti.OrientedGaussCode.writhe`: writhe is independent of the base point.
-/

public section

namespace TauCeti

namespace BasedOrientedGaussCode

variable {n : ℕ}

/-- Change the names of the visit positions, transporting the partner matching with them. This is
an implementation device for cyclic rotation; arbitrary changes of visit positions are not an
operation on cyclic Gauss words. -/
private def reindexVisits (D : BasedOrientedGaussCode n) (e : Equiv.Perm (Fin (2 * n))) :
    BasedOrientedGaussCode n where
  visit := D.visit ∘ e.symm
  over := D.over ∘ e.symm
  sign := D.sign
  partner := PerfectMatching.congr e D.partner
  visit_eq_iff := by
    intro i j
    simp only [Function.comp_apply, D.visit_eq_iff, PerfectMatching.congr_val_apply]
    constructor
    · rintro (h | h)
      · exact Or.inl (e.symm.injective h)
      · exact Or.inr (e.symm.injective (by simpa using h))
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr (by simpa using congrArg e.symm h)
  over_partner := by
    intro i
    simp [Function.comp_def]

private theorem reindexVisits_trans (D : BasedOrientedGaussCode n)
    (e f : Equiv.Perm (Fin (2 * n))) :
    (D.reindexVisits e).reindexVisits f = D.reindexVisits (e.trans f) := by
  apply ext <;> funext i <;> simp [reindexVisits, Function.comp_def]

private theorem reindexVisits_refl (D : BasedOrientedGaussCode n) :
    D.reindexVisits (Equiv.refl (Fin (2 * n))) = D := by
  apply ext <;> funext i <;> simp [reindexVisits]

/-- Move the base point of a based oriented Gauss code forward by one visit in the oriented
traversal. This cyclically shifts the visit and over/under sequences and transports the partner
matching; crossing labels and signs are unchanged. -/
def rotateBasepoint (n : ℕ) : Equiv.Perm (BasedOrientedGaussCode n) where
  toFun D := D.reindexVisits (finRotate (2 * n)).symm
  invFun D := D.reindexVisits (finRotate (2 * n))
  left_inv D := by
    dsimp
    rw [reindexVisits_trans]
    simpa using D.reindexVisits_refl
  right_inv D := by
    dsimp
    rw [reindexVisits_trans]
    simpa using D.reindexVisits_refl

/-- After moving the base point forward, visit `i` contains the data formerly at the next visit. -/
@[simp]
theorem visit_rotateBasepoint (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    (rotateBasepoint n D).visit i = D.visit (finRotate (2 * n) i) := by
  simp [rotateBasepoint, reindexVisits]

/-- Moving the base point backward reads the data at the preceding visit. -/
@[simp]
theorem visit_rotateBasepoint_symm (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    ((rotateBasepoint n).symm D).visit i = D.visit ((finRotate (2 * n)).symm i) := by
  simp [rotateBasepoint, reindexVisits]

/-- Moving the base point forward cyclically shifts the over/under sequence. -/
@[simp]
theorem over_rotateBasepoint (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    (rotateBasepoint n D).over i = D.over (finRotate (2 * n) i) := by
  simp [rotateBasepoint, reindexVisits]

/-- Moving the base point backward cyclically shifts the over/under sequence backward. -/
@[simp]
theorem over_rotateBasepoint_symm (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    ((rotateBasepoint n).symm D).over i = D.over ((finRotate (2 * n)).symm i) := by
  simp [rotateBasepoint, reindexVisits]

/-- Moving the base point does not change crossing signs. -/
@[simp]
theorem sign_rotateBasepoint (D : BasedOrientedGaussCode n) :
    (rotateBasepoint n D).sign = D.sign := by
  simp [rotateBasepoint, reindexVisits]

/-- Moving the base point backward does not change crossing signs. -/
@[simp]
theorem sign_rotateBasepoint_symm (D : BasedOrientedGaussCode n) :
    ((rotateBasepoint n).symm D).sign = D.sign := by
  simp [rotateBasepoint, reindexVisits]

/-- Moving the base point transports the partner matching by the same cyclic relabelling of
visits. -/
@[simp]
theorem partner_rotateBasepoint (D : BasedOrientedGaussCode n) :
    (rotateBasepoint n D).partner =
      PerfectMatching.congr (finRotate (2 * n)).symm D.partner := by
  rfl

/-- Moving the base point backward transports the partner matching by the inverse cyclic
relabelling of visits. -/
@[simp]
theorem partner_rotateBasepoint_symm (D : BasedOrientedGaussCode n) :
    ((rotateBasepoint n).symm D).partner =
      PerfectMatching.congr (finRotate (2 * n)) D.partner := by
  rfl

/-- Moving the base point preserves writhe. -/
@[simp]
theorem writhe_rotateBasepoint (D : BasedOrientedGaussCode n) :
    (rotateBasepoint n D).writhe = D.writhe := by
  simp [writhe_def]

/-- Mirroring a based code commutes with moving its base point. -/
@[simp]
theorem mirror_rotateBasepoint (D : BasedOrientedGaussCode n) :
    (rotateBasepoint n D).mirror = rotateBasepoint n D.mirror := by
  apply ext <;> funext i <;> simp

/-- Reversing orientation turns a forward basepoint rotation into a backward one. -/
@[simp]
theorem reverse_rotateBasepoint (D : BasedOrientedGaussCode n) :
    (rotateBasepoint n D).reverse = (rotateBasepoint n).symm D.reverse := by
  apply ext
  · funext i
    rw [visit_reverse, visit_rotateBasepoint, visit_rotateBasepoint_symm, visit_reverse]
    exact congrArg D.visit (rev_finRotate_symm i).symm
  · funext i
    rw [over_reverse, over_rotateBasepoint, over_rotateBasepoint_symm, over_reverse]
    exact congrArg D.over (rev_finRotate_symm i).symm
  · rw [sign_reverse, sign_rotateBasepoint, sign_rotateBasepoint_symm, sign_reverse]

/-- Relabelling crossings commutes with moving the base point. -/
@[simp]
theorem relabel_rotateBasepoint (D : BasedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (rotateBasepoint n D).relabel e = rotateBasepoint n (D.relabel e) := by
  apply ext <;> funext i <;> simp

private def unbasedSetoid (n : ℕ) : Setoid (BasedOrientedGaussCode n) :=
  Equiv.Perm.SameCycle.setoid (rotateBasepoint n)

end BasedOrientedGaussCode

/-- An oriented Gauss code with no chosen base point, obtained from based oriented Gauss codes by
cyclically rotating the traversal. -/
def OrientedGaussCode (n : ℕ) :=
  Quotient (BasedOrientedGaussCode.unbasedSetoid n)

namespace BasedOrientedGaussCode

variable {n : ℕ}

/-- Forget the chosen base point of an oriented Gauss code. -/
def forgetBasepoint (D : BasedOrientedGaussCode n) : OrientedGaussCode n :=
  Quotient.mk'' D

/-- Two based oriented Gauss codes give the same unbased code exactly when an integral power of
basepoint rotation carries the first to the second. -/
@[simp]
theorem forgetBasepoint_eq_iff {D E : BasedOrientedGaussCode n} :
    D.forgetBasepoint = E.forgetBasepoint ↔
      ∃ k : ℤ, (rotateBasepoint n ^ k) D = E := by
  simp only [forgetBasepoint, OrientedGaussCode, Quotient.eq_iff_equiv]
  rfl

/-- Moving the base point does not change the unbased oriented Gauss code. -/
@[simp]
theorem forgetBasepoint_rotateBasepoint (D : BasedOrientedGaussCode n) :
    (rotateBasepoint n D).forgetBasepoint = D.forgetBasepoint := by
  rw [forgetBasepoint_eq_iff]
  exact ⟨-1, by simp⟩

end BasedOrientedGaussCode

namespace OrientedGaussCode

variable {n : ℕ}

/-- A basepoint-invariant function on based oriented Gauss codes descends to unbased oriented
Gauss codes. -/
protected def lift {α : Sort*} (f : BasedOrientedGaussCode n → α)
    (h : ∀ D, f (BasedOrientedGaussCode.rotateBasepoint n D) = f D) :
    OrientedGaussCode n → α :=
  Quotient.lift f fun _ _ hDE => Equiv.Perm.SameCycle.apply_eq_of_apply_eq hDE h

/-- Applying a lifted basepoint-invariant function to a based representative recovers its value
on that representative. -/
@[simp]
protected theorem lift_forgetBasepoint {α : Sort*} (f : BasedOrientedGaussCode n → α)
    (h : ∀ D, f (BasedOrientedGaussCode.rotateBasepoint n D) = f D)
    (D : BasedOrientedGaussCode n) :
    OrientedGaussCode.lift f h D.forgetBasepoint = f D := by
  simp [OrientedGaussCode.lift, BasedOrientedGaussCode.forgetBasepoint]

/-- To prove a property of an unbased oriented Gauss code, it suffices to prove it for every based
representative. -/
@[elab_as_elim]
protected theorem inductionOn {motive : OrientedGaussCode n → Prop} (D : OrientedGaussCode n)
    (h : ∀ E : BasedOrientedGaussCode n, motive E.forgetBasepoint) : motive D :=
  Quotient.inductionOn D h

/-- The writhe of an unbased oriented Gauss code. -/
def writhe (D : OrientedGaussCode n) : ℤ :=
  OrientedGaussCode.lift BasedOrientedGaussCode.writhe
    BasedOrientedGaussCode.writhe_rotateBasepoint D

/-- The writhe of an unbased code is the writhe of any based representative. -/
@[simp]
theorem writhe_forgetBasepoint (D : BasedOrientedGaussCode n) :
    writhe D.forgetBasepoint = D.writhe := by
  simp [writhe]

/-- Mirror an unbased oriented Gauss code. -/
def mirror (D : OrientedGaussCode n) : OrientedGaussCode n :=
  Quotient.map' BasedOrientedGaussCode.mirror (by
    intro E F h
    exact Equiv.Perm.SameCycle.map h BasedOrientedGaussCode.mirror_rotateBasepoint) D

/-- Mirroring an unbased code is represented by mirroring any based representative. -/
@[simp]
theorem mirror_forgetBasepoint (D : BasedOrientedGaussCode n) :
    mirror D.forgetBasepoint = D.mirror.forgetBasepoint := by
  unfold mirror BasedOrientedGaussCode.forgetBasepoint
  apply Quotient.map'_mk''

/-- Mirroring twice recovers the original unbased oriented Gauss code. -/
@[simp]
theorem mirror_mirror (D : OrientedGaussCode n) : D.mirror.mirror = D := by
  refine D.inductionOn ?_
  simp

/-- Mirroring negates the writhe of an unbased oriented Gauss code. -/
@[simp]
theorem writhe_mirror (D : OrientedGaussCode n) : D.mirror.writhe = -D.writhe := by
  refine D.inductionOn ?_
  simp

/-- Reverse the orientation of an unbased oriented Gauss code. -/
def reverse (D : OrientedGaussCode n) : OrientedGaussCode n :=
  Quotient.map' BasedOrientedGaussCode.reverse (by
    intro E F h
    have h' : (BasedOrientedGaussCode.rotateBasepoint n).SameCycle E F := h
    have hmap := Equiv.Perm.SameCycle.map h'
      BasedOrientedGaussCode.reverse_rotateBasepoint
    exact Equiv.Perm.sameCycle_inv.mp hmap) D

/-- Reversing an unbased code is represented by reversing any based representative. -/
@[simp]
theorem reverse_forgetBasepoint (D : BasedOrientedGaussCode n) :
    reverse D.forgetBasepoint = D.reverse.forgetBasepoint := by
  unfold reverse BasedOrientedGaussCode.forgetBasepoint
  apply Quotient.map'_mk''

/-- Reversing orientation twice recovers the original unbased oriented Gauss code. -/
@[simp]
theorem reverse_reverse (D : OrientedGaussCode n) : D.reverse.reverse = D := by
  refine D.inductionOn ?_
  simp

/-- Reversing orientation preserves the writhe of an unbased oriented Gauss code. -/
@[simp]
theorem writhe_reverse (D : OrientedGaussCode n) : D.reverse.writhe = D.writhe := by
  refine D.inductionOn ?_
  simp

/-- Relabel the crossings of an unbased oriented Gauss code. -/
def relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) : OrientedGaussCode n :=
  Quotient.map' (fun E : BasedOrientedGaussCode n => E.relabel e) (by
    intro E F h
    exact Equiv.Perm.SameCycle.map (τ := BasedOrientedGaussCode.rotateBasepoint n)
      (g := fun D => D.relabel e) h fun D => BasedOrientedGaussCode.relabel_rotateBasepoint D e) D

/-- Relabelling an unbased code is represented by relabelling any based representative. -/
@[simp]
theorem relabel_forgetBasepoint (D : BasedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    relabel D.forgetBasepoint e = (D.relabel e).forgetBasepoint := by
  unfold relabel BasedOrientedGaussCode.forgetBasepoint
  apply Quotient.map'_mk''

/-- Relabelling by the identity equivalence has no effect. -/
@[simp]
theorem relabel_refl (D : OrientedGaussCode n) :
    D.relabel (Equiv.refl (Fin n)) = D := by
  refine D.inductionOn ?_
  simp

/-- Successive relabellings compose. -/
@[simp]
theorem relabel_relabel (D : OrientedGaussCode n) (e f : Fin n ≃ Fin n) :
    (D.relabel e).relabel f = D.relabel (e.trans f) := by
  refine D.inductionOn ?_
  simp

/-- Relabelling crossings preserves writhe. -/
@[simp]
theorem writhe_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).writhe = D.writhe := by
  refine D.inductionOn ?_
  simp

/-- Mirroring commutes with relabelling crossings. -/
@[simp]
theorem mirror_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).mirror = D.mirror.relabel e := by
  refine D.inductionOn ?_
  simp

/-- Reversing orientation commutes with relabelling crossings. -/
@[simp]
theorem reverse_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).reverse = D.reverse.relabel e := by
  refine D.inductionOn ?_
  simp

/-- Mirroring and reversing orientation commute. -/
@[simp]
theorem mirror_reverse (D : OrientedGaussCode n) :
    D.reverse.mirror = D.mirror.reverse := by
  refine D.inductionOn ?_
  simp

end OrientedGaussCode

end TauCeti
