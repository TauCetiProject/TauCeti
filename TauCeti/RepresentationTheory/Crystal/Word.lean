/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Basic

/-!
# Words of crystal operators

A word of simple roots acts by successive partial raising or lowering operators, read from
left to right. Reversing the word and exchanging raising with lowering gives its partial
inverse. These operations describe generation from a highest element without choosing a
reduced Weyl-group expression.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1–2.
-/

public section

namespace TauCeti.NormalCrystal

variable {ι X Y B : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} (c : NormalCrystal P b B)

/-- Apply the raising operators of a word from left to right, stopping when one is undefined. -/
def eWord (w : List b.support) (x : B) : Option B :=
  w.foldlM (fun x i ↦ c.e i x) x

/-- Apply the lowering operators of a word from left to right, stopping when one is undefined. -/
def fWord (w : List b.support) (x : B) : Option B :=
  w.foldlM (fun x i ↦ c.f i x) x

@[simp]
theorem eWord_nil (x : B) : c.eWord [] x = some x := (rfl)

@[simp]
theorem fWord_nil (x : B) : c.fWord [] x = some x := (rfl)

/-- A word acts first by its initial letter. -/
theorem eWord_cons (i : b.support) (w : List b.support) (x : B) :
    c.eWord (i :: w) x = (c.e i x).bind (c.eWord w) := (rfl)

/-- A word acts first by its initial letter. -/
theorem fWord_cons (i : b.support) (w : List b.support) (x : B) :
    c.fWord (i :: w) x = (c.f i x).bind (c.fWord w) := (rfl)

/-- Concatenating words composes their partial raising actions. -/
theorem eWord_append (v w : List b.support) (x : B) :
    c.eWord (v ++ w) x = (c.eWord v x).bind (c.eWord w) := by
  induction v generalizing x with
  | nil => simp
  | cons i v ih => simp only [List.cons_append, eWord_cons, ih, Option.bind_assoc]

/-- Concatenating words composes their partial lowering actions. -/
theorem fWord_append (v w : List b.support) (x : B) :
    c.fWord (v ++ w) x = (c.fWord v x).bind (c.fWord w) := by
  induction v generalizing x with
  | nil => simp
  | cons i v ih => simp only [List.cons_append, fWord_cons, ih, Option.bind_assoc]

@[simp]
theorem eWord_singleton (i : b.support) (x : B) : c.eWord [i] x = c.e i x := by
  simp [eWord_cons]

@[simp]
theorem fWord_singleton (i : b.support) (x : B) : c.fWord [i] x = c.f i x := by
  simp [fWord_cons]

@[simp]
theorem dual_eWord (w : List b.support) (x : B) : c.dual.eWord w x = c.fWord w x := by
  simp only [eWord, fWord, dual_e]

@[simp]
theorem dual_fWord (w : List b.support) (x : B) : c.dual.fWord w x = c.eWord w x := by
  simp only [eWord, fWord, dual_f]

/-- The partial inverse of a raising word is the reversed lowering word. -/
theorem eWord_eq_some_iff {w : List b.support} {x y : B} :
    c.eWord w x = some y ↔ c.fWord w.reverse y = some x := by
  induction w generalizing x y with
  | nil => simp [eq_comm]
  | cons i w ih =>
    simp only [eWord_cons, List.reverse_cons, fWord_append, fWord_singleton,
      Option.bind_eq_some_iff, ih, c.e_eq_some_iff]
    exact ⟨fun ⟨z, hz, hy⟩ ↦ ⟨z, hy, hz⟩, fun ⟨z, hy, hz⟩ ↦ ⟨z, hz, hy⟩⟩

/-- The partial inverse of a lowering word is the reversed raising word. -/
theorem fWord_eq_some_iff {w : List b.support} {x y : B} :
    c.fWord w x = some y ↔ c.eWord w.reverse y = some x := by
  simpa using c.dual.eWord_eq_some_iff (w := w) (x := x) (y := y)

/-- A raising word adds the sum of its simple roots to the weight. -/
theorem wt_of_eWord_eq_some {w : List b.support} {x y : B}
    (h : c.eWord w x = some y) :
    c.wt y = c.wt x + (w.map fun i : b.support ↦ P.root i).sum := by
  induction w generalizing x with
  | nil =>
    obtain rfl := Option.some.inj h
    simp
  | cons i w ih =>
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp (c.eWord_cons i w x ▸ h)
    rw [ih h, c.wt_of_e_eq_some hz, List.map_cons, List.sum_cons, add_assoc]

/-- A lowering word subtracts the sum of its simple roots from the weight. -/
theorem wt_of_fWord_eq_some {w : List b.support} {x y : B}
    (h : c.fWord w x = some y) :
    c.wt y = c.wt x - (w.map fun i : b.support ↦ P.root i).sum := by
  have hwt := c.wt_of_eWord_eq_some (c.fWord_eq_some_iff.mp h)
  rw [List.map_reverse, List.sum_reverse] at hwt
  exact eq_sub_iff_add_eq.mpr hwt.symm

/-- A raising word defined on a highest element must be empty. -/
theorem eWord_eq_some_iff_of_highest {x y : B} (hx : ∀ i, c.e i x = none)
    (w : List b.support) : c.eWord w x = some y ↔ w = [] ∧ x = y := by
  cases w with
  | nil => simp
  | cons i w => simp [eWord_cons, hx]

end TauCeti.NormalCrystal
