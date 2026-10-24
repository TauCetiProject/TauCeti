/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Excess
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Group.Int

/-!
# Shifting bounded assignments and prescribed excess

Subtracting a reference assignment translates both arrow bounds and vertex excess. The reference
need not be feasible. This gives equivalences for exact and interval excess problems and, by
subtracting the lower bound, reduces signed bounds to nonnegative capacities. Subtracting a
feasible reference instead reduces its prescribed-excess problem to a circulation problem.

`Realizes` and `RealizesWithin` use the same arrow assignments and interval bounds as
`BoundedFlow`; their extra constraint prescribes excess at every vertex. Excess is incoming minus
outgoing, so the shifted demand is the original demand minus the reference excess.

## References

* D. P. Bertsekas, *Linear Network Optimization*, Section 1.1.3 and Exercises 2.4–2.6.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}
variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

/-- Arrow assignments between `lo` and `hi` whose excess is the prescribed function `b`.
Positive excess denotes demand; negative excess denotes supply. -/
abbrev Realizes [Preorder K] (lo hi : Assignment Q K) (b : V → K) :=
  {f : Assignment Q K // f ∈ Set.Icc lo hi ∧ excessAt f = b}

/-- Arrow assignments between `lo` and `hi` whose excess lies between `a` and `b`.
The vertex bounds constrain net excess, rather than total traffic through a vertex. -/
abbrev RealizesWithin [Preorder K] (lo hi : Assignment Q K) (a b : V → K) :=
  {f : Assignment Q K // f ∈ Set.Icc lo hi ∧ excessAt f ∈ Set.Icc a b}

namespace Realizes

variable [Preorder K] {lo hi : Assignment Q K} {b : V → K}

/-- A realizing assignment respects its arrow bounds. -/
theorem mem_Icc (f : Realizes lo hi b) : f.val ∈ Set.Icc lo hi := f.property.1

/-- A realizing assignment has the prescribed excess at each vertex. -/
@[simp]
theorem excessAt_eq (f : Realizes lo hi b) (x : V) : excessAt f.val x = b x :=
  congrFun f.property.2 x

end Realizes

namespace RealizesWithin

variable [Preorder K] {lo hi : Assignment Q K} {a b : V → K}

/-- An interval-excess assignment respects its arrow bounds. -/
theorem mem_Icc (f : RealizesWithin lo hi a b) : f.val ∈ Set.Icc lo hi := f.property.1

/-- An interval-excess assignment respects its vertex bounds. -/
theorem excessAt_mem_Icc (f : RealizesWithin lo hi a b) :
    excessAt f.val ∈ Set.Icc a b := f.property.2

end RealizesWithin

section Ordered

variable [PartialOrder K] [IsOrderedAddMonoid K]

namespace Realizes

/-- Subtract an arbitrary reference assignment, shifting arrow bounds and prescribed excess.
The inverse adds the reference assignment. -/
def shiftEquiv (lo hi h : Assignment Q K) (b : V → K) :
    Realizes lo hi b ≃ Realizes (lo - h) (hi - h) (b - excessAt h) :=
  (Equiv.subRight h).subtypeEquiv fun f ↦ by
    simp only [Equiv.subRight_apply, Set.sub_mem_Icc_iff_left, sub_add_cancel]
    simp only [funext_iff, excessAt_sub, Pi.sub_apply, sub_left_inj]

@[simp]
theorem shiftEquiv_apply_val (lo hi h : Assignment Q K) (b : V → K)
    (f : Realizes lo hi b) : (shiftEquiv lo hi h b f).val = f.val - h :=
  (rfl)

@[simp]
theorem shiftEquiv_symm_apply_val (lo hi h : Assignment Q K) (b : V → K)
    (f : Realizes (lo - h) (hi - h) (b - excessAt h)) :
    ((shiftEquiv lo hi h b).symm f).val = f.val + h :=
  (rfl)

/-- A shift by a subgroup-valued reference preserves subgroup membership arrowwise. -/
theorem shiftEquiv_apply_mem_iff (lo hi h : Assignment Q K) (b : V → K)
    (H : AddSubgroup K) (hh : ∀ ⦃x y⦄ (e : Q x y), h e ∈ H)
    (f : Realizes lo hi b) {x y : V} (e : Q x y) :
    (shiftEquiv lo hi h b f).val e ∈ H ↔ f.val e ∈ H := by
  simpa [sub_eq_add_neg] using H.add_mem_cancel_right (y := f.val e) (H.neg_mem (hh e))

/-- Subtracting the lower bound turns the arrow constraints into ordinary capacity constraints. -/
def shiftLowerEquiv (lo hi : Assignment Q K) (b : V → K) :
    Realizes lo hi b ≃ Realizes 0 (hi - lo) (b - excessAt lo) :=
  (shiftEquiv lo hi lo b).trans (Equiv.subtypeEquivRight fun f ↦ by simp)

@[simp]
theorem shiftLowerEquiv_apply_val (lo hi : Assignment Q K) (b : V → K)
    (f : Realizes lo hi b) : (shiftLowerEquiv lo hi b f).val = f.val - lo :=
  (rfl)

@[simp]
theorem shiftLowerEquiv_symm_apply_val (lo hi : Assignment Q K) (b : V → K)
    (f : Realizes 0 (hi - lo) (b - excessAt lo)) :
    ((shiftLowerEquiv lo hi b).symm f).val = f.val + lo :=
  (rfl)

/-- Relative to a feasible reference, the prescribed-excess problem is a circulation problem. -/
def circulationEquiv {lo hi : Assignment Q K} {b : V → K} (h : Realizes lo hi b) :
    Realizes lo hi b ≃ {f : Assignment Q K //
      f ∈ Set.Icc (lo - h.val) (hi - h.val) ∧ IsCirculation f} :=
  (shiftEquiv lo hi h.val b).trans (Equiv.subtypeEquivRight fun f ↦ by
    simp only [funext_iff, Pi.sub_apply, h.excessAt_eq, sub_self, isCirculation_iff])

@[simp]
theorem circulationEquiv_apply_val {lo hi : Assignment Q K} {b : V → K}
    (h f : Realizes lo hi b) : (circulationEquiv h f).val = f.val - h.val :=
  (rfl)

@[simp]
theorem circulationEquiv_symm_apply_val {lo hi : Assignment Q K} {b : V → K}
    (h : Realizes lo hi b) (f : {f : Assignment Q K //
      f ∈ Set.Icc (lo - h.val) (hi - h.val) ∧ IsCirculation f}) :
    ((circulationEquiv h).symm f).val = f.val + h.val :=
  (rfl)

end Realizes

namespace RealizesWithin

/-- Subtract a reference assignment, shifting both endpoints of the vertex-excess intervals. -/
def shiftEquiv (lo hi h : Assignment Q K) (a b : V → K) :
    RealizesWithin lo hi a b ≃
      RealizesWithin (lo - h) (hi - h) (a - excessAt h) (b - excessAt h) :=
  (Equiv.subRight h).subtypeEquiv fun f ↦ by
    have hex : excessAt (f - h) = excessAt f - excessAt h := funext (excessAt_sub f h)
    simp only [Equiv.subRight_apply, hex, Set.sub_mem_Icc_iff_left, sub_add_cancel]

@[simp]
theorem shiftEquiv_apply_val (lo hi h : Assignment Q K) (a b : V → K)
    (f : RealizesWithin lo hi a b) : (shiftEquiv lo hi h a b f).val = f.val - h :=
  (rfl)

@[simp]
theorem shiftEquiv_symm_apply_val (lo hi h : Assignment Q K) (a b : V → K)
    (f : RealizesWithin (lo - h) (hi - h) (a - excessAt h) (b - excessAt h)) :
    ((shiftEquiv lo hi h a b).symm f).val = f.val + h :=
  (rfl)

/-- Interval-excess shifts also preserve any additive subgroup containing the reference. -/
theorem shiftEquiv_apply_mem_iff (lo hi h : Assignment Q K) (a b : V → K)
    (H : AddSubgroup K) (hh : ∀ ⦃x y⦄ (e : Q x y), h e ∈ H)
    (f : RealizesWithin lo hi a b) {x y : V} (e : Q x y) :
    (shiftEquiv lo hi h a b f).val e ∈ H ↔ f.val e ∈ H := by
  simpa [sub_eq_add_neg] using H.add_mem_cancel_right (y := f.val e) (H.neg_mem (hh e))

/-- Equal excess endpoints give exactly the prescribed-excess problem, with the same assignment. -/
def equivRealizes (lo hi : Assignment Q K) (b : V → K) :
    RealizesWithin lo hi b b ≃ Realizes lo hi b :=
  Equiv.subtypeEquivRight fun f ↦ by simp

omit [IsOrderedAddMonoid K] in
@[simp]
theorem equivRealizes_apply_val (lo hi : Assignment Q K) (b : V → K)
    (f : RealizesWithin lo hi b b) : (equivRealizes lo hi b f).val = f.val :=
  (rfl)

omit [IsOrderedAddMonoid K] in
@[simp]
theorem equivRealizes_symm_apply_val (lo hi : Assignment Q K) (b : V → K)
    (f : Realizes lo hi b) : ((equivRealizes lo hi b).symm f).val = f.val :=
  (rfl)

end RealizesWithin

end Ordered

/-! ### Signed-bound examples -/

-- A circulation whose asymmetric lower bound has nonzero excess. Subtracting that lower bound
-- therefore produces a prescribed-excess problem, rather than a circulation problem.
example :
    let Q : Bool → Bool → Type := fun _ _ ↦ Unit
    let lo : Assignment Q ℤ := fun x y _ ↦ if x = false ∧ y = true then 1 else 0
    let hi : Assignment Q ℤ := fun _ _ _ ↦ 2
    ∃ f : Realizes lo hi 0,
      (Realizes.shiftLowerEquiv lo hi 0 f).val (x := false) (y := true) () = 0 ∧
      excessAt (Realizes.shiftLowerEquiv lo hi 0 f).val false = 1 ∧
      excessAt (Realizes.shiftLowerEquiv lo hi 0 f).val true = -1 := by
  intro Q lo hi
  have hf : (fun _ _ _ ↦ 1 : Assignment Q ℤ) ∈ Set.Icc lo hi := by
    constructor
    · intro x y e
      dsimp [lo]
      split_ifs <;> norm_num
    · intro x y e
      norm_num [hi]
  have he : excessAt (fun _ _ _ ↦ 1 : Assignment Q ℤ) = 0 := by
    funext x
    cases x <;> simp [excessAt_def]
  refine ⟨⟨fun _ _ _ ↦ 1, hf, he⟩, ?_, ?_, ?_⟩
  · simp [lo]
  · simp [excessAt_def, lo]
  · simp [excessAt_def, lo]

-- The reference may lie outside both original bounds. The resulting signed assignment still
-- has exactly the shifted bounds and excess, and the inverse recovers the original assignment.
example :
    let Q : Bool → Bool → Type := fun _ _ ↦ Unit
    let lo : Assignment Q ℤ := fun _ _ _ ↦ -2
    let hi : Assignment Q ℤ := fun _ _ _ ↦ 1
    let h : Assignment Q ℤ := fun _ _ _ ↦ 3
    ∃ f : Realizes lo hi 0,
      (Realizes.shiftEquiv lo hi h 0 f).val (x := false) (y := true) () = -4 ∧
      (Realizes.shiftEquiv lo hi h 0).symm (Realizes.shiftEquiv lo hi h 0 f) = f := by
  intro Q lo hi h
  have hf : (fun _ _ _ ↦ -1 : Assignment Q ℤ) ∈ Set.Icc lo hi := by
    constructor <;> intro x y e <;> norm_num [lo, hi]
  have he : excessAt (fun _ _ _ ↦ -1 : Assignment Q ℤ) = 0 := by
    funext x
    cases x <;> simp [excessAt_def]
  refine ⟨⟨fun _ _ _ ↦ -1, hf, he⟩, ?_, ?_⟩
  · simp [h]
  · exact Equiv.symm_apply_apply _ _

end TauCeti
