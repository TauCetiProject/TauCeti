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

`ExcessFlow` and `ExcessIntervalFlow` use the same arrow assignments and interval bounds as
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
abbrev ExcessFlow [Preorder K] (lo hi : Assignment Q K) (b : V → K) :=
  {f : Assignment Q K // f ∈ Set.Icc lo hi ∧ excessAt f = b}

/-- Arrow assignments between `lo` and `hi` whose excess lies between `a` and `b`.
The vertex bounds constrain net excess, rather than total traffic through a vertex. -/
abbrev ExcessIntervalFlow [Preorder K] (lo hi : Assignment Q K) (a b : V → K) :=
  {f : Assignment Q K // f ∈ Set.Icc lo hi ∧ excessAt f ∈ Set.Icc a b}

namespace ExcessFlow

variable [Preorder K] {lo hi : Assignment Q K} {b : V → K}

/-- A realizing assignment respects its arrow bounds. -/
theorem mem_Icc (f : ExcessFlow lo hi b) : f.val ∈ Set.Icc lo hi := f.property.1

/-- A realizing assignment has the prescribed excess at each vertex. -/
@[simp]
theorem excessAt_eq (f : ExcessFlow lo hi b) (x : V) : excessAt f.val x = b x :=
  congrFun f.property.2 x

end ExcessFlow

namespace ExcessIntervalFlow

variable [Preorder K] {lo hi : Assignment Q K} {a b : V → K}

/-- An interval-excess assignment respects its arrow bounds. -/
theorem mem_Icc (f : ExcessIntervalFlow lo hi a b) : f.val ∈ Set.Icc lo hi := f.property.1

/-- An interval-excess assignment respects its vertex bounds. -/
theorem excessAt_mem_Icc (f : ExcessIntervalFlow lo hi a b) :
    excessAt f.val ∈ Set.Icc a b := f.property.2

end ExcessIntervalFlow

section Ordered

variable [PartialOrder K] [IsOrderedAddMonoid K]

namespace ExcessIntervalFlow

/-- Subtract a reference assignment, shifting both endpoints of the vertex-excess intervals. -/
def shiftEquiv (lo hi h : Assignment Q K) (a b : V → K) :
    ExcessIntervalFlow lo hi a b ≃
      ExcessIntervalFlow (lo - h) (hi - h) (a - excessAt h) (b - excessAt h) :=
  (Equiv.subRight h).subtypeEquiv fun f ↦ by
    have hex : excessAt (f - h) = excessAt f - excessAt h := funext (excessAt_sub f h)
    simp only [Equiv.subRight_apply, hex, Set.sub_mem_Icc_iff_left, sub_add_cancel]

@[simp]
theorem shiftEquiv_apply_val (lo hi h : Assignment Q K) (a b : V → K)
    (f : ExcessIntervalFlow lo hi a b) : (shiftEquiv lo hi h a b f).val = f.val - h :=
  (rfl)

@[simp]
theorem shiftEquiv_symm_apply_val (lo hi h : Assignment Q K) (a b : V → K)
    (f : ExcessIntervalFlow (lo - h) (hi - h) (a - excessAt h) (b - excessAt h)) :
    ((shiftEquiv lo hi h a b).symm f).val = f.val + h :=
  (rfl)

/-- Interval-excess shifts also preserve any additive subgroup containing the reference. -/
theorem shiftEquiv_apply_mem_iff (lo hi h : Assignment Q K) (a b : V → K)
    {M : Type*} [SetLike M K] [AddSubgroupClass M K] (H : M)
    (hh : ∀ ⦃x y⦄ (e : Q x y), h e ∈ H)
    (f : ExcessIntervalFlow lo hi a b) {x y : V} (e : Q x y) :
    (shiftEquiv lo hi h a b f).val e ∈ H ↔ f.val e ∈ H := by
  rw [shiftEquiv_apply_val]
  exact Assignment.sub_apply_mem_iff e (hh e)

/-- Equal excess endpoints give exactly the prescribed-excess problem, with the same assignment. -/
def equivExcessFlow (lo hi : Assignment Q K) (b : V → K) :
    ExcessIntervalFlow lo hi b b ≃ ExcessFlow lo hi b :=
  Equiv.subtypeEquivRight fun f ↦ by simp

omit [IsOrderedAddMonoid K] in
@[simp]
theorem equivExcessFlow_apply_val (lo hi : Assignment Q K) (b : V → K)
    (f : ExcessIntervalFlow lo hi b b) : (equivExcessFlow lo hi b f).val = f.val :=
  (rfl)

omit [IsOrderedAddMonoid K] in
@[simp]
theorem equivExcessFlow_symm_apply_val (lo hi : Assignment Q K) (b : V → K)
    (f : ExcessFlow lo hi b) : ((equivExcessFlow lo hi b).symm f).val = f.val :=
  (rfl)

end ExcessIntervalFlow

namespace ExcessFlow

/-- Subtract an arbitrary reference assignment, shifting arrow bounds and prescribed excess.
The inverse adds the reference assignment. -/
def shiftEquiv (lo hi h : Assignment Q K) (b : V → K) :
    ExcessFlow lo hi b ≃ ExcessFlow (lo - h) (hi - h) (b - excessAt h) :=
  (ExcessIntervalFlow.equivExcessFlow lo hi b).symm.trans
    ((ExcessIntervalFlow.shiftEquiv lo hi h b b).trans
      (ExcessIntervalFlow.equivExcessFlow _ _ _))

@[simp]
theorem shiftEquiv_apply_val (lo hi h : Assignment Q K) (b : V → K)
    (f : ExcessFlow lo hi b) : (shiftEquiv lo hi h b f).val = f.val - h :=
  (rfl)

@[simp]
theorem shiftEquiv_symm_apply_val (lo hi h : Assignment Q K) (b : V → K)
    (f : ExcessFlow (lo - h) (hi - h) (b - excessAt h)) :
    ((shiftEquiv lo hi h b).symm f).val = f.val + h :=
  (rfl)

/-- A shift by a subgroup-valued reference preserves subgroup membership arrowwise. -/
theorem shiftEquiv_apply_mem_iff (lo hi h : Assignment Q K) (b : V → K)
    {M : Type*} [SetLike M K] [AddSubgroupClass M K] (H : M)
    (hh : ∀ ⦃x y⦄ (e : Q x y), h e ∈ H)
    (f : ExcessFlow lo hi b) {x y : V} (e : Q x y) :
    (shiftEquiv lo hi h b f).val e ∈ H ↔ f.val e ∈ H := by
  rw [shiftEquiv_apply_val]
  exact Assignment.sub_apply_mem_iff e (hh e)

/-- Subtracting the lower bound turns the arrow constraints into ordinary capacity constraints. -/
def shiftLowerEquiv (lo hi : Assignment Q K) (b : V → K) :
    ExcessFlow lo hi b ≃ ExcessFlow 0 (hi - lo) (b - excessAt lo) :=
  (shiftEquiv lo hi lo b).trans (Equiv.subtypeEquivRight fun f ↦ by simp)

@[simp]
theorem shiftLowerEquiv_apply_val (lo hi : Assignment Q K) (b : V → K)
    (f : ExcessFlow lo hi b) : (shiftLowerEquiv lo hi b f).val = f.val - lo :=
  (rfl)

@[simp]
theorem shiftLowerEquiv_symm_apply_val (lo hi : Assignment Q K) (b : V → K)
    (f : ExcessFlow 0 (hi - lo) (b - excessAt lo)) :
    ((shiftLowerEquiv lo hi b).symm f).val = f.val + lo :=
  (rfl)

/-- Relative to a feasible reference, the prescribed-excess problem is a circulation problem. -/
def circulationEquiv {lo hi : Assignment Q K} {b : V → K} (h : ExcessFlow lo hi b) :
    ExcessFlow lo hi b ≃ {f : Assignment Q K //
      f ∈ Set.Icc (lo - h.val) (hi - h.val) ∧ IsCirculation f} :=
  (shiftEquiv lo hi h.val b).trans (Equiv.subtypeEquivRight fun f ↦ by
    simp only [funext_iff, Pi.sub_apply, h.excessAt_eq, sub_self, isCirculation_iff])

@[simp]
theorem circulationEquiv_apply_val {lo hi : Assignment Q K} {b : V → K}
    (h f : ExcessFlow lo hi b) : (circulationEquiv h f).val = f.val - h.val :=
  (rfl)

@[simp]
theorem circulationEquiv_symm_apply_val {lo hi : Assignment Q K} {b : V → K}
    (h : ExcessFlow lo hi b) (f : {f : Assignment Q K //
      f ∈ Set.Icc (lo - h.val) (hi - h.val) ∧ IsCirculation f}) :
    ((circulationEquiv h).symm f).val = f.val + h.val :=
  (rfl)

end ExcessFlow

end Ordered

/-! ### Signed-bound examples -/

-- A circulation whose asymmetric lower bound has nonzero excess. Subtracting that lower bound
-- therefore produces a prescribed-excess problem, rather than a circulation problem.
example :
    let Q : Bool → Bool → Type := fun _ _ ↦ Unit
    let lo : Assignment Q ℤ := fun x y _ ↦ if x = false ∧ y = true then 1 else 0
    let hi : Assignment Q ℤ := fun _ _ _ ↦ 2
    ∃ f : ExcessFlow lo hi 0,
      (ExcessFlow.shiftLowerEquiv lo hi 0 f).val (x := false) (y := true) () = 0 ∧
      excessAt (ExcessFlow.shiftLowerEquiv lo hi 0 f).val false = 1 ∧
      excessAt (ExcessFlow.shiftLowerEquiv lo hi 0 f).val true = -1 := by
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
    ∃ f : ExcessFlow lo hi 0,
      (ExcessFlow.shiftEquiv lo hi h 0 f).val (x := false) (y := true) () = -4 ∧
      (ExcessFlow.shiftEquiv lo hi h 0).symm (ExcessFlow.shiftEquiv lo hi h 0 f) = f := by
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
