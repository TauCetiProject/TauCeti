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

The abbreviations `Network.ExcessFlow` and `Network.ExcessIntervalFlow` specialize these types to
the lower and upper bounds carried by a bundled network.

## References

* D. P. Bertsekas, *Linear Network Optimization*, Section 1.1.3 and Exercises 2.4–2.6.
-/

public section

namespace TauCeti

open Finset

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

namespace Network

variable [Preorder K]

/-- Assignments respecting a network's bounds with prescribed excess `b` at every vertex. -/
abbrev ExcessFlow (N : Network K V) [∀ x y, Fintype (N.Hom x y)] (b : V → K) :=
  TauCeti.ExcessFlow N.lower N.upper b

/-- Assignments respecting a network's bounds whose excess at each vertex lies in the prescribed
interval. -/
abbrev ExcessIntervalFlow (N : Network K V) [∀ x y, Fintype (N.Hom x y)] (a b : V → K) :=
  TauCeti.ExcessIntervalFlow N.lower N.upper a b

end Network

namespace ExcessFlow

variable [Preorder K] {lo hi : Assignment Q K} {b : V → K}

/-- Reindex a prescribed-excess assignment along equalities of its bounds and excess. -/
def congr {lo' hi' : Assignment Q K} {b' : V → K} (hlo : lo = lo') (hhi : hi = hi')
    (hb : b = b') : ExcessFlow lo hi b ≃ ExcessFlow lo' hi' b' :=
  Equiv.subtypeEquivRight fun _ ↦ by subst lo'; subst hi'; subst b'; rfl

@[simp]
theorem congr_apply_val {lo' hi' : Assignment Q K} {b' : V → K} (hlo : lo = lo')
    (hhi : hi = hi') (hb : b = b') (f : ExcessFlow lo hi b) :
    (congr hlo hhi hb f).val = f.val :=
  (rfl)

/-- Reversing a prescribed-excess reindexing reverses each equality. -/
@[simp]
theorem congr_symm {lo' hi' : Assignment Q K} {b' : V → K} (hlo : lo = lo')
    (hhi : hi = hi') (hb : b = b') :
    (congr hlo hhi hb).symm = congr hlo.symm hhi.symm hb.symm :=
  (rfl)

/-- Reindexing a prescribed-excess problem along reflexive equalities is the identity. -/
@[simp]
theorem congr_refl :
    congr (lo := lo) (hi := hi) (b := b) rfl rfl rfl = Equiv.refl _ :=
  (rfl)

/-- A realizing assignment respects its arrow bounds. -/
theorem mem_Icc (f : ExcessFlow lo hi b) : f.val ∈ Set.Icc lo hi := f.property.1

/-- A realizing assignment has the prescribed excess at each vertex. -/
@[simp]
theorem excessAt_eq (f : ExcessFlow lo hi b) (x : V) : excessAt f.val x = b x :=
  congrFun f.property.2 x

/-- On a vertex set that no arrow enters or leaves, such as a weakly connected component, the
prescribed excess of a feasible assignment has total zero. -/
theorem sum_eq_zero_of_forall_mem_iff (f : ExcessFlow lo hi b) {S : Finset V}
    (hS : ∀ ⦃x y⦄, Q x y → (x ∈ S ↔ y ∈ S)) : ∑ v ∈ S, b v = 0 := by
  simpa only [f.excessAt_eq] using sum_excessAt_eq_zero_of_forall_mem_iff f.val hS

/-- Prescribed excess of a feasible assignment has total zero. -/
theorem sum_eq_zero (f : ExcessFlow lo hi b) : ∑ v, b v = 0 :=
  f.sum_eq_zero_of_forall_mem_iff fun _ _ _ ↦ by simp

end ExcessFlow

namespace ExcessFlow

variable [Preorder K] [AddLeftMono K] [DecidableEq V]
variable {lo hi : Assignment Q K} {b : V → K}

/-- Every feasible prescribed-excess assignment satisfies the incoming cut inequality. -/
theorem sum_add_arrowSum_le (f : ExcessFlow lo hi b) (S : Finset V) :
    (∑ v ∈ S, b v) + arrowSum lo S Sᶜ ≤ arrowSum hi Sᶜ S := by
  have hex : ∑ v ∈ S, b v = arrowSum f.val Sᶜ S - arrowSum f.val S Sᶜ := by
    simpa only [← f.property.2] using sum_excessAt_eq_arrowSum_sub f.val S
  rw [hex, sub_add_eq_add_sub, sub_le_iff_le_add]
  exact add_le_add (arrowSum_mono f.mem_Icc.2 Sᶜ S) (arrowSum_mono f.mem_Icc.1 S Sᶜ)

end ExcessFlow

namespace ExcessIntervalFlow

variable [Preorder K] {lo hi : Assignment Q K} {a b : V → K}

/-- Reindex an interval-excess assignment along equalities of its arrow and vertex bounds. -/
def congr {lo' hi' : Assignment Q K} {a' b' : V → K} (hlo : lo = lo') (hhi : hi = hi')
    (ha : a = a') (hb : b = b') :
    ExcessIntervalFlow lo hi a b ≃ ExcessIntervalFlow lo' hi' a' b' :=
  Equiv.subtypeEquivRight fun _ ↦ by subst lo'; subst hi'; subst a'; subst b'; rfl

@[simp]
theorem congr_apply_val {lo' hi' : Assignment Q K} {a' b' : V → K} (hlo : lo = lo')
    (hhi : hi = hi') (ha : a = a') (hb : b = b') (f : ExcessIntervalFlow lo hi a b) :
    (congr hlo hhi ha hb f).val = f.val :=
  (rfl)

/-- Reversing an interval-excess reindexing reverses each equality. -/
@[simp]
theorem congr_symm {lo' hi' : Assignment Q K} {a' b' : V → K} (hlo : lo = lo')
    (hhi : hi = hi') (ha : a = a') (hb : b = b') :
    (congr hlo hhi ha hb).symm = congr hlo.symm hhi.symm ha.symm hb.symm :=
  (rfl)

/-- Reindexing an interval-excess problem along reflexive equalities is the identity. -/
@[simp]
theorem congr_refl :
    congr (lo := lo) (hi := hi) (a := a) (b := b) rfl rfl rfl rfl = Equiv.refl _ :=
  (rfl)

/-- An interval-excess assignment respects its arrow bounds. -/
theorem mem_Icc (f : ExcessIntervalFlow lo hi a b) : f.val ∈ Set.Icc lo hi := f.property.1

/-- An interval-excess assignment respects its vertex bounds. -/
theorem excessAt_mem_Icc (f : ExcessIntervalFlow lo hi a b) :
    excessAt f.val ∈ Set.Icc a b := f.property.2

end ExcessIntervalFlow

namespace ExcessIntervalFlow

variable [PartialOrder K] [IsOrderedAddMonoid K]
variable {lo hi : Assignment Q K} {a b : V → K}

/-- On a vertex set that no arrow enters or leaves, such as a weakly connected component, the
lower vertex bounds have nonpositive total. -/
theorem sum_le_zero_of_forall_mem_iff (f : ExcessIntervalFlow lo hi a b) {S : Finset V}
    (hS : ∀ ⦃x y⦄, Q x y → (x ∈ S ↔ y ∈ S)) : ∑ v ∈ S, a v ≤ 0 :=
  (sum_le_sum fun v _ ↦ f.excessAt_mem_Icc.1 v).trans_eq
    (sum_excessAt_eq_zero_of_forall_mem_iff f.val hS)

/-- On a vertex set that no arrow enters or leaves, such as a weakly connected component, the
upper vertex bounds have nonnegative total. -/
theorem zero_le_sum_of_forall_mem_iff (f : ExcessIntervalFlow lo hi a b) {S : Finset V}
    (hS : ∀ ⦃x y⦄, Q x y → (x ∈ S ↔ y ∈ S)) : 0 ≤ ∑ v ∈ S, b v :=
  (sum_excessAt_eq_zero_of_forall_mem_iff f.val hS).symm.trans_le
    (sum_le_sum fun v _ ↦ f.excessAt_mem_Icc.2 v)

/-- The lower vertex bounds of a feasible problem have nonpositive total. -/
theorem sum_le_zero (f : ExcessIntervalFlow lo hi a b) : ∑ v, a v ≤ 0 :=
  f.sum_le_zero_of_forall_mem_iff fun _ _ _ ↦ by simp

/-- The upper vertex bounds of a feasible problem have nonnegative total. -/
theorem zero_le_sum (f : ExcessIntervalFlow lo hi a b) : 0 ≤ ∑ v, b v :=
  f.zero_le_sum_of_forall_mem_iff fun _ _ _ ↦ by simp

end ExcessIntervalFlow

section Ordered

variable [PartialOrder K] [IsOrderedAddMonoid K]

namespace ExcessIntervalFlow

/-- Subtract a reference assignment, shifting both endpoints of the vertex-excess intervals. -/
def shiftEquiv (lo hi h : Assignment Q K) (a b : V → K) :
    ExcessIntervalFlow lo hi a b ≃
      ExcessIntervalFlow (lo - h) (hi - h) (a - excessAt h) (b - excessAt h) :=
  (Equiv.subRight h).subtypeEquiv fun f ↦ by
    have hex : excessAt (f - h) = excessAt f - excessAt h := excessAt_sub f h
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

/-- Shifting interval excess by the zero assignment is the identity equivalence. -/
theorem shiftEquiv_zero (lo hi : Assignment Q K) (a b : V → K) :
    (shiftEquiv lo hi 0 a b).trans
        (congr (sub_zero lo) (sub_zero hi)
          (by simp only [excessAt_zero, sub_zero])
          (by simp only [excessAt_zero, sub_zero])) =
      Equiv.refl (ExcessIntervalFlow lo hi a b) := by
  apply Equiv.ext
  intro f
  apply Subtype.ext
  simp only [Equiv.trans_apply, congr_apply_val, shiftEquiv_apply_val, Equiv.refl_apply,
    sub_zero]

/-- Successive interval-excess shifts compose by adding their reference assignments. -/
theorem shiftEquiv_add (lo hi h k : Assignment Q K) (a b : V → K) :
    ((shiftEquiv lo hi h a b).trans
        (shiftEquiv (lo - h) (hi - h) k (a - excessAt h) (b - excessAt h))).trans
      (congr (sub_sub lo h k) (sub_sub hi h k)
        (by simp only [excessAt_add, sub_sub])
        (by simp only [excessAt_add, sub_sub])) =
      shiftEquiv lo hi (h + k) a b := by
  apply Equiv.ext
  intro f
  apply Subtype.ext
  simp only [Equiv.trans_apply, congr_apply_val, shiftEquiv_apply_val, sub_sub]

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

/-- Shifting prescribed excess by the zero assignment is the identity equivalence. -/
theorem shiftEquiv_zero (lo hi : Assignment Q K) (b : V → K) :
    (shiftEquiv lo hi 0 b).trans
        (congr (sub_zero lo) (sub_zero hi)
          (by simp only [excessAt_zero, sub_zero])) =
      Equiv.refl (ExcessFlow lo hi b) := by
  apply Equiv.ext
  intro f
  apply Subtype.ext
  simp only [Equiv.trans_apply, congr_apply_val, shiftEquiv_apply_val, Equiv.refl_apply,
    sub_zero]

/-- Successive prescribed-excess shifts compose by adding their reference assignments. -/
theorem shiftEquiv_add (lo hi h k : Assignment Q K) (b : V → K) :
    ((shiftEquiv lo hi h b).trans
        (shiftEquiv (lo - h) (hi - h) k (b - excessAt h))).trans
      (congr (sub_sub lo h k) (sub_sub hi h k)
        (by simp only [excessAt_add, sub_sub])) =
      shiftEquiv lo hi (h + k) b := by
  apply Equiv.ext
  intro f
  apply Subtype.ext
  simp only [Equiv.trans_apply, congr_apply_val, shiftEquiv_apply_val, sub_sub]

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
