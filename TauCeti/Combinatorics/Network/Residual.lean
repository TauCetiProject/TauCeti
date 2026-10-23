/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Order.Interval.Set.Defs
public import TauCeti.Combinatorics.Network.Excess

/-!
# Residual arrows and the residual update

Let `Q` be an arrow family on `V` with lower and upper bounds `lo hi : Assignment Q K`, and let
`f` be a feasible assignment, `lo ≤ f ≤ hi` arrowwise; feasibility is membership in the order
interval `Set.Icc lo hi` for the pointwise order on assignments. The *residual arrows* from `v`
to `w` are the forward copies `e⁺` of the arrows `e : Q v w` together with the reverse copies `e⁻`
of the arrows `e : Q w v`. A forward copy has *residual capacity* `hi e - f e`, the room left to
increase `f e`; a reverse copy has residual capacity `f e - lo e`, the room left to decrease it.
The residual arrow family does not depend on `f`, and zero-capacity residual arrows are retained.

Given any assignment `r` of the residual arrows, the *residual update* of `f` by `r` is
`f' e = f e + r e⁺ - r e⁻`. Augmentation along residual paths and cycles is the case of a residual
assignment supported on a path or cycle, for ordinary flows as well as for assignments with signed
lower bounds. We prove:

* if `0 ≤ r ≤` the residual capacities, then `f'` is feasible;
* `excessAt f' = excessAt f + excessAt r` at every vertex, with no conservation hypothesis on `r`;
  so a residual circulation preserves every excess, and a residual `s`–`t` assignment changes the
  excess only at `s` and `t`, raising it at `t` and lowering it at `s` by its value;
* conversely every feasible assignment is a residual update of `f` by a feasible residual
  assignment, so the feasible residual updates of `f` are exactly the feasible assignments.

## Main definitions

* `TauCeti.ResidualHom Q`: the residual arrow family `fun v w ↦ Q v w ⊕ Q w v`.
* `TauCeti.residualCapacity lo hi f`: the residual capacities of `f`.
* `TauCeti.residualNet`: the net change `r e⁺ - r e⁻` of a residual assignment, as an additive
  homomorphism.
* `TauCeti.residualUpdate f r`: the residual update `f + residualNet r`.

## Main results

* `TauCeti.excessAt_residualNet`: passing from residual arrows to net changes preserves excess.
* `TauCeti.residualUpdate_mem_Icc`: feasible residual updates are feasible.
* `TauCeti.excessAt_residualUpdate`: excess is additive under residual updates.
* `TauCeti.residualCapacity_residualUpdate`: the residual capacities after a residual update.
* `TauCeti.excessAt_residualUpdate_source`: a residual assignment conserved away from `s` and `t`
  lowers the excess at `s` by its value at `t`.
* `TauCeti.image_residualUpdate_Icc`: the residual updates of a feasible `f` by feasible residual
  assignments are exactly the feasible assignments.
* `TauCeti.Assignment.map_residualCapacity` and `TauCeti.Assignment.map_residualUpdate`:
  residual capacities and residual updates commute with additive coefficient maps.

## Implementation notes

The residual arrows are tagged by `Sum.inl` (forward) and `Sum.inr` (reverse) rather than by
their direction relative to the original arrow family, so that a forward copy of an arrow
`v → w` and a reverse copy of an antiparallel arrow `w → v` remain distinct residual arrows from
`v` to `w`, as do the two residual copies of a loop. Bounds are separate parameters, so the
results apply to any arrow family carrying lower and upper bounds.

## References

* R. K. Ahuja, T. L. Magnanti, J. B. Orlin, *Network Flows: Theory, Algorithms, and
  Applications*, Prentice Hall, 1993 (residual networks).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003
  (residual graphs and augmentation).
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

variable (Q) in
/-- The *residual arrow family* of `Q`: a residual arrow from `v` to `w` is either a forward copy
`Sum.inl e` of an arrow `e : Q v w` or a reverse copy `Sum.inr e` of an arrow `e : Q w v`. -/
abbrev ResidualHom (v w : V) : Type v :=
  Q v w ⊕ Q w v

section Sub

variable [Sub K]

/-- The *residual capacities* of an assignment `f` with lower and upper bounds `lo` and `hi`: the
forward copy of an arrow `e` has capacity `hi e - f e` and its reverse copy has capacity
`f e - lo e`. -/
def residualCapacity (lo hi f : Assignment Q K) : Assignment (ResidualHom Q) K :=
  fun _ _ e ↦ Sum.elim (fun e ↦ hi e - f e) (fun e ↦ f e - lo e) e

@[simp]
theorem residualCapacity_inl (lo hi f : Assignment Q K) {v w : V} (e : Q v w) :
    residualCapacity lo hi f (Sum.inl e : ResidualHom Q v w) = hi e - f e :=
  (rfl)

@[simp]
theorem residualCapacity_inr (lo hi f : Assignment Q K) {v w : V} (e : Q w v) :
    residualCapacity lo hi f (Sum.inr e : ResidualHom Q v w) = f e - lo e :=
  (rfl)

end Sub

/-- Residual capacities commute with additive coefficient maps. -/
theorem Assignment.map_residualCapacity [AddGroup K] {L F : Type*} [AddGroup L] [FunLike F K L]
    [AddMonoidHomClass F K L] (φ : F) (lo hi f : Assignment Q K) :
    (residualCapacity lo hi f).map φ = residualCapacity (lo.map φ) (hi.map φ) (f.map φ) := by
  funext _ _ e
  rcases e with e | e <;> simp

section AddCommGroup

variable [AddCommGroup K]

/-- The *net change* of a residual assignment `r`: the value of `r` on the forward copy of an
arrow minus its value on the reverse copy. -/
def residualNet : Assignment (ResidualHom Q) K →+ Assignment Q K where
  toFun r _ _ e := r (Sum.inl e) - r (Sum.inr e)
  map_zero' := by
    funext _ _ e
    exact sub_self 0
  map_add' r r' := by
    funext _ _ e
    exact add_sub_add_comm _ _ _ _

@[simp]
theorem residualNet_apply (r : Assignment (ResidualHom Q) K) {v w : V} (e : Q v w) :
    residualNet r e = r (Sum.inl e) - r (Sum.inr e) :=
  (rfl)

/-- The *residual update* of `f` by a residual assignment `r`: the value on each arrow `e` is
`f e + r e⁺ - r e⁻`, where `e⁺ = Sum.inl e` and `e⁻ = Sum.inr e` are its residual copies. -/
def residualUpdate (f : Assignment Q K) (r : Assignment (ResidualHom Q) K) : Assignment Q K :=
  f + residualNet r

theorem residualUpdate_def (f : Assignment Q K) (r : Assignment (ResidualHom Q) K) :
    residualUpdate f r = f + residualNet r :=
  (rfl)

@[simp]
theorem residualUpdate_apply (f : Assignment Q K) (r : Assignment (ResidualHom Q) K) {v w : V}
    (e : Q v w) : residualUpdate f r e = f e + r (Sum.inl e) - r (Sum.inr e) :=
  (add_sub_assoc _ _ _).symm

@[simp]
theorem residualUpdate_zero (f : Assignment Q K) : residualUpdate f 0 = f := by
  simp [residualUpdate_def]

/-- Updating by `r` and then by `r'` is updating by `r + r'`. -/
theorem residualUpdate_residualUpdate (f : Assignment Q K) (r r' : Assignment (ResidualHom Q) K) :
    residualUpdate (residualUpdate f r) r' = residualUpdate f (r + r') := by
  simp [residualUpdate_def, add_assoc]

section Map

variable {L F : Type*} [AddCommGroup L] [FunLike F K L] [AddMonoidHomClass F K L]

theorem Assignment.map_residualNet (φ : F) (r : Assignment (ResidualHom Q) K) :
    (residualNet r).map φ = residualNet (r.map φ) := by
  funext _ _ e
  simp

/-- Residual updates commute with additive coefficient maps. -/
theorem Assignment.map_residualUpdate (φ : F) (f : Assignment Q K)
    (r : Assignment (ResidualHom Q) K) :
    (residualUpdate f r).map φ = residualUpdate (f.map φ) (r.map φ) := by
  rw [residualUpdate_def, residualUpdate_def, map_add, map_residualNet]

end Map

/-- Residual updates preserve values in an additive subgroup: if `f` and `r` take values in `H`,
so does the residual update of `f` by `r`. -/
theorem residualUpdate_mem (H : AddSubgroup K) {f : Assignment Q K}
    {r : Assignment (ResidualHom Q) K} (hf : ∀ ⦃v w⦄ (e : Q v w), f e ∈ H)
    (hr : ∀ ⦃v w⦄ (e : ResidualHom Q v w), r e ∈ H) {v w : V} (e : Q v w) :
    residualUpdate f r e ∈ H := by
  rw [residualUpdate_apply]
  exact H.sub_mem (H.add_mem (hf e) (hr _)) (hr _)

/-- Residual capacities take values in an additive subgroup containing the bounds and the
assignment. -/
theorem residualCapacity_mem (H : AddSubgroup K) {lo hi f : Assignment Q K}
    (hlo : ∀ ⦃v w⦄ (e : Q v w), lo e ∈ H) (hhi : ∀ ⦃v w⦄ (e : Q v w), hi e ∈ H)
    (hf : ∀ ⦃v w⦄ (e : Q v w), f e ∈ H) {v w : V} (e : ResidualHom Q v w) :
    residualCapacity lo hi f e ∈ H := by
  rcases e with e | e
  · exact H.sub_mem (hhi e) (hf e)
  · exact H.sub_mem (hf e) (hlo e)

/-- **Residual capacities after a residual update.** Updating `f` by `r` lowers the residual
capacity of a residual arrow `a` by the value of `r` on `a` and raises it by the value of `r` on the
reverse residual arrow `a.swap`, the other residual copy of the same arrow. -/
theorem residualCapacity_residualUpdate (lo hi f : Assignment Q K)
    (r : Assignment (ResidualHom Q) K) {v w : V} (a : ResidualHom Q v w) :
    residualCapacity lo hi (residualUpdate f r) a =
      residualCapacity lo hi f a - r a + r (a.swap : ResidualHom Q w v) := by
  rcases a with e | e <;> simp only [residualCapacity_inl, residualCapacity_inr, Sum.swap_inl,
    Sum.swap_inr, residualUpdate_apply] <;> abel

/-- The residual capacity on the residual arrows from `S` to `T` is the room left on the arrows
from `S` to `T` plus the room left to decrease the arrows from `T` to `S`. -/
theorem arrowSum_residualCapacity [∀ v w, Fintype (Q v w)] (lo hi f : Assignment Q K)
    (S T : Finset V) :
    arrowSum (residualCapacity lo hi f) S T = arrowSum (hi - f) S T + arrowSum (f - lo) T S := by
  simp only [arrowSum_def, Fintype.sum_sum_type, residualCapacity_inl, residualCapacity_inr,
    sum_add_distrib, Pi.sub_apply]
  congr 1
  exact sum_comm

section Excess

variable [Fintype V] [∀ v w, Fintype (Q v w)]

/-- Passing from a residual assignment to its net change preserves excess: a forward copy carries
value along its arrow, and a reverse copy carries value against it. -/
@[simp]
theorem excessAt_residualNet (r : Assignment (ResidualHom Q) K) (v : V) :
    excessAt (residualNet r) v = excessAt r v := by
  simp only [excessAt_def, residualNet_apply, Fintype.sum_sum_type, sum_sub_distrib,
    sum_add_distrib]
  abel

/-- **Excess under residual updates.** The excess of the residual update of `f` by `r` is the
excess of `f` plus the excess of `r` in the residual arrow family. No conservation is assumed. -/
@[simp]
theorem excessAt_residualUpdate (f : Assignment Q K) (r : Assignment (ResidualHom Q) K)
    (v : V) : excessAt (residualUpdate f r) v = excessAt f v + excessAt r v := by
  rw [residualUpdate_def, excessAt_add, excessAt_residualNet]

/-- A residual circulation preserves every excess. -/
theorem IsCirculation.excessAt_residualUpdate {r : Assignment (ResidualHom Q) K}
    (hr : IsCirculation r) (f : Assignment Q K) (v : V) :
    excessAt (residualUpdate f r) v = excessAt f v := by
  rw [TauCeti.excessAt_residualUpdate, (isCirculation_iff r).1 hr v, add_zero]

/-- A residual assignment conserved away from `s` and `t` lowers the excess at `s` by its excess
at `t`. Together with `excessAt_residualUpdate` at `t`, the value of an `s`–`t` assignment rises by
the residual value, and the value of the reversed `t`–`s` assignment falls by it. -/
theorem excessAt_residualUpdate_source {r : Assignment (ResidualHom Q) K} {s t : V}
    (hconserve : ∀ v, v ≠ s → v ≠ t → excessAt r v = 0) (f : Assignment Q K) :
    excessAt (residualUpdate f r) s = excessAt f s - excessAt r t := by
  rw [excessAt_residualUpdate, excessAt_source_eq_neg_sink r hconserve, sub_eq_add_neg]

end Excess

section Order

variable [PartialOrder K] [IsOrderedAddMonoid K]

/-- The residual capacities of a feasible assignment are nonnegative. -/
theorem residualCapacity_nonneg {lo hi f : Assignment Q K} (hf : f ∈ Set.Icc lo hi) :
    0 ≤ residualCapacity lo hi f := by
  intro v w e
  rcases e with e | e
  · exact sub_nonneg.mpr (hf.2 v w e)
  · exact sub_nonneg.mpr (hf.1 w v e)

/-- **Feasibility of residual updates.** Updating an assignment by a residual assignment between
zero and its residual capacities gives an assignment within the bounds. Such a residual assignment
exists only when the residual capacities are nonnegative, that is, when `f` is itself feasible. -/
theorem residualUpdate_mem_Icc {lo hi f : Assignment Q K}
    {r : Assignment (ResidualHom Q) K} (hr : r ∈ Set.Icc 0 (residualCapacity lo hi f)) :
    residualUpdate f r ∈ Set.Icc lo hi := by
  constructor <;> intro v w e <;> rw [residualUpdate_apply]
  · have h₁ : 0 ≤ r (Sum.inl e) := hr.1 v w (Sum.inl e)
    have h₂ : r (Sum.inr e) ≤ f e - lo e := hr.2 w v (Sum.inr e)
    calc lo e = f e + 0 - (f e - lo e) := by abel
      _ ≤ f e + r (Sum.inl e) - r (Sum.inr e) := by gcongr
  · have h₁ : r (Sum.inl e) ≤ hi e - f e := hr.2 v w (Sum.inl e)
    have h₂ : 0 ≤ r (Sum.inr e) := hr.1 w v (Sum.inr e)
    calc f e + r (Sum.inl e) - r (Sum.inr e) ≤ f e + (hi e - f e) - 0 := by gcongr
      _ = hi e := by abel

end Order

section Lattice

variable [Lattice K] [IsOrderedAddMonoid K]

/-- **Completeness of residual updates.** Every feasible assignment `g` is the residual update of
a feasible `f` by a residual assignment between zero and the residual capacities of `f`: put the
positive part of `g - f` on the forward copies and its negative part on the reverse copies. -/
theorem exists_residualUpdate_eq {lo hi f g : Assignment Q K} (hf : f ∈ Set.Icc lo hi)
    (hg : g ∈ Set.Icc lo hi) :
    ∃ r ∈ Set.Icc 0 (residualCapacity lo hi f), residualUpdate f r = g := by
  refine ⟨fun _ _ e ↦ Sum.elim (fun e ↦ (g e - f e)⁺) (fun e ↦ (g e - f e)⁻) e, ⟨?_, ?_⟩, ?_⟩
  · intro v w e
    rcases e with e | e
    · exact posPart_nonneg _
    · exact negPart_nonneg _
  · intro v w e
    rcases e with e | e
    · dsimp only [Sum.elim_inl]
      rw [residualCapacity_inl, posPart_def]
      exact sup_le (sub_le_sub_right (hg.2 v w e) _) (sub_nonneg.mpr (hf.2 v w e))
    · dsimp only [Sum.elim_inr]
      rw [residualCapacity_inr, negPart_def, neg_sub]
      exact sup_le (sub_le_sub_left (hg.1 w v e) _) (sub_nonneg.mpr (hf.1 w v e))
  · funext v w e
    rw [residualUpdate_apply, add_sub_assoc]
    exact (congrArg (f e + ·) (posPart_sub_negPart _)).trans (add_sub_cancel _ _)

/-- The residual updates of a feasible assignment `f` by residual assignments between zero and its
residual capacities are exactly the feasible assignments. -/
theorem image_residualUpdate_Icc {lo hi f : Assignment Q K} (hf : f ∈ Set.Icc lo hi) :
    residualUpdate f '' Set.Icc 0 (residualCapacity lo hi f) = Set.Icc lo hi := by
  ext g
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact residualUpdate_mem_Icc hr
  · intro hg
    exact exists_residualUpdate_eq hf hg

end Lattice

end AddCommGroup

end TauCeti
