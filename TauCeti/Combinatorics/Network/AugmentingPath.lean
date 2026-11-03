/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Extr
public import TauCeti.Combinatorics.Network.Augmentation

/-!
# Augmenting paths and the optimality of flows

A bounded `s`–`t` assignment `f` is *maximum* when no bounded `s`–`t` assignment has a larger
value. An *augmenting walk* for `f` is a walk from `s` to `t` in the residual network of `f` that
traverses only residual arrows of positive capacity, so the sink is positively reachable from the
source for the residual capacities. This file proves the augmenting-path optimality criterion of
Ford and Fulkerson: for distinct terminals the following are equivalent.

1. `f` is maximum.
2. There is no augmenting walk for `f`.
3. The value of `f` equals the cut bound of some vertex set containing `s` but not `t`.

If an augmenting walk exists, then augmenting along an augmenting path inside it by its bottleneck
increases the value. If there is none, then no residual arrow of positive capacity leaves the set
of vertices positively reachable from `s`, so by the residual cut gap identity
`TauCeti.BoundedFlow.cutBound_sub_val` the value equals the cut bound of that set. Weak duality
turns the equality of value and cut bound into maximality. The same criteria hold for ordinary
flows, with cut capacities in place of cut bounds.

These criteria hold over every linearly ordered additive commutative group of coefficients. They
do not by themselves give the existence of a maximum flow, which needs a terminating choice of
augmentations. One augmentation step, along an augmenting walk by its bottleneck, is the relation
`TauCeti.Flow.AugmentsTo`; a flow between distinct terminals is maximum exactly when no step
starts from it.

## Main definitions

* `TauCeti.BoundedFlow.IsMaximum` and `TauCeti.BoundedFlow.IsMinimum`: bounded `s`–`t`
  assignments of largest and smallest value, exchanged by terminal swap.
* `TauCeti.Flow.IsMaximum`: an ordinary `s`–`t` flow of largest value.
* `TauCeti.Flow.AugmentsTo`: one augmentation step, along an augmenting walk by its bottleneck.

## Main results

* `TauCeti.BoundedFlow.exists_val_lt_of_positiveReachable`: augmentation along an augmenting walk
  increases the value.
* `TauCeti.BoundedFlow.val_eq_cutBound_of_not_positiveReachable`: without an augmenting walk, the
  value equals the cut bound of the vertices positively reachable from the source.
* `TauCeti.BoundedFlow.tfae_isMaximum` and `TauCeti.Flow.tfae_isMaximum`: the augmenting-path
  optimality criterion for bounded `s`–`t` assignments and for ordinary flows.
* `TauCeti.Flow.isMaximum_iff_forall_not_augmentsTo`: a flow is maximum exactly when no
  augmentation step starts from it.

## References

* L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*, Canadian J. Math. 8 (1956).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Theorem 10.1 and Corollary 10.1a.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

variable [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K]

namespace BoundedFlow

section Preorder

variable [Preorder K] {lo hi : Assignment Q K} {s t : V}

/-- A bounded `s`–`t` assignment is *maximum* when it maximizes the value among all bounded
`s`–`t` assignments for the same bounds. -/
def IsMaximum (f : BoundedFlow lo hi s t) : Prop :=
  IsMaxOn val Set.univ f

theorem isMaximum_iff {f : BoundedFlow lo hi s t} :
    f.IsMaximum ↔ ∀ g : BoundedFlow lo hi s t, g.val ≤ f.val :=
  isMaxOn_univ_iff

/-- When the terminals coincide, every bounded assignment is maximum. -/
theorem isMaximum_of_eq (hst : s = t) (f : BoundedFlow lo hi s t) : f.IsMaximum :=
  isMaximum_iff.2 fun g ↦ (val_eq_zero_of_eq hst g).trans_le (val_eq_zero_of_eq hst f).ge

/-- A bounded terminal assignment is minimum when no other feasible assignment has smaller
terminal value. No sign condition is imposed on that value. -/
def IsMinimum (f : BoundedFlow lo hi s t) : Prop :=
  IsMinOn val Set.univ f

theorem isMinimum_iff {f : BoundedFlow lo hi s t} :
    f.IsMinimum ↔ ∀ g : BoundedFlow lo hi s t, f.val ≤ g.val :=
  isMinOn_univ_iff

/-- When the terminals coincide, every bounded assignment is minimum. -/
theorem isMinimum_of_eq (hst : s = t) (f : BoundedFlow lo hi s t) : f.IsMinimum :=
  isMinimum_iff.2 fun g ↦ (val_eq_zero_of_eq hst f).trans_le (val_eq_zero_of_eq hst g).ge

end Preorder

/-- All minimum bounded terminal assignments have the same value. -/
theorem IsMinimum.val_eq [PartialOrder K] {lo hi : Assignment Q K} {s t : V}
    {f g : BoundedFlow lo hi s t} (hf : f.IsMinimum) (hg : g.IsMinimum) : f.val = g.val :=
  le_antisymm (isMinimum_iff.1 hf g) (isMinimum_iff.1 hg f)

/-- All maximum bounded `s`–`t` assignments have the same value. -/
theorem IsMaximum.val_eq [PartialOrder K] {lo hi : Assignment Q K} {s t : V}
    {f g : BoundedFlow lo hi s t} (hf : f.IsMaximum) (hg : g.IsMaximum) : f.val = g.val :=
  le_antisymm (isMaximum_iff.1 hg f) (isMaximum_iff.1 hf g)

section PartialOrder

variable [PartialOrder K] [IsOrderedAddMonoid K] {lo hi : Assignment Q K} {s t : V}

/-- Exchanging the terminals exchanges minimum and maximum assignments. -/
@[simp]
theorem isMaximum_swap (f : BoundedFlow lo hi s t) : f.swap.IsMaximum ↔ f.IsMinimum := by
  rw [isMaximum_iff, isMinimum_iff]
  constructor
  · intro h g
    simpa using h g.swap
  · intro h g
    simpa using neg_le_neg (h g.swap)

/-- Exchanging the terminals exchanges maximum and minimum assignments. -/
@[simp]
theorem isMinimum_swap (f : BoundedFlow lo hi s t) : f.swap.IsMinimum ↔ f.IsMaximum := by
  rw [← isMaximum_swap, swap_swap]

/-- A bounded terminal assignment attaining a lower cut bound is minimum. -/
theorem isMinimum_of_val_eq_neg_cutBound_compl [DecidableEq V]
    (f : BoundedFlow lo hi s t) {S : Finset V} (hs : s ∈ S) (ht : t ∉ S)
    (h : f.val = -cutBound lo hi Sᶜ) : f.IsMinimum :=
  isMinimum_iff.2 fun g ↦ h ▸ g.neg_cutBound_compl_le_val hs ht

/-- A bounded `s`–`t` assignment whose value equals the cut bound of a vertex set containing `s`
but not `t` is maximum. -/
theorem isMaximum_of_val_eq_cutBound [DecidableEq V] (f : BoundedFlow lo hi s t) {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) (h : f.val = cutBound lo hi S) : f.IsMaximum :=
  isMaximum_iff.2 fun g ↦ h ▸ g.val_le_cutBound hs ht

open Classical in
/-- If a bounded `s`–`t` assignment has no augmenting walk, then its value equals the cut bound of
the set of vertices positively reachable from the source for its residual capacities. -/
theorem val_eq_cutBound_of_not_positiveReachable [DecidableEq V] (f : BoundedFlow lo hi s t)
    (h : ¬PositiveReachable (residualCapacity lo hi f.toFun) s t) :
    f.val =
      cutBound lo hi (univ.filter (PositiveReachable (residualCapacity lo hi f.toFun) s)) := by
  rw [f.val_eq_cutBound_iff (by simp) (by simpa using h)]
  intro v hv w hw e
  simp only [mem_filter, mem_univ, true_and] at hv hw
  refine ((residualCapacity_nonneg f.mem_Icc v w e).eq_or_lt.resolve_right fun he ↦ ?_).symm
  exact hw (hv.tail e he)

end PartialOrder

section LinearOrder

variable [LinearOrder K] [IsOrderedAddMonoid K] {lo hi : Assignment Q K} {s t : V}

/-- **Augmentation.** If the sink of a bounded `s`–`t` assignment between distinct terminals is
positively reachable from the source for its residual capacities, then augmenting along an
augmenting path by its bottleneck gives a bounded `s`–`t` assignment of larger value. -/
theorem exists_val_lt_of_positiveReachable (hst : s ≠ t) (f : BoundedFlow lo hi s t)
    (h : PositiveReachable (residualCapacity lo hi f.toFun) s t) :
    ∃ g : BoundedFlow lo hi s t, f.val < g.val := by
  obtain ⟨p, hp, hpos⟩ := positiveReachable_iff_exists_isPath.1 h
  have hne : p.arrows ≠ [] := p.arrows_ne_nil hst
  have hq : 0 < p.bottleneck (residualCapacity lo hi f.toFun) hne :=
    ArrowWalk.lt_bottleneck_iff.2 hpos
  refine ⟨f.update (walkFlow p hp.nodup_arrows hq.le (residualCapacity_nonneg f.mem_Icc)
    fun _ ha ↦ ArrowWalk.bottleneck_le ha).toBoundedFlow, ?_⟩
  rw [val_update, val_walkFlow hst]
  exact lt_add_of_pos_right _ hq

/-- A maximum bounded `s`–`t` assignment between distinct terminals has no augmenting walk. -/
theorem IsMaximum.not_positiveReachable (hst : s ≠ t) {f : BoundedFlow lo hi s t}
    (hf : f.IsMaximum) : ¬PositiveReachable (residualCapacity lo hi f.toFun) s t := fun h ↦
  have ⟨g, hg⟩ := exists_val_lt_of_positiveReachable hst f h
  (hg.trans_le (isMaximum_iff.1 hf g)).false

/-- **Augmenting-path optimality criterion.** For a bounded `s`–`t` assignment `f` between distinct
terminals, the following are equivalent: `f` is maximum; there is no augmenting walk, that is, the
sink is not positively reachable from the source for the residual capacities of `f`; and the
value of `f` equals the cut bound of some vertex set containing `s` but not `t`. -/
theorem tfae_isMaximum [DecidableEq V] (hst : s ≠ t) (f : BoundedFlow lo hi s t) :
    List.TFAE [f.IsMaximum, ¬PositiveReachable (residualCapacity lo hi f.toFun) s t,
      ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = cutBound lo hi S] := by
  tfae_have 1 → 2 := IsMaximum.not_positiveReachable hst
  tfae_have 2 → 3 := fun h ↦ by
    classical
    exact ⟨_, by simp, by simpa using h, f.val_eq_cutBound_of_not_positiveReachable h⟩
  tfae_have 3 → 1 := fun ⟨S, hs, ht, h⟩ ↦ f.isMaximum_of_val_eq_cutBound hs ht h
  tfae_finish

/-- A bounded `s`–`t` assignment between distinct terminals is maximum exactly when it has no
augmenting walk. -/
theorem isMaximum_iff_not_positiveReachable (hst : s ≠ t) (f : BoundedFlow lo hi s t) :
    f.IsMaximum ↔ ¬PositiveReachable (residualCapacity lo hi f.toFun) s t := by
  classical
  exact (f.tfae_isMaximum hst).out 1 2

/-- A maximum bounded `s`–`t` assignment between distinct terminals attains the cut bound of some
vertex set containing `s` but not `t`. -/
theorem IsMaximum.exists_val_eq_cutBound [DecidableEq V] (hst : s ≠ t)
    {f : BoundedFlow lo hi s t} (hf : f.IsMaximum) :
    ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = cutBound lo hi S :=
  ((f.tfae_isMaximum hst).out 1 3).1 hf

/-- A bounded terminal assignment is minimum exactly when its residual network has no positive
path from the sink to the source. -/
theorem isMinimum_iff_not_positiveReachable (hst : s ≠ t) (f : BoundedFlow lo hi s t) :
    f.IsMinimum ↔ ¬PositiveReachable (residualCapacity lo hi f.toFun) t s := by
  rw [← isMaximum_swap, isMaximum_iff_not_positiveReachable hst.symm, swap_toFun]

/-- A minimum bounded terminal assignment attains a lower cut bound. -/
theorem IsMinimum.exists_val_eq_neg_cutBound_compl [DecidableEq V] (hst : s ≠ t)
    {f : BoundedFlow lo hi s t} (hf : f.IsMinimum) :
    ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = -cutBound lo hi Sᶜ := by
  obtain ⟨T, ht, hs, hT⟩ := ((isMaximum_swap f).2 hf).exists_val_eq_cutBound hst.symm
  refine ⟨Tᶜ, by simpa using hs, by simpa using ht, ?_⟩
  rw [compl_compl, ← neg_neg f.val, ← val_swap, hT]

end LinearOrder

end BoundedFlow

/-! ### Ordinary flows -/

namespace Flow

section Preorder

variable [Preorder K] {cap : Assignment Q K} {s t : V}

/-- An ordinary `s`–`t` flow is *maximum* when it maximizes the value among all ordinary `s`–`t`
flows for the same capacities. -/
def IsMaximum (f : Flow cap s t) : Prop :=
  IsMaxOn (fun g : Flow cap s t ↦ g.val) Set.univ f

theorem isMaximum_iff {f : Flow cap s t} : f.IsMaximum ↔ ∀ g : Flow cap s t, g.val ≤ f.val :=
  isMaxOn_univ_iff

end Preorder

/-- An ordinary flow is maximum among ordinary flows exactly when it is maximum among all bounded
assignments with zero lower bounds: a bounded assignment of larger value has positive value, so it
is itself an ordinary flow. -/
@[simp]
theorem isMaximum_toBoundedFlow [LinearOrder K] {cap : Assignment Q K} {s t : V}
    (f : Flow cap s t) : f.toBoundedFlow.IsMaximum ↔ f.IsMaximum := by
  rw [BoundedFlow.isMaximum_iff, isMaximum_iff]
  refine ⟨fun hf g ↦ hf g.toBoundedFlow, fun hf g ↦ le_of_not_gt fun hg ↦ ?_⟩
  have hg₀ : 0 ≤ excessAt g.toFun t := by
    rw [← BoundedFlow.val_def]
    exact f.val_nonneg.trans hg.le
  exact (hf ⟨g, hg₀⟩).not_gt hg

section LinearOrder

variable [LinearOrder K] [IsOrderedAddMonoid K] {cap : Assignment Q K} {s t : V}

/-- **Augmenting-path optimality criterion for ordinary flows.** For an ordinary `s`–`t` flow `f`
between distinct terminals, the following are equivalent: `f` is maximum; there is no augmenting
walk for `f`; and the value of `f` equals the capacity of the arrows leaving some vertex set
containing `s` but not `t`. -/
theorem tfae_isMaximum [DecidableEq V] (hst : s ≠ t) (f : Flow cap s t) :
    List.TFAE [f.IsMaximum, ¬PositiveReachable (residualCapacity 0 cap f.toFun) s t,
      ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = arrowSum cap S Sᶜ] := by
  simpa using f.toBoundedFlow.tfae_isMaximum hst

/-- An ordinary `s`–`t` flow between distinct terminals is maximum exactly when it has no
augmenting walk. -/
theorem isMaximum_iff_not_positiveReachable (hst : s ≠ t) (f : Flow cap s t) :
    f.IsMaximum ↔ ¬PositiveReachable (residualCapacity 0 cap f.toFun) s t := by
  classical
  exact (f.tfae_isMaximum hst).out 1 2

/-- A maximum ordinary `s`–`t` flow between distinct terminals saturates some cut: its value
equals the capacity of the arrows leaving some vertex set containing `s` but not `t`. -/
theorem IsMaximum.exists_val_eq_arrowSum [DecidableEq V] (hst : s ≠ t) {f : Flow cap s t}
    (hf : f.IsMaximum) : ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = arrowSum cap S Sᶜ :=
  ((f.tfae_isMaximum hst).out 1 3).1 hf

/-! ### Augmentation steps -/

/-- `f.AugmentsTo g` when the flow `g` arises from `f` by one augmentation step: augmentation by
its bottleneck along an augmenting walk of `f`, a residual walk from `s` to `t` that traverses at
least one arrow, traverses no arrow twice, and has positive residual capacity on every arrow. -/
def AugmentsTo (f g : Flow cap s t) : Prop :=
  ∃ (p : ArrowWalk (ResidualHom Q) s t) (hp : p.arrows.Nodup) (hne : p.arrows ≠ []),
    (∀ a ∈ p.arrows, 0 < residualCapacity 0 cap f.toFun a.2.2) ∧
      f.augmentBottleneck p hp hne = g

theorem augmentsTo_iff {f g : Flow cap s t} :
    f.AugmentsTo g ↔ ∃ (p : ArrowWalk (ResidualHom Q) s t) (hp : p.arrows.Nodup)
      (hne : p.arrows ≠ []), (∀ a ∈ p.arrows, 0 < residualCapacity 0 cap f.toFun a.2.2) ∧
        f.augmentBottleneck p hp hne = g :=
  Iff.rfl

/-- Augmentation by the bottleneck along an augmenting walk is an augmentation step. -/
theorem augmentsTo_augmentBottleneck (f : Flow cap s t) {p : ArrowWalk (ResidualHom Q) s t}
    (hp : p.arrows.Nodup) (hne : p.arrows ≠ [])
    (hpos : ∀ a ∈ p.arrows, 0 < residualCapacity 0 cap f.toFun a.2.2) :
    f.AugmentsTo (f.augmentBottleneck p hp hne) :=
  ⟨p, hp, hne, hpos, rfl⟩

/-- An augmentation step between distinct terminals strictly increases the value. -/
theorem AugmentsTo.val_lt (hst : s ≠ t) {f g : Flow cap s t} (h : f.AugmentsTo g) :
    f.val < g.val := by
  obtain ⟨p, hp, hne, hpos, rfl⟩ := h
  exact val_lt_val_augmentBottleneck hst hpos

/-- An augmentation step preserves values in an additive subgroup that contains the capacities. -/
theorem AugmentsTo.mem {H : AddSubgroup K} (hcap : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ H)
    {f g : Flow cap s t} (h : f.AugmentsTo g) (hf : ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ H) {v w : V}
    (e : Q v w) : g.toFun e ∈ H := by
  obtain ⟨p, hp, hne, -, rfl⟩ := h
  exact augmentBottleneck_mem hcap hf e

/-- An ordinary flow between distinct terminals is maximum exactly when no augmentation step
starts from it. -/
theorem isMaximum_iff_forall_not_augmentsTo (hst : s ≠ t) (f : Flow cap s t) :
    f.IsMaximum ↔ ∀ g, ¬f.AugmentsTo g := by
  refine ⟨fun hf g hg ↦ (hg.val_lt hst).not_ge (isMaximum_iff.1 hf g), fun h ↦ ?_⟩
  rw [isMaximum_iff_not_positiveReachable hst, positiveReachable_iff_exists_isPath]
  rintro ⟨p, hp, hpos⟩
  exact h _ (f.augmentsTo_augmentBottleneck hp.nodup_arrows (p.arrows_ne_nil hst) hpos)

end LinearOrder

end Flow

end TauCeti
