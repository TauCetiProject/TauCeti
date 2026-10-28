/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.AuxiliaryTerminals
public import TauCeti.Combinatorics.Network.ShortestAugmentation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Flows between vertex sets

Let `Q` be an arrow family on a finite vertex type `V` with capacities `cap`, and let `A` and `B`
be finite vertex sets. An *`A`–`B` flow* is an arrow assignment between zero and the capacities
that is conserved at every vertex outside `A ∪ B`, has nonpositive excess at every vertex of `A`
and nonnegative excess at every vertex of `B`. Its *value* is its total excess on `B`, which is
minus its total excess on `A`. An `A`–`B` cut is a vertex set containing `A` and avoiding `B`, an
admissible side in the sense of `TauCeti.TerminalCut.IsAdmissible`, and its capacity is the total
capacity of the arrows leaving it. Either set may be empty, in which case every `A`–`B` flow has
value zero.

For disjoint `A` and `B` this file proves the max-flow/min-cut theorem between vertex sets: weak
duality, the augmenting-path optimality criterion, the existence of an `A`–`B` flow and an
`A`–`B` cut of equal value and capacity, and integrality in an additive subgroup containing the
capacities. Here an augmenting walk runs from a vertex of `A` to a vertex of `B` along residual
arrows of positive capacity.

The existence results come from the reduction to single terminals. Add a fresh source with an arrow
to each `a ∈ A` of capacity the total capacity leaving `a`, and a fresh sink with an arrow from each
`b ∈ B` of capacity the total capacity entering `b` (`TauCeti.setFlowCapacity`). The `A`–`B` flows
then correspond exactly to the ordinary flows between the fresh terminals, with the same values on
the original arrows and the same value (`TauCeti.SetFlow.auxFlowEquiv`), and normalizing a minimum
cut between the fresh terminals gives a minimum `A`–`B` cut of the same capacity
(`TauCeti.TerminalCut.IsMinimum.isMinimum_union_sdiff`, in
`TauCeti.Combinatorics.Network.AuxiliaryTerminals`).

## Main definitions

* `TauCeti.SetFlow cap A B`: `A`–`B` flows for the capacities `cap`, with value `SetFlow.val`.
* `TauCeti.SetFlow.IsMaximum`: an `A`–`B` flow of largest value.
* `TauCeti.SetFlow.toAuxFlow` and `TauCeti.Flow.toSetFlow`: the ordinary flow of the auxiliary
  network corresponding to an `A`–`B` flow, and the `A`–`B` flow corresponding to an ordinary flow
  of the auxiliary network.
* `TauCeti.SetFlow.auxFlowEquiv`: the correspondence between `A`–`B` flows and ordinary flows of
  the auxiliary network.

## Main results

* `TauCeti.SetFlow.val_eq_arrowSum_sub`: the value is the net value across every `A`–`B` cut.
* `TauCeti.SetFlow.val_le_arrowSum`: weak duality.
* `TauCeti.SetFlow.tfae_isMaximum`: an `A`–`B` flow is maximum exactly when it has no augmenting
  walk, and exactly when its value is the capacity of some `A`–`B` cut.
* `TauCeti.TerminalCut.isAdmissible_filter_positiveReachable`: without augmenting walks, the
  vertices positively reachable from `A` form an `A`–`B` cut.
* `TauCeti.SetFlow.exists_isMaximum_mem`: integrality of maximum `A`–`B` flows.
* `TauCeti.SetFlow.exists_val_eq_arrowSum`: the max-flow/min-cut theorem between vertex sets.

## References

* L. R. Ford, D. R. Fulkerson, *Flows in Networks*, Princeton University Press, 1962.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Chapter 10.
-/

public section

namespace TauCeti

open Finset Sum

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

variable [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K]

/-- An *`A`–`B` flow* for the capacities `cap`: an arrow assignment between zero and `cap` that is
conserved at every vertex outside `A ∪ B`, with nonpositive excess at every vertex of `A` and
nonnegative excess at every vertex of `B`. -/
@[ext]
structure SetFlow [Preorder K] (cap : Assignment Q K) (A B : Finset V) where
  /-- The value on each arrow. -/
  toFun : Assignment Q K
  /-- The assignment lies between zero and the capacities. -/
  mem_Icc : toFun ∈ Set.Icc 0 cap
  /-- The assignment is conserved at every vertex outside `A ∪ B`. -/
  conserve : ∀ v, v ∉ A → v ∉ B → excessAt toFun v = 0
  /-- Every vertex of `A` is a supply vertex. -/
  excessAt_nonpos : ∀ a ∈ A, excessAt toFun a ≤ 0
  /-- Every vertex of `B` is a demand vertex. -/
  excessAt_nonneg : ∀ b ∈ B, 0 ≤ excessAt toFun b

omit [∀ v w, Fintype (Q v w)] [AddCommGroup K] in
open Classical in
/-- If no vertex of `B` is positively reachable from a vertex of `A` for the capacities `c`, then
the vertices positively reachable from `A` form an `A`–`B` cut. -/
theorem TerminalCut.isAdmissible_filter_positiveReachable [Zero K] [LT K] {c : Assignment Q K}
    {A B : Finset V} (h : ∀ a ∈ A, ∀ b ∈ B, ¬PositiveReachable c a b) :
    TerminalCut.IsAdmissible A B (univ.filter fun v ↦ ∃ a ∈ A, PositiveReachable c a v) := by
  refine TerminalCut.isAdmissible_iff.2
    ⟨fun a ha ↦ mem_filter.2 ⟨mem_univ a, a, ha, .refl _ a⟩, disjoint_left.2 ?_⟩
  rintro b hb hbB
  obtain ⟨a, ha, hab⟩ := (mem_filter.1 hb).2
  exact h a ha b hbB hab

namespace SetFlow

section Preorder

variable [Preorder K] {cap : Assignment Q K} {A B : Finset V}

theorem nonneg (f : SetFlow cap A B) {x y : V} (e : Q x y) : 0 ≤ f.toFun e :=
  f.mem_Icc.1 x y e

theorem le_cap (f : SetFlow cap A B) {x y : V} (e : Q x y) : f.toFun e ≤ cap e :=
  f.mem_Icc.2 x y e

/-- The *value* of an `A`–`B` flow: its total excess on `B`. -/
def val (f : SetFlow cap A B) : K :=
  ∑ b ∈ B, excessAt f.toFun b

theorem val_def (f : SetFlow cap A B) : f.val = ∑ b ∈ B, excessAt f.toFun b :=
  (rfl)

/-- An `A`–`B` flow is *maximum* when it maximizes the value among all `A`–`B` flows for the same
capacities. -/
def IsMaximum (f : SetFlow cap A B) : Prop :=
  IsMaxOn (fun g : SetFlow cap A B ↦ g.val) Set.univ f

theorem isMaximum_iff {f : SetFlow cap A B} :
    f.IsMaximum ↔ ∀ g : SetFlow cap A B, g.val ≤ f.val :=
  isMaxOn_univ_iff

end Preorder

section PartialOrder

variable [PartialOrder K] {cap : Assignment Q K} {A B : Finset V}

/-- An `A`–`B` flow is conserved at every vertex of `A ∩ B`. -/
theorem excessAt_eq_zero_of_mem_of_mem (f : SetFlow cap A B) {v : V} (hA : v ∈ A) (hB : v ∈ B) :
    excessAt f.toFun v = 0 :=
  (f.excessAt_nonpos v hA).antisymm (f.excessAt_nonneg v hB)

/-- The total excess of an `A`–`B` flow on `A` is minus its value. -/
theorem sum_excessAt_source (f : SetFlow cap A B) :
    ∑ a ∈ A, excessAt f.toFun a = -f.val := by
  classical
  have hunion : ∑ v ∈ A ∪ B, excessAt f.toFun v = 0 := by
    rw [← sum_excessAt f.toFun]
    refine sum_subset (subset_univ _) fun v _ hv ↦ ?_
    rw [mem_union, not_or] at hv
    exact f.conserve v hv.1 hv.2
  have hinter : ∑ v ∈ A ∩ B, excessAt f.toFun v = 0 :=
    sum_eq_zero fun v hv ↦ f.excessAt_eq_zero_of_mem_of_mem (mem_inter.1 hv).1 (mem_inter.1 hv).2
  rw [eq_neg_iff_add_eq_zero, val_def, ← sum_union_inter, hunion, hinter, add_zero]

/-- An `A`–`B` flow with no demand vertices has value zero. -/
@[simp]
theorem val_empty_right (f : SetFlow cap A ∅) : f.val = 0 :=
  sum_empty

/-- An `A`–`B` flow with no supply vertices has value zero. -/
@[simp]
theorem val_empty_left (f : SetFlow cap ∅ B) : f.val = 0 := by
  simpa [eq_comm] using f.sum_excessAt_source

/-- The value of an `A`–`B` flow is the value on arrows leaving `S` minus the value on arrows
entering `S`, for every `A`–`B` cut `S`. -/
theorem val_eq_arrowSum_sub [DecidableEq V] (f : SetFlow cap A B) {S : Finset V}
    (hS : TerminalCut.IsAdmissible A B S) :
    f.val = arrowSum f.toFun S Sᶜ - arrowSum f.toFun Sᶜ S := by
  have hsum : ∑ v ∈ S, excessAt f.toFun v = ∑ a ∈ A, excessAt f.toFun a :=
    (sum_subset hS.subset fun v hvS hvA ↦
      f.conserve v hvA (disjoint_left.1 hS.disjoint hvS)).symm
  rw [← neg_sub, ← sum_excessAt_eq_arrowSum_sub, hsum, sum_excessAt_source, neg_neg]

/-- **Residual cut gap.** For every `A`–`B` cut `S`, the capacity of `S` exceeds the value of an
`A`–`B` flow by its total residual capacity on the residual arrows leaving `S`. -/
theorem arrowSum_sub_val [DecidableEq V] (f : SetFlow cap A B) {S : Finset V}
    (hS : TerminalCut.IsAdmissible A B S) :
    arrowSum cap S Sᶜ - f.val = arrowSum (residualCapacity 0 cap f.toFun) S Sᶜ := by
  rw [arrowSum_residualCapacity, arrowSum_sub, arrowSum_sub, f.val_eq_arrowSum_sub hS,
    arrowSum_zero]
  abel

variable [IsOrderedAddMonoid K]

/-- The value of an `A`–`B` flow is nonnegative. -/
theorem val_nonneg (f : SetFlow cap A B) : 0 ≤ f.val :=
  sum_nonneg f.excessAt_nonneg

/-- **Weak duality.** The value of an `A`–`B` flow is at most the capacity of every `A`–`B` cut. -/
theorem val_le_arrowSum [DecidableEq V] (f : SetFlow cap A B) {S : Finset V}
    (hS : TerminalCut.IsAdmissible A B S) : f.val ≤ arrowSum cap S Sᶜ := by
  rw [f.val_eq_arrowSum_sub hS]
  calc arrowSum f.toFun S Sᶜ - arrowSum f.toFun Sᶜ S ≤ arrowSum f.toFun S Sᶜ :=
        sub_le_self _ (by simpa only [arrowSum_zero] using arrowSum_mono f.mem_Icc.1 Sᶜ S)
    _ ≤ arrowSum cap S Sᶜ := arrowSum_mono f.mem_Icc.2 _ _

/-- An `A`–`B` flow attains the capacity of an `A`–`B` cut `S` exactly when every residual arrow
leaving `S` has zero residual capacity. -/
theorem val_eq_arrowSum_iff [DecidableEq V] (f : SetFlow cap A B) {S : Finset V}
    (hS : TerminalCut.IsAdmissible A B S) :
    f.val = arrowSum cap S Sᶜ ↔
      ∀ v ∈ S, ∀ w ∉ S, ∀ e : ResidualHom Q v w, residualCapacity 0 cap f.toFun e = 0 := by
  rw [eq_comm, ← sub_eq_zero, f.arrowSum_sub_val hS,
    arrowSum_eq_zero_iff_of_nonneg (residualCapacity_nonneg f.mem_Icc)]
  simp only [mem_compl]

/-- An `A`–`B` flow whose value is the capacity of an `A`–`B` cut is maximum. -/
theorem isMaximum_of_val_eq_arrowSum [DecidableEq V] (f : SetFlow cap A B) {S : Finset V}
    (hS : TerminalCut.IsAdmissible A B S) (h : f.val = arrowSum cap S Sᶜ) : f.IsMaximum :=
  isMaximum_iff.2 fun g ↦ h ▸ g.val_le_arrowSum hS

open Classical in
/-- If no vertex of `B` is positively reachable from a vertex of `A` for the residual capacities
of an `A`–`B` flow, then its value is the capacity of the set of vertices positively reachable
from `A`, which is an `A`–`B` cut. -/
theorem val_eq_arrowSum_of_not_positiveReachable [DecidableEq V] (f : SetFlow cap A B)
    (h : ∀ a ∈ A, ∀ b ∈ B, ¬PositiveReachable (residualCapacity 0 cap f.toFun) a b) :
    f.val = arrowSum cap
      (univ.filter fun v ↦ ∃ a ∈ A, PositiveReachable (residualCapacity 0 cap f.toFun) a v)
      (univ.filter fun v ↦ ∃ a ∈ A, PositiveReachable (residualCapacity 0 cap f.toFun) a v)ᶜ := by
  rw [f.val_eq_arrowSum_iff (TerminalCut.isAdmissible_filter_positiveReachable h)]
  intro v hv w hw e
  simp only [mem_filter, mem_univ, true_and, not_exists, not_and] at hv hw
  obtain ⟨a, ha, hav⟩ := hv
  refine ((residualCapacity_nonneg f.mem_Icc v w e).eq_or_lt.resolve_right fun he ↦ ?_).symm
  exact hw a ha (hav.tail e he)

end PartialOrder

section LinearOrder

variable [LinearOrder K] [IsOrderedAddMonoid K] {cap : Assignment Q K} {A B : Finset V}

/-- **Augmentation.** If a vertex of `B` is positively reachable from a vertex of `A` for the
residual capacities of an `A`–`B` flow, for disjoint `A` and `B`, then augmenting along an
augmenting path by its bottleneck gives an `A`–`B` flow of larger value. -/
theorem exists_val_lt_of_positiveReachable (hAB : Disjoint A B) (f : SetFlow cap A B) {a b : V}
    (ha : a ∈ A) (hb : b ∈ B) (h : PositiveReachable (residualCapacity 0 cap f.toFun) a b) :
    ∃ g : SetFlow cap A B, f.val < g.val := by
  classical
  have hab : a ≠ b := fun hab ↦ disjoint_left.1 hAB ha (hab ▸ hb)
  obtain ⟨p, hp, hpos⟩ := positiveReachable_iff_exists_isPath.1 h
  have hne : p.arrows ≠ [] := p.arrows_ne_nil hab
  set q := p.bottleneck (residualCapacity 0 cap f.toFun) hne
  have hq : 0 < q := ArrowWalk.lt_bottleneck_iff.2 hpos
  -- the augmented assignment raises the excess at `b` by `q`, lowers it at `a` by `q`, and keeps
  -- every other excess
  have hexcess (v : V) : excessAt (residualUpdate f.toFun (walkAssignment p q)) v =
      excessAt f.toFun v + ((if v = b then q else 0) - if v = a then q else 0) := by
    rw [excessAt_residualUpdate, excessAt_walkAssignment]
  let g : SetFlow cap A B :=
    { toFun := residualUpdate f.toFun (walkAssignment p q)
      mem_Icc := residualUpdate_walkAssignment_mem_Icc f.mem_Icc hp.nodup_arrows hq.le
        fun _ ha ↦ ArrowWalk.bottleneck_le ha
      conserve v hvA hvB := by
        simp [hexcess, (ne_of_mem_of_not_mem hb hvB).symm, (ne_of_mem_of_not_mem ha hvA).symm,
          f.conserve v hvA hvB]
      excessAt_nonpos a' ha' := by
        have hf := f.excessAt_nonpos a' ha'
        simp only [hexcess, ne_of_mem_of_not_mem ha' (disjoint_right.1 hAB hb), ↓reduceIte,
          zero_sub]
        split_ifs
        · exact add_nonpos hf (neg_nonpos.2 hq.le)
        · simpa using hf
      excessAt_nonneg b' hb' := by
        have hf := f.excessAt_nonneg b' hb'
        simp only [hexcess, ne_of_mem_of_not_mem hb' (disjoint_left.1 hAB ha), ↓reduceIte,
          sub_zero]
        split_ifs
        · exact add_nonneg hf hq.le
        · simpa using hf }
  refine ⟨g, ?_⟩
  have hval : g.val = f.val + q := by
    simp [val_def, g, hexcess, sum_add_distrib, hb, disjoint_left.1 hAB ha]
  rw [hval]
  exact lt_add_of_pos_right _ hq

/-- A maximum `A`–`B` flow for disjoint `A` and `B` has no augmenting walk. -/
theorem IsMaximum.not_positiveReachable (hAB : Disjoint A B) {f : SetFlow cap A B}
    (hf : f.IsMaximum) {a b : V} (ha : a ∈ A) (hb : b ∈ B) :
    ¬PositiveReachable (residualCapacity 0 cap f.toFun) a b := fun h ↦
  have ⟨g, hg⟩ := exists_val_lt_of_positiveReachable hAB f ha hb h
  (hg.trans_le (isMaximum_iff.1 hf g)).false

/-- **Augmenting-path optimality criterion for `A`–`B` flows.** For an `A`–`B` flow `f` between
disjoint vertex sets, the following are equivalent: `f` is maximum; there is no augmenting walk
for `f` from a vertex of `A` to a vertex of `B`; and the value of `f` equals the capacity of some
`A`–`B` cut. -/
theorem tfae_isMaximum [DecidableEq V] (hAB : Disjoint A B) (f : SetFlow cap A B) :
    List.TFAE [f.IsMaximum,
      ∀ a ∈ A, ∀ b ∈ B, ¬PositiveReachable (residualCapacity 0 cap f.toFun) a b,
      ∃ S : Finset V, TerminalCut.IsAdmissible A B S ∧ f.val = arrowSum cap S Sᶜ] := by
  tfae_have 1 → 2 := fun hf a ha b hb ↦ hf.not_positiveReachable hAB ha hb
  tfae_have 2 → 3 := fun h ↦ by
    classical
    exact ⟨_, TerminalCut.isAdmissible_filter_positiveReachable h,
      f.val_eq_arrowSum_of_not_positiveReachable h⟩
  tfae_have 3 → 1 := fun ⟨S, hS, h⟩ ↦ f.isMaximum_of_val_eq_arrowSum hS h
  tfae_finish

/-- A maximum `A`–`B` flow between disjoint vertex sets saturates some `A`–`B` cut. -/
theorem IsMaximum.exists_val_eq_arrowSum [DecidableEq V] (hAB : Disjoint A B)
    {f : SetFlow cap A B} (hf : f.IsMaximum) :
    ∃ S : Finset V, TerminalCut.IsAdmissible A B S ∧ f.val = arrowSum cap S Sᶜ :=
  ((f.tfae_isMaximum hAB).out 1 3).1 hf

end LinearOrder

end SetFlow

variable [DecidableEq V]

section AuxFlow

variable [PartialOrder K] {cap : Assignment Q K} {A B : Finset V}

namespace SetFlow

/-- The excess at an original vertex of the restriction of an ordinary flow of the auxiliary
network is the value sent to the fresh sink minus the value arriving from the fresh source. -/
private theorem excessAt_auxTerminalRestrict
    (g : Flow (setFlowCapacity cap A B) (inr false) (inr true)) (v : V) :
    excessAt (auxTerminalRestrict g.toFun) v =
      ∑ e : AuxTerminalHom Q A B (inl v) (inr true), g.toFun e -
        ∑ e : AuxTerminalHom Q A B (inr false) (inl v), g.toFun e := by
  have h := g.conserve (inl v) inl_ne_inr inl_ne_inr
  rw [AuxTerminalHom.excessAt_inl] at h
  rw [← sub_eq_zero, ← h]
  abel

/-- The assignment of the auxiliary network corresponding to an `A`–`B` flow is conserved at every
original vertex. -/
theorem excessAt_auxTerminalCapacity_inl (f : SetFlow cap A B) (v : V) :
    excessAt (auxTerminalCapacity (A := A) (B := B) f.toFun (fun a ↦ -excessAt f.toFun a)
      fun b ↦ excessAt f.toFun b) (inl v) = 0 := by
  rw [AuxTerminalHom.excessAt_inl, auxTerminalRestrict_auxTerminalCapacity,
    sum_auxTerminalCapacity_source, sum_auxTerminalCapacity_sink]
  by_cases hA : v ∈ A <;> by_cases hB : v ∈ B
  · simp [hA, hB, f.excessAt_eq_zero_of_mem_of_mem hA hB]
  · simp [hA, hB]
  · simp [hA, hB]
  · simp [hA, hB, f.conserve v hA hB]

variable [IsOrderedAddMonoid K]

omit [DecidableEq V] in
/-- The assignment of the auxiliary network corresponding to an `A`–`B` flow lies below the
auxiliary capacities `setFlowCapacity cap A B`. -/
theorem auxTerminalCapacity_le_setFlowCapacity (f : SetFlow cap A B) :
    auxTerminalCapacity f.toFun (fun a ↦ -excessAt f.toFun a) (fun b ↦ excessAt f.toFun b) ≤
      setFlowCapacity cap A B :=
  AuxTerminalHom.forall_iff.2 ⟨fun _ _ e ↦ by simpa using f.le_cap e,
    fun a _ ↦ by simpa using neg_excessAt_le_of_mem_Icc f.mem_Icc a,
    fun b _ ↦ by simpa using excessAt_le_of_mem_Icc f.mem_Icc b⟩

/-- The ordinary flow from the fresh source to the fresh sink of the auxiliary network
corresponding to an `A`–`B` flow. It keeps the values on the original arrows, and carries minus the
excess at `a` on the arrow from the fresh source to `a ∈ A` and the excess at `b` on the arrow from
`b ∈ B` to the fresh sink. -/
def toAuxFlow (f : SetFlow cap A B) : Flow (setFlowCapacity cap A B) (inr false) (inr true) where
  toFun := auxTerminalCapacity f.toFun (fun a ↦ -excessAt f.toFun a) fun b ↦ excessAt f.toFun b
  mem_Icc := ⟨auxTerminalCapacity_nonneg f.mem_Icc.1
    (fun a ha ↦ neg_nonneg.2 (f.excessAt_nonpos a ha)) f.excessAt_nonneg,
    f.auxTerminalCapacity_le_setFlowCapacity⟩
  conserve
    | inl v, _, _ => f.excessAt_auxTerminalCapacity_inl v
    | inr false, hσ, _ => (hσ rfl).elim
    | inr true, _, hτ => (hτ rfl).elim
  excessAt_sink_nonneg := by
    rw [AuxTerminalHom.excessAt_inr_true]
    simp only [sum_auxTerminalCapacity_sink, sum_ite_mem, univ_inter]
    exact f.val_nonneg

@[simp]
theorem toAuxFlow_toFun (f : SetFlow cap A B) :
    f.toAuxFlow.toFun =
      auxTerminalCapacity f.toFun (fun a ↦ -excessAt f.toFun a) fun b ↦ excessAt f.toFun b :=
  (rfl)

end SetFlow

variable [IsOrderedAddMonoid K]

/-- The `A`–`B` flow corresponding to an ordinary flow from the fresh source to the fresh sink of
the auxiliary network, for disjoint `A` and `B`: its restriction to the original arrows. -/
def Flow.toSetFlow (g : Flow (setFlowCapacity cap A B) (inr false) (inr true))
    (hAB : Disjoint A B) : SetFlow cap A B where
  toFun := auxTerminalRestrict g.toFun
  mem_Icc := ⟨fun _ _ e ↦ by simpa using g.nonneg (AuxTerminalHom.original e),
    fun _ _ e ↦ by simpa using g.le_upper (AuxTerminalHom.original e)⟩
  conserve v hA hB := by
    rw [SetFlow.excessAt_auxTerminalRestrict, AuxTerminalHom.sum_sink_of_notMem hB,
      AuxTerminalHom.sum_source_of_notMem hA, sub_zero]
  excessAt_nonpos a ha := by
    rw [SetFlow.excessAt_auxTerminalRestrict,
      AuxTerminalHom.sum_sink_of_notMem (disjoint_left.1 hAB ha), zero_sub, neg_nonpos]
    exact sum_nonneg fun e _ ↦ g.nonneg e
  excessAt_nonneg b hb := by
    rw [SetFlow.excessAt_auxTerminalRestrict,
      AuxTerminalHom.sum_source_of_notMem (disjoint_right.1 hAB hb), sub_zero]
    exact sum_nonneg fun e _ ↦ g.nonneg e

@[simp]
theorem Flow.toSetFlow_toFun (g : Flow (setFlowCapacity cap A B) (inr false) (inr true))
    (hAB : Disjoint A B) : (g.toSetFlow hAB).toFun = auxTerminalRestrict g.toFun :=
  (rfl)

namespace SetFlow

/-- **Reduction to single terminals.** For disjoint `A` and `B`, the `A`–`B` flows correspond to
the ordinary flows from the fresh source to the fresh sink for the auxiliary capacities
`setFlowCapacity cap A B`, by `SetFlow.toAuxFlow` and `Flow.toSetFlow`. An `A`–`B` flow keeps its
values on the original arrows, and carries minus its excess at `a` on the arrow from the fresh
source to `a ∈ A` and its excess at `b` on the arrow from `b ∈ B` to the fresh sink. -/
def auxFlowEquiv (hAB : Disjoint A B) :
    SetFlow cap A B ≃ Flow (setFlowCapacity cap A B) (inr false) (inr true) where
  toFun := toAuxFlow
  invFun g := g.toSetFlow hAB
  left_inv f := SetFlow.ext (auxTerminalRestrict_auxTerminalCapacity _ _ _)
  right_inv g := by
    refine Flow.ext (funext₃ (AuxTerminalHom.forall_iff.2
      ⟨fun _ _ e ↦ ?_, fun a ha ↦ ?_, fun b hb ↦ ?_⟩)) <;>
      simp only [toAuxFlow_toFun, Flow.toSetFlow_toFun]
    · rw [auxTerminalCapacity_original, auxTerminalRestrict_apply]
    · rw [auxTerminalCapacity_source, excessAt_auxTerminalRestrict,
        AuxTerminalHom.sum_sink_of_notMem (disjoint_left.1 hAB ha), AuxTerminalHom.sum_source ha,
        zero_sub, neg_neg]
    · rw [auxTerminalCapacity_sink, excessAt_auxTerminalRestrict,
        AuxTerminalHom.sum_source_of_notMem (disjoint_right.1 hAB hb), AuxTerminalHom.sum_sink hb,
        sub_zero]

@[simp]
theorem auxFlowEquiv_apply (hAB : Disjoint A B) (f : SetFlow cap A B) :
    auxFlowEquiv hAB f = f.toAuxFlow :=
  (rfl)

@[simp]
theorem auxFlowEquiv_symm_apply (hAB : Disjoint A B)
    (g : Flow (setFlowCapacity cap A B) (inr false) (inr true)) :
    (auxFlowEquiv hAB).symm g = g.toSetFlow hAB :=
  (rfl)

@[simp]
theorem toAuxFlow_toSetFlow (hAB : Disjoint A B) (f : SetFlow cap A B) :
    f.toAuxFlow.toSetFlow hAB = f :=
  (auxFlowEquiv hAB).symm_apply_apply f

/-- The ordinary flow of the auxiliary network corresponding to an `A`–`B` flow has the same
value. -/
@[simp]
theorem val_toAuxFlow (f : SetFlow cap A B) : f.toAuxFlow.val = f.val := by
  rw [BoundedFlow.val_def, AuxTerminalHom.excessAt_inr_true, toAuxFlow_toFun]
  simp only [sum_auxTerminalCapacity_sink, sum_ite_mem, univ_inter, val_def]

end SetFlow

@[simp]
theorem Flow.toSetFlow_toAuxFlow (hAB : Disjoint A B)
    (g : Flow (setFlowCapacity cap A B) (inr false) (inr true)) :
    (g.toSetFlow hAB).toAuxFlow = g :=
  (SetFlow.auxFlowEquiv hAB).apply_symm_apply g

/-- The `A`–`B` flow corresponding to an ordinary flow of the auxiliary network has the same
value. -/
@[simp]
theorem Flow.val_toSetFlow (hAB : Disjoint A B)
    (g : Flow (setFlowCapacity cap A B) (inr false) (inr true)) :
    (g.toSetFlow hAB).val = g.val := by
  rw [← SetFlow.val_toAuxFlow, g.toSetFlow_toAuxFlow hAB]

/-- An `A`–`B` flow is maximum exactly when the corresponding flow of the auxiliary network is. -/
@[simp]
theorem SetFlow.isMaximum_toAuxFlow (hAB : Disjoint A B) {f : SetFlow cap A B} :
    f.toAuxFlow.IsMaximum ↔ f.IsMaximum := by
  rw [Flow.isMaximum_iff, isMaximum_iff, (auxFlowEquiv hAB).forall_congr_left]
  simp

end AuxFlow

namespace SetFlow

variable [LinearOrder K] [IsOrderedAddMonoid K] {cap : Assignment Q K} {A B : Finset V}

omit [DecidableEq V] in
/-- **Integrality of maximum `A`–`B` flows.** For disjoint `A` and `B` and nonnegative capacities in
an additive subgroup `H`, some maximum `A`–`B` flow takes values in `H`. -/
theorem exists_isMaximum_mem (hAB : Disjoint A B) (hcap : 0 ≤ cap) (H : AddSubgroup K)
    (hcapH : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ H) :
    ∃ f : SetFlow cap A B, f.IsMaximum ∧ ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ H := by
  classical
  obtain ⟨g, hg, hgH⟩ := Flow.exists_isMaximum_mem (s := inr false) (t := inr true)
    (setFlowCapacity_nonneg hcap) H (setFlowCapacity_mem hcapH)
  refine ⟨g.toSetFlow hAB, ?_, fun _ _ e ↦ by simpa using hgH (AuxTerminalHom.original e)⟩
  rwa [← isMaximum_toAuxFlow hAB, Flow.toSetFlow_toAuxFlow]

omit [DecidableEq V] in
/-- For disjoint `A` and `B` and nonnegative capacities, a maximum `A`–`B` flow exists. -/
theorem exists_isMaximum (hAB : Disjoint A B) (hcap : 0 ≤ cap) :
    ∃ f : SetFlow cap A B, f.IsMaximum :=
  let ⟨f, hf, _⟩ := exists_isMaximum_mem hAB hcap ⊤ fun _ _ _ ↦ AddSubgroup.mem_top _
  ⟨f, hf⟩

/-- **Max-flow/min-cut theorem between vertex sets.** For disjoint `A` and `B` and nonnegative
capacities, some `A`–`B` flow has value equal to the capacity of some `A`–`B` cut. By weak duality
(`TauCeti.SetFlow.val_le_arrowSum`) this flow is maximum and this cut is minimum. -/
theorem exists_val_eq_arrowSum (hAB : Disjoint A B) (hcap : 0 ≤ cap) :
    ∃ f : SetFlow cap A B, ∃ S : Finset V,
      TerminalCut.IsAdmissible A B S ∧ f.val = arrowSum cap S Sᶜ :=
  let ⟨f, hf⟩ := exists_isMaximum hAB hcap
  ⟨f, hf.exists_val_eq_arrowSum hAB⟩

end SetFlow

/-!
## Example

On the vertices `0, 1, 2, 3`, take unit capacities on the arrows `0 → 2`, `0 → 3` and `1 → 3`,
and capacity zero on one arrow for every other ordered pair, loops included. For the supply
vertices `A = {0, 1}` and the demand vertices `B = {2, 3}`, the assignment saturating every arrow is
an `A`–`B` flow with excesses `-2, -1, 1, 2`, so of value `3`. This is the capacity of the cut `A`,
so the flow is maximum. The corresponding flow of the auxiliary network also has value `3`, and
carries `2` on the arrow from the fresh source to `0`.
-/

private abbrev ExHom (_ _ : Fin 4) : Type := Unit

private def exCap : Assignment ExHom ℤ := fun v w _ ↦
  ![![0, 0, 1, 1], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]] v w

private def exSetFlow : SetFlow exCap {0, 1} {2, 3} where
  toFun := exCap
  mem_Icc := ⟨fun v w _ ↦ by revert v w; decide, le_rfl⟩
  conserve v h₀ h₁ := by
    fin_cases v <;> simp_all
  excessAt_nonpos a ha := by
    fin_cases a <;> simp_all [excessAt_def, Fin.sum_univ_four, exCap]
  excessAt_nonneg b hb := by
    fin_cases b <;> simp_all [excessAt_def, Fin.sum_univ_four, exCap]

private theorem val_exSetFlow : exSetFlow.val = 3 := by
  simp [SetFlow.val_def, excessAt_def, Fin.sum_univ_four, exSetFlow, exCap]

-- The flow saturates the cut `{0, 1}`, of capacity `3`, so it is maximum.
example : exSetFlow.IsMaximum :=
  exSetFlow.isMaximum_of_val_eq_arrowSum (S := {0, 1})
    (TerminalCut.isAdmissible_iff.2 (by decide)) (by
    rw [val_exSetFlow]
    simp [arrowSum_eq_sum_ite, Fin.sum_univ_four, exCap])

-- The flow of the auxiliary network has the same value, and carries minus the excess at `0` on
-- the arrow from the fresh source to `0`.
example : exSetFlow.toAuxFlow.val = 3 := by
  rw [SetFlow.val_toAuxFlow, val_exSetFlow]

example : exSetFlow.toAuxFlow.toFun
    (AuxTerminalHom.source (B := {2, 3}) (a := 0) (by decide)) = 2 := by
  simp [excessAt_def, Fin.sum_univ_four, exSetFlow, exCap]

end TauCeti
