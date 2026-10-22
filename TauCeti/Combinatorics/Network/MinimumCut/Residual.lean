/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.AugmentingPath
public import TauCeti.Combinatorics.Network.MinimumCut.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import TauCeti.Combinatorics.Network.CutSubmodular

/-!
# Minimum cuts from a maximum assignment

Let `f` be a maximum bounded `s`–`t` assignment for lower and upper bounds `lo` and `hi`, between
distinct terminals. Weak duality and the augmenting-path optimality criterion show that the
minimum of the cut bound `cutBound lo hi` over the vertex sets containing `s` but not `t` is the
value of `f`. The residual cut gap identity `TauCeti.BoundedFlow.cutBound_sub_val` then identifies
the minimum cuts: they are exactly the vertex sets containing `s` but not `t` that no residual
arrow of positive capacity leaves.

Consequently every minimum cut contains all vertices that are positively reachable from the
source for the residual capacities of `f`, and no vertex from which the sink is positively
reachable. Both bounds are attained: the vertices reachable from the source form the smallest
minimum cut, and the vertices from which the sink is not reachable form the largest. So a vertex
lies on the source side of every minimum cut exactly when it is reachable from the source, and on
the source side of none exactly when the sink is reachable from it; the minimum cut is unique
exactly when every vertex is of one of these two kinds. Since the minimum cuts do not mention `f`,
both reachability relations are the same for every maximum assignment.

The bounds may be negative and the value of `f` may have either sign. The ordinary-flow
statements, for zero lower bounds and the cut capacity of the arrows leaving a set, follow by
specialization.

## Main results

* `TauCeti.BoundedFlow.IsMaximum.isMinimum_cutBound_iff`: the minimum cuts are the
  terminal-separating sets that no residual arrow of positive capacity leaves.
* `TauCeti.BoundedFlow.IsMaximum.isMinimum_cutBound_iff_forall_positiveReachable`: equivalently,
  the terminal-separating sets closed under residual positive reachability.
* `TauCeti.BoundedFlow.IsMaximum.isLeast_filter_positiveReachable` and
  `TauCeti.BoundedFlow.IsMaximum.isGreatest_compl_filter_positiveReachable`: the smallest and
  largest minimum cuts, by residual reachability from the source and to the sink.
* `TauCeti.BoundedFlow.IsMaximum.mem_smallest_iff` and
  `TauCeti.BoundedFlow.IsMaximum.mem_largest_iff`: the same, for the extremal cuts
  `TauCeti.TerminalCut.smallest` and `TauCeti.TerminalCut.largest` of the minimum-cut lattice.
* `TauCeti.BoundedFlow.IsMaximum.existsUnique_isMinimum_iff`: the minimum cut is unique exactly
  when every vertex is reachable from the source or reaches the sink.
* `TauCeti.BoundedFlow.IsMaximum.positiveReachable_source_iff` and
  `TauCeti.BoundedFlow.IsMaximum.positiveReachable_sink_iff`: residual reachability from the
  source and to the sink does not depend on the chosen maximum assignment.
* `TauCeti.Flow.IsMaximum.isMinimum_iff`, `TauCeti.Flow.IsMaximum.mem_smallest_iff`,
  `TauCeti.Flow.IsMaximum.mem_largest_iff` and
  `TauCeti.Flow.IsMaximum.existsUnique_isMinimum_iff`: the ordinary-flow specializations.

## References

* L. R. Ford, D. R. Fulkerson, *Flows in Networks*, Princeton University Press, 1962.
* J.-C. Picard, M. Queyranne, *On the structure of all minimum cuts in a network and
  applications*, Math. Programming Stud. 13 (1980), 8–16.
-/

public section

namespace TauCeti

open Finset TerminalCut

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}
variable [Fintype V] [DecidableEq V] [∀ v w, Fintype (Q v w)]
variable [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]

namespace BoundedFlow.IsMaximum

variable {lo hi : Assignment Q K} {s t : V} {f : BoundedFlow lo hi s t}

/-- For a maximum bounded `s`–`t` assignment `f` between distinct terminals, the minimum cuts for
the cut bound are the vertex sets containing `s` but not `t` whose cut bound is the value of `f`.
-/
theorem isMinimum_cutBound_iff_val_eq (hst : s ≠ t) (hf : f.IsMaximum) {S : Finset V} :
    IsMinimum (cutBound lo hi) {s} {t} S ↔ s ∈ S ∧ t ∉ S ∧ f.val = cutBound lo hi S := by
  rw [isMinimum_singleton_iff]
  refine ⟨fun ⟨hs, ht, hS⟩ ↦ ⟨hs, ht, ?_⟩, fun ⟨hs, ht, hS⟩ ↦
    ⟨hs, ht, fun T hsT htT ↦ hS.symm.le.trans (f.val_le_cutBound hsT htT)⟩⟩
  obtain ⟨T, hsT, htT, hT⟩ := hf.exists_val_eq_cutBound hst
  exact le_antisymm (f.val_le_cutBound hs ht) ((hS T hsT htT).trans hT.ge)

/-- **Residual characterization of minimum cuts.** For a maximum bounded `s`–`t` assignment `f`
between distinct terminals, the minimum cuts for the cut bound are exactly the vertex sets
containing `s` but not `t` that no residual arrow of positive capacity leaves. -/
theorem isMinimum_cutBound_iff (hst : s ≠ t) (hf : f.IsMaximum) {S : Finset V} :
    IsMinimum (cutBound lo hi) {s} {t} S ↔ s ∈ S ∧ t ∉ S ∧
      ∀ v ∈ S, ∀ w ∉ S, ∀ e : ResidualHom Q v w, residualCapacity lo hi f.toFun e = 0 := by
  rw [hf.isMinimum_cutBound_iff_val_eq hst]
  exact and_congr_right fun hs ↦ and_congr_right fun ht ↦ f.val_eq_cutBound_iff hs ht

/-- A minimum cut is closed under positive reachability for the residual capacities of a maximum
bounded `s`–`t` assignment. -/
theorem mem_of_positiveReachable (hst : s ≠ t) (hf : f.IsMaximum) {S : Finset V}
    (hS : IsMinimum (cutBound lo hi) {s} {t} S) {v w : V}
    (h : PositiveReachable (residualCapacity lo hi f.toFun) v w) (hv : v ∈ S) : w ∈ S := by
  have hS' := ((hf.isMinimum_cutBound_iff hst).1 hS).2.2
  refine h.mem_of_mem (C := (S : Set V)) hv fun x y e hx he ↦ ?_
  by_contra hy
  exact he.ne' (hS' x hx y hy e)

/-- For a maximum bounded `s`–`t` assignment `f` between distinct terminals, the minimum cuts for
the cut bound are exactly the vertex sets containing `s` but not `t` that are closed under positive
reachability for the residual capacities of `f`. -/
theorem isMinimum_cutBound_iff_forall_positiveReachable (hst : s ≠ t) (hf : f.IsMaximum)
    {S : Finset V} :
    IsMinimum (cutBound lo hi) {s} {t} S ↔ s ∈ S ∧ t ∉ S ∧
      ∀ v ∈ S, ∀ w, PositiveReachable (residualCapacity lo hi f.toFun) v w → w ∈ S := by
  refine ⟨fun hS ↦ ⟨(isMinimum_singleton_iff.1 hS).1, (isMinimum_singleton_iff.1 hS).2.1,
    fun v hv w h ↦ hf.mem_of_positiveReachable hst hS h hv⟩, fun ⟨hs, ht, hS⟩ ↦
    (hf.isMinimum_cutBound_iff hst).2 ⟨hs, ht, fun v hv w hw e ↦ ?_⟩⟩
  refine ((residualCapacity_nonneg f.mem_Icc v w e).eq_or_lt.resolve_right fun he ↦ hw ?_).symm
  exact hS v hv w (.single e he)

/-- The vertices positively reachable from the source for the residual capacities of a maximum
bounded `s`–`t` assignment form the smallest minimum cut. -/
theorem isLeast_filter_positiveReachable (hst : s ≠ t) (hf : f.IsMaximum)
    [DecidablePred (PositiveReachable (residualCapacity lo hi f.toFun) s)] :
    IsLeast {S | IsMinimum (cutBound lo hi) {s} {t} S}
      (univ.filter (PositiveReachable (residualCapacity lo hi f.toFun) s)) := by
  refine ⟨(hf.isMinimum_cutBound_iff_val_eq hst).2 ⟨by simp,
    by simpa using hf.not_positiveReachable hst, ?_⟩, fun S hS v hv ↦
    hf.mem_of_positiveReachable hst hS (by simpa using hv) (isMinimum_singleton_iff.1 hS).1⟩
  convert f.val_eq_cutBound_of_not_positiveReachable (hf.not_positiveReachable hst)

/-- The vertices from which the sink is not positively reachable for the residual capacities of a
maximum bounded `s`–`t` assignment form the largest minimum cut. -/
theorem isGreatest_compl_filter_positiveReachable (hst : s ≠ t) (hf : f.IsMaximum)
    [DecidablePred (PositiveReachable (residualCapacity lo hi f.toFun) · t)] :
    IsGreatest {S | IsMinimum (cutBound lo hi) {s} {t} S}
      (univ.filter (PositiveReachable (residualCapacity lo hi f.toFun) · t))ᶜ := by
  refine ⟨(hf.isMinimum_cutBound_iff hst).2 ⟨by simpa using hf.not_positiveReachable hst, by simp,
    fun v hv w hw e ↦ ?_⟩, fun S hS v hv ↦ ?_⟩
  · simp only [mem_compl, mem_filter, mem_univ, true_and, not_not] at hv hw
    refine ((residualCapacity_nonneg f.mem_Icc v w e).eq_or_lt.resolve_right fun he ↦ hv ?_).symm
    exact (PositiveReachable.single e he).trans hw
  · simp only [mem_compl, mem_filter, mem_univ, true_and]
    exact fun h ↦ (isMinimum_singleton_iff.1 hS).2.1 (hf.mem_of_positiveReachable hst hS h hv)

/-- A vertex lies on the source side of every minimum cut exactly when it is positively reachable
from the source for the residual capacities of a maximum bounded `s`–`t` assignment. -/
theorem forall_isMinimum_mem_iff (hst : s ≠ t) (hf : f.IsMaximum) {v : V} :
    (∀ S, IsMinimum (cutBound lo hi) {s} {t} S → v ∈ S) ↔
      PositiveReachable (residualCapacity lo hi f.toFun) s v := by
  classical
  refine ⟨fun h ↦ by simpa using h _ (hf.isLeast_filter_positiveReachable hst).1, fun h S hS ↦
    hf.mem_of_positiveReachable hst hS h (isMinimum_singleton_iff.1 hS).1⟩

/-- A vertex lies on the source side of no minimum cut exactly when the sink is positively
reachable from it for the residual capacities of a maximum bounded `s`–`t` assignment. -/
theorem forall_isMinimum_notMem_iff (hst : s ≠ t) (hf : f.IsMaximum) {v : V} :
    (∀ S, IsMinimum (cutBound lo hi) {s} {t} S → v ∉ S) ↔
      PositiveReachable (residualCapacity lo hi f.toFun) v t := by
  classical
  refine ⟨fun h ↦ by simpa using h _ (hf.isGreatest_compl_filter_positiveReachable hst).1,
    fun h S hS hv ↦ (isMinimum_singleton_iff.1 hS).2.1 (hf.mem_of_positiveReachable hst hS h hv)⟩

/-- A vertex belongs to the smallest minimum cut exactly when it is positively reachable from the
source for the residual capacities of a maximum bounded `s`–`t` assignment. -/
theorem mem_smallest_iff (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular (cutBound lo hi)) {v : V} :
    v ∈ smallest hsub (disjoint_singleton.2 hst) ↔
      PositiveReachable (residualCapacity lo hi f.toFun) s v := by
  rw [TerminalCut.mem_smallest_iff, hf.forall_isMinimum_mem_iff hst]

/-- A vertex belongs to the largest minimum cut exactly when the sink is not positively reachable
from it for the residual capacities of a maximum bounded `s`–`t` assignment. -/
theorem mem_largest_iff (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular (cutBound lo hi)) {v : V} :
    v ∈ largest hsub (disjoint_singleton.2 hst) ↔
      ¬PositiveReachable (residualCapacity lo hi f.toFun) v t := by
  rw [TerminalCut.mem_largest_iff, ← hf.forall_isMinimum_notMem_iff hst]
  simp only [not_forall, not_not, exists_prop]

/-- The minimum cut is unique exactly when every vertex is positively reachable from the source or
reaches the sink positively, for the residual capacities of a maximum bounded `s`–`t` assignment.
-/
theorem existsUnique_isMinimum_iff (hst : s ≠ t) (hf : f.IsMaximum) :
    (∃! S, IsMinimum (cutBound lo hi) {s} {t} S) ↔
      ∀ v, PositiveReachable (residualCapacity lo hi f.toFun) s v ∨
        PositiveReachable (residualCapacity lo hi f.toFun) v t := by
  classical
  have hR := hf.isLeast_filter_positiveReachable hst
  have hT := hf.isGreatest_compl_filter_positiveReachable hst
  constructor
  · rintro ⟨S, -, hS⟩ v
    have hRT := (hS _ hR.1).trans (hS _ hT.1).symm
    by_contra! hv
    have hvT : v ∈ (univ.filter (PositiveReachable (residualCapacity lo hi f.toFun) · t))ᶜ := by
      simpa using hv.2
    rw [← hRT] at hvT
    exact hv.1 (by simpa using hvT)
  · intro h
    refine ⟨_, hR.1, fun S hS ↦ le_antisymm (fun v hv ↦ ?_) (hR.2 hS)⟩
    have hv' := hT.2 hS hv
    simp only [mem_compl, mem_filter, mem_univ, true_and] at hv' ⊢
    exact (h v).resolve_right hv'

omit [DecidableEq V] in
/-- Positive reachability from the source for the residual capacities is the same for all
maximum bounded `s`–`t` assignments. -/
theorem positiveReachable_source_iff (hst : s ≠ t) (hf : f.IsMaximum)
    {g : BoundedFlow lo hi s t} (hg : g.IsMaximum) {v : V} :
    PositiveReachable (residualCapacity lo hi f.toFun) s v ↔
      PositiveReachable (residualCapacity lo hi g.toFun) s v := by
  classical
  rw [← hf.forall_isMinimum_mem_iff hst, hg.forall_isMinimum_mem_iff hst]

omit [DecidableEq V] in
/-- Positive reachability of the sink for the residual capacities is the same for all maximum
bounded `s`–`t` assignments. -/
theorem positiveReachable_sink_iff (hst : s ≠ t) (hf : f.IsMaximum)
    {g : BoundedFlow lo hi s t} (hg : g.IsMaximum) {v : V} :
    PositiveReachable (residualCapacity lo hi f.toFun) v t ↔
      PositiveReachable (residualCapacity lo hi g.toFun) v t := by
  classical
  rw [← hf.forall_isMinimum_notMem_iff hst, hg.forall_isMinimum_notMem_iff hst]

end BoundedFlow.IsMaximum

/-! ### Ordinary flows -/

namespace Flow.IsMaximum

variable {cap : Assignment Q K} {s t : V} {f : Flow cap s t}

/-- **Residual characterization of minimum cuts for ordinary flows.** For a maximum ordinary
`s`–`t` flow `f` between distinct terminals, the minimum cuts for the capacity of the arrows
leaving a set are exactly the vertex sets containing `s` but not `t` that no residual arrow of
positive capacity leaves. -/
theorem isMinimum_iff (hst : s ≠ t) (hf : f.IsMaximum) {S : Finset V} :
    IsMinimum (fun S ↦ arrowSum cap S Sᶜ) {s} {t} S ↔ s ∈ S ∧ t ∉ S ∧
      ∀ v ∈ S, ∀ w ∉ S, ∀ e : ResidualHom Q v w, residualCapacity 0 cap f.toFun e = 0 := by
  rw [← funext (cutBound_zero_left cap)]
  exact ((isMaximum_toBoundedFlow f).2 hf).isMinimum_cutBound_iff hst

/-- A vertex lies on the source side of every minimum cut exactly when it is positively reachable
from the source for the residual capacities of a maximum ordinary `s`–`t` flow. -/
theorem forall_isMinimum_mem_iff (hst : s ≠ t) (hf : f.IsMaximum) {v : V} :
    (∀ S, IsMinimum (fun S ↦ arrowSum cap S Sᶜ) {s} {t} S → v ∈ S) ↔
      PositiveReachable (residualCapacity 0 cap f.toFun) s v := by
  rw [← funext (cutBound_zero_left cap)]
  exact ((isMaximum_toBoundedFlow f).2 hf).forall_isMinimum_mem_iff hst

/-- A vertex lies on the source side of no minimum cut exactly when the sink is positively
reachable from it for the residual capacities of a maximum ordinary `s`–`t` flow. -/
theorem forall_isMinimum_notMem_iff (hst : s ≠ t) (hf : f.IsMaximum) {v : V} :
    (∀ S, IsMinimum (fun S ↦ arrowSum cap S Sᶜ) {s} {t} S → v ∉ S) ↔
      PositiveReachable (residualCapacity 0 cap f.toFun) v t := by
  rw [← funext (cutBound_zero_left cap)]
  exact ((isMaximum_toBoundedFlow f).2 hf).forall_isMinimum_notMem_iff hst

/-- A vertex belongs to the smallest minimum cut exactly when it is positively reachable from the
source for the residual capacities of a maximum ordinary `s`–`t` flow. -/
theorem mem_smallest_iff (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ) {v : V} :
    v ∈ smallest hsub (disjoint_singleton.2 hst) ↔
      PositiveReachable (residualCapacity 0 cap f.toFun) s v := by
  rw [TerminalCut.mem_smallest_iff, hf.forall_isMinimum_mem_iff hst]

/-- A vertex belongs to the largest minimum cut exactly when the sink is not positively reachable
from it for the residual capacities of a maximum ordinary `s`–`t` flow. -/
theorem mem_largest_iff (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ) {v : V} :
    v ∈ largest hsub (disjoint_singleton.2 hst) ↔
      ¬PositiveReachable (residualCapacity 0 cap f.toFun) v t := by
  rw [TerminalCut.mem_largest_iff, ← hf.forall_isMinimum_notMem_iff hst]
  simp only [not_forall, not_not, exists_prop]

/-- The minimum cut is unique exactly when every vertex is positively reachable from the source or
reaches the sink positively, for the residual capacities of a maximum ordinary `s`–`t` flow. -/
theorem existsUnique_isMinimum_iff (hst : s ≠ t) (hf : f.IsMaximum) :
    (∃! S, IsMinimum (fun S ↦ arrowSum cap S Sᶜ) {s} {t} S) ↔
      ∀ v, PositiveReachable (residualCapacity 0 cap f.toFun) s v ∨
        PositiveReachable (residualCapacity 0 cap f.toFun) v t := by
  rw [← funext (cutBound_zero_left cap)]
  exact ((isMaximum_toBoundedFlow f).2 hf).existsUnique_isMinimum_iff hst

end Flow.IsMaximum

/-!
## Example

On the vertices `s = 0`, `a = 1`, `b = 2` and `t = 3`, take the arrows `s → a` with bounds
`[-2, 1]`, `s → b` with bounds `[0, 3]`, `a → t` with bounds `[-1, 1]`, `b → t` with bounds
`[0, 1]` and `t → s` with bounds `[-1, 0]`, and one arrow with bounds `[0, 0]` for every other
ordered pair, loops included. The assignment `1, 1, 1, 1, -1` on the five main arrows has value
`3`, which is the cut bound of `{s, b}`, so it is maximum. In its residual network `b` is
positively reachable from `s`, and `t` is positively reachable only from itself. So the smallest
minimum cut is `{s, b}` and the largest is `{s, a, b}`; in particular the minimum cut is not
unique. The cut `{s}` is not minimum: its residual gap is the room `2` left on `s → b`.
-/

private abbrev ExHom (_ _ : Fin 4) : Type := Unit

private def exLower : Assignment ExHom ℤ := fun v w _ ↦
  ![![0, -2, 0, 0], ![0, 0, 0, -1], ![0, 0, 0, 0], ![-1, 0, 0, 0]] v w

private def exUpper : Assignment ExHom ℤ := fun v w _ ↦
  ![![0, 1, 3, 0], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 0]] v w

private def exFlow : BoundedFlow exLower exUpper (0 : Fin 4) 3 where
  toFun v w _ := ![![0, 1, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 1], ![-1, 0, 0, 0]] v w
  mem_Icc := ⟨fun v w _ ↦ by revert v w; decide, fun v w _ ↦ by revert v w; decide⟩
  conserve v h0 h3 := by
    fin_cases v <;> simp_all [excessAt_def, Fin.sum_univ_four]

private theorem exFlow_val : exFlow.val = 3 := by
  simp [BoundedFlow.val_def, excessAt_def, Fin.sum_univ_four, exFlow]

private theorem exFlow_isMaximum : exFlow.IsMaximum :=
  exFlow.isMaximum_of_val_eq_cutBound (S := {0, 2}) (by decide) (by decide) (by
    simp [exFlow_val, cutBound_def, arrowSum_eq_sum_ite, Fin.sum_univ_four, exLower, exUpper])

private theorem isMinimum_ex {S : Finset (Fin 4)} (h0 : 0 ∈ S) (h3 : 3 ∉ S)
    (hS : cutBound exLower exUpper S = 3) : IsMinimum (cutBound exLower exUpper) {0} {3} S :=
  (exFlow_isMaximum.isMinimum_cutBound_iff_val_eq (by decide)).2 ⟨h0, h3, exFlow_val.trans hS.symm⟩

private theorem isMinimum_ex_02 : IsMinimum (cutBound exLower exUpper) {0} {3} {0, 2} :=
  isMinimum_ex (by decide) (by decide) (by
    simp [cutBound_def, arrowSum_eq_sum_ite, Fin.sum_univ_four, exLower, exUpper])

private theorem isMinimum_ex_012 : IsMinimum (cutBound exLower exUpper) {0} {3} {0, 1, 2} :=
  isMinimum_ex (by decide) (by decide) (by
    simp [cutBound_def, arrowSum_eq_sum_ite, Fin.sum_univ_four, exLower, exUpper])

private theorem exLower_le_exUpper : exLower ≤ exUpper :=
  exFlow.mem_Icc.1.trans exFlow.mem_Icc.2

-- The cut `{s}` exceeds the maximum value by the residual capacity `2` of `s → b`.
example : cutBound exLower exUpper {0} - exFlow.val = 2 := by
  rw [exFlow.cutBound_sub_val (by decide) (by decide), arrowSum_eq_sum_ite]
  simp [Fin.sum_univ_four, exLower, exUpper, exFlow]

example : smallest (isSubmodular_cutBound exLower exUpper exLower_le_exUpper)
    (disjoint_singleton.2 (by decide : (0 : Fin 4) ≠ 3)) = {0, 2} := by
  refine le_antisymm ((isLeast_smallest _ _).2 isMinimum_ex_02) fun v hv ↦ ?_
  rw [exFlow_isMaximum.mem_smallest_iff (by decide)]
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact .refl _ _
  · refine .single (Q := ResidualHom ExHom) (Sum.inl ()) ?_
    simp [exUpper, exFlow]

example : largest (isSubmodular_cutBound exLower exUpper exLower_le_exUpper)
    (disjoint_singleton.2 (by decide : (0 : Fin 4) ≠ 3)) = {0, 1, 2} := by
  refine le_antisymm (fun v hv ↦ ?_) ((isGreatest_largest _ _).2 isMinimum_ex_012)
  rw [exFlow_isMaximum.mem_largest_iff (by decide)] at hv
  fin_cases v <;> simp_all

end TauCeti
