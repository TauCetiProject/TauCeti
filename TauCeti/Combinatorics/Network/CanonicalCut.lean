/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Augmentation
public import TauCeti.Combinatorics.Network.MinimumCut

/-!
# Residual characterizations of maximum assignments and minimum cuts

Let `f` be a bounded `s`–`t` assignment for lower and upper bounds `lo` and `hi`, and let `S` be a
vertex set containing `s` but not `t`. The cut bound of `S` exceeds the value of `f` by the total
residual capacity of `f` on the residual arrows leaving `S`:
`cutBound lo hi S - f.val = (hi - f)(δ⁺ S) + (f - lo)(δ⁻ S)`. Every residual capacity is
nonnegative, so the value meets the cut bound exactly when no residual arrow of positive capacity
leaves `S`.

The residual arrows of positive capacity form the arrow family `PosResidualHom lo hi f`, whose
walks are the augmenting walks of `f`. Between distinct terminals `s ≠ t`:

* `f` has the largest value among bounded `s`–`t` assignments exactly when `t` is not reachable
  from `s` along positive residual arrows, and exactly when its value equals some cut bound;
* for such a maximum `f`, the minimum cuts of the cut bound are exactly the vertex sets containing
  `s` but not `t` that no positive residual arrow leaves. The smallest minimum cut consists of the
  vertices reachable from `s`, and the largest of the vertices from which `t` is not reachable.

Since the smallest and largest minimum cuts are defined without reference to `f`, these two
reachability sets are the same for every maximum assignment. Lower bounds may be negative, and so
may the maximum value. The results take a maximum assignment as given rather than constructing
one. Ordinary flows are the case of zero lower bounds and nonnegative value, and their optimality
criteria are stated separately.

## Main results

* `TauCeti.BoundedFlow.cutBound_sub_val`: the cut-gap identity.
* `TauCeti.BoundedFlow.cutBound_eq_val_iff`: the value equals a cut bound exactly when no positive
  residual arrow leaves the cut.
* `TauCeti.BoundedFlow.forall_val_le_iff_not_arrowReachable` and
  `TauCeti.BoundedFlow.forall_val_le_iff_exists_cutBound_eq`: optimality criteria for bounded
  `s`–`t` assignments.
* `TauCeti.BoundedFlow.minimumValue_cutBound` and
  `TauCeti.BoundedFlow.isMinimum_cutBound_iff_isEmpty`: the minimum cut value and the minimum cuts
  for a maximum assignment.
* `TauCeti.BoundedFlow.mem_smallest_iff_arrowReachable` and
  `TauCeti.BoundedFlow.mem_largest_iff_not_arrowReachable`: the smallest and largest minimum cuts
  as residual reachability sets, which therefore do not depend on the maximum assignment.
* `TauCeti.BoundedFlow.existsUnique_isMinimum_iff`: the minimum cut is unique exactly when every
  vertex is reachable from `s` or reaches `t`.
* `TauCeti.Flow.forall_val_le_iff_not_arrowReachable` and
  `TauCeti.Flow.forall_val_le_iff_exists_arrowSum_eq`: optimality criteria for ordinary flows.

## References

* L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*, Canadian J. Math. 8 (1956).
* J.-C. Picard, M. Queyranne, *On the structure of all minimum cuts in a network and
  applications*, Math. Programming Stud. 13 (1980).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

namespace BoundedFlow

/-! ### The cut gap -/

/-- **The cut-gap identity.** For a vertex set `S` containing `s` but not `t`, the cut bound of
`S` exceeds the value of a bounded `s`–`t` assignment `f` by the total residual capacity of `f` on
the residual arrows leaving `S`. -/
theorem cutBound_sub_val [Preorder K] [DecidableEq V] {lo hi : Assignment Q K} {s t : V}
    (f : BoundedFlow lo hi s t) {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    cutBound lo hi S - f.val = arrowSum (residualCapacity lo hi f.toFun) S Sᶜ := by
  rw [f.val_eq_arrowSum_sub hs ht, cutBound_def, arrowSum_residualCapacity, arrowSum_sub,
    arrowSum_sub]
  abel

section PartialOrder

variable [PartialOrder K] [IsOrderedAddMonoid K] {lo hi : Assignment Q K} {s t : V}

/-- The value of a bounded `s`–`t` assignment equals the cut bound of a vertex set containing `s`
but not `t` exactly when no residual arrow of positive capacity leaves the set. -/
theorem cutBound_eq_val_iff [DecidableEq V] (f : BoundedFlow lo hi s t) {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) :
    cutBound lo hi S = f.val ↔ ∀ v ∈ S, ∀ w ∉ S, IsEmpty (PosResidualHom lo hi f.toFun v w) := by
  have hnonneg := residualCapacity_nonneg f.mem_Icc
  rw [← sub_eq_zero, f.cutBound_sub_val hs ht, arrowSum_eq_zero_iff_of_nonneg hnonneg]
  simp only [mem_compl, isEmpty_subtype]
  exact forall₂_congr fun v _ ↦ forall₂_congr fun w _ ↦ forall_congr' fun e ↦
    ⟨fun h h' ↦ h'.ne' h, fun h ↦ ((hnonneg v w e).eq_of_not_lt h).symm⟩

/-- If `t` is not reachable from `s` along the positive residual arrows of a bounded `s`–`t`
assignment, then the vertices reachable from `s` form a cut whose bound equals the value. -/
theorem cutBound_eq_val_of_forall_mem_iff [DecidableEq V] (f : BoundedFlow lo hi s t)
    {S : Finset V} (hS : ∀ v, v ∈ S ↔ ArrowReachable (PosResidualHom lo hi f.toFun) s v)
    (hst : ¬ ArrowReachable (PosResidualHom lo hi f.toFun) s t) : cutBound lo hi S = f.val := by
  refine (f.cutBound_eq_val_iff ((hS s).2 (.refl s)) (mt (hS t).1 hst)).2 fun v hv w hw ↦
    ⟨fun e ↦ hw ((hS w).2 (((hS v).1 hv).trans (.of_arrow e)))⟩

/-- If `t` is not reachable from `s` along the positive residual arrows of a bounded `s`–`t`
assignment, then the vertices from which `t` is not reachable form a cut whose bound equals the
value. -/
theorem cutBound_eq_val_of_forall_mem_iff_not [DecidableEq V] (f : BoundedFlow lo hi s t)
    {S : Finset V} (hS : ∀ v, v ∈ S ↔ ¬ ArrowReachable (PosResidualHom lo hi f.toFun) v t)
    (hst : ¬ ArrowReachable (PosResidualHom lo hi f.toFun) s t) : cutBound lo hi S = f.val := by
  refine (f.cutBound_eq_val_iff ((hS s).2 hst) fun ht ↦ (hS t).1 ht (.refl t)).2 fun v hv w hw ↦
    ⟨fun e ↦ (hS v).1 hv ((ArrowReachable.of_arrow e).trans (not_not.1 (mt (hS w).2 hw)))⟩

end PartialOrder

/-! ### Optimality criteria -/

section LinearOrder

variable [LinearOrder K] [IsOrderedAddMonoid K] {lo hi : Assignment Q K} {s t : V}

/-- **Augmentation.** If `t` is reachable from `s ≠ t` along the positive residual arrows of a
bounded `s`–`t` assignment `f`, then some bounded `s`–`t` assignment has a larger value than `f`. -/
theorem exists_val_lt_of_arrowReachable (hst : s ≠ t) (f : BoundedFlow lo hi s t)
    (h : ArrowReachable (PosResidualHom lo hi f.toFun) s t) :
    ∃ g : BoundedFlow lo hi s t, f.val < g.val := by
  obtain ⟨p, hp⟩ := h.exists_isPath
  set p' := p.map fun _ _ e ↦ e.val
  have hp' : p'.arrows.Nodup := (hp.map _).nodup_arrows
  have hne : p'.arrows ≠ [] := p'.arrows_ne_nil hst
  have hpos : ∀ a ∈ p'.arrows, 0 < residualCapacity lo hi f.toFun a.2.2 := by
    intro a ha
    rw [ArrowWalk.arrows_map, List.mem_map] at ha
    obtain ⟨b, -, rfl⟩ := ha
    exact b.2.2.2
  have hq := (ArrowWalk.lt_bottleneck_iff (hne := hne)).2 hpos
  refine ⟨f.update (walkFlow p' hp' hq.le (residualCapacity_nonneg f.mem_Icc)
    fun _ ha ↦ ArrowWalk.bottleneck_le ha).toBoundedFlow, ?_⟩
  rw [val_update, val_walkFlow hst]
  exact lt_add_of_pos_right _ hq

/-- **Optimality criterion.** A bounded `s`–`t` assignment between distinct terminals has the
largest value exactly when `t` is not reachable from `s` along its positive residual arrows. -/
theorem forall_val_le_iff_not_arrowReachable (hst : s ≠ t) (f : BoundedFlow lo hi s t) :
    (∀ g : BoundedFlow lo hi s t, g.val ≤ f.val) ↔
      ¬ ArrowReachable (PosResidualHom lo hi f.toFun) s t := by
  classical
  refine ⟨fun hf h ↦ ?_, fun h g ↦ ?_⟩
  · obtain ⟨g, hg⟩ := f.exists_val_lt_of_arrowReachable hst h
    exact (hf g).not_gt hg
  · let S := univ.filter (ArrowReachable (PosResidualHom lo hi f.toFun) s)
    have hS : ∀ v, v ∈ S ↔ ArrowReachable (PosResidualHom lo hi f.toFun) s v := by simp [S]
    rw [← f.cutBound_eq_val_of_forall_mem_iff hS h]
    exact g.val_le_cutBound ((hS s).2 (.refl s)) (mt (hS t).1 h)

/-- **Optimality criterion.** A bounded `s`–`t` assignment between distinct terminals has the
largest value exactly when its value equals the cut bound of some vertex set containing `s` but
not `t`. -/
theorem forall_val_le_iff_exists_cutBound_eq [DecidableEq V] (hst : s ≠ t)
    (f : BoundedFlow lo hi s t) :
    (∀ g : BoundedFlow lo hi s t, g.val ≤ f.val) ↔
      ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ cutBound lo hi S = f.val := by
  refine ⟨fun hf ↦ ?_, fun ⟨S, hs, ht, hS⟩ g ↦ hS ▸ g.val_le_cutBound hs ht⟩
  have h := (f.forall_val_le_iff_not_arrowReachable hst).1 hf
  classical
  let S := univ.filter (ArrowReachable (PosResidualHom lo hi f.toFun) s)
  have hS : ∀ v, v ∈ S ↔ ArrowReachable (PosResidualHom lo hi f.toFun) s v := by simp [S]
  exact ⟨S, (hS s).2 (.refl s), mt (hS t).1 h, f.cutBound_eq_val_of_forall_mem_iff hS h⟩

/-! ### Minimum cuts of a maximum assignment -/

variable [DecidableEq V]

/-- **Strong duality for a maximum assignment.** The minimum cut bound between distinct terminals
is the value of any bounded `s`–`t` assignment of largest value. -/
theorem minimumValue_cutBound (hst : s ≠ t) (f : BoundedFlow lo hi s t)
    (hf : ∀ g : BoundedFlow lo hi s t, g.val ≤ f.val) :
    TerminalCut.minimumValue (cutBound lo hi) (disjoint_singleton.2 hst) = f.val := by
  obtain ⟨S, hs, ht, hS⟩ := (f.forall_val_le_iff_exists_cutBound_eq hst).1 hf
  obtain ⟨T, hT⟩ := TerminalCut.exists_minimum (cutBound lo hi) (disjoint_singleton.2 hst)
  obtain ⟨hTs, hTt⟩ := TerminalCut.isAdmissible_singleton.1 hT.admissible
  rw [← ((TerminalCut.isMinimum_iff_value_eq _ _).1 hT).2]
  exact le_antisymm (hS ▸ hT.le (TerminalCut.isAdmissible_singleton.2 ⟨hs, ht⟩))
    (f.val_le_cutBound hTs hTt)

/-- For a bounded `s`–`t` assignment of largest value, the minimum cuts of the cut bound are
exactly the vertex sets containing `s` but not `t` whose cut bound is the value. -/
theorem isMinimum_cutBound_iff_cutBound_eq (hst : s ≠ t) (f : BoundedFlow lo hi s t)
    (hf : ∀ g : BoundedFlow lo hi s t, g.val ≤ f.val) {S : Finset V} :
    TerminalCut.IsMinimum (cutBound lo hi) {s} {t} S ↔
      s ∈ S ∧ t ∉ S ∧ cutBound lo hi S = f.val := by
  rw [TerminalCut.isMinimum_iff_value_eq _ (disjoint_singleton.2 hst),
    TerminalCut.isAdmissible_singleton, f.minimumValue_cutBound hst hf, and_assoc]

/-- For a bounded `s`–`t` assignment of largest value, the minimum cuts of the cut bound are
exactly the vertex sets containing `s` but not `t` that no positive residual arrow leaves. -/
theorem isMinimum_cutBound_iff_isEmpty (hst : s ≠ t) (f : BoundedFlow lo hi s t)
    (hf : ∀ g : BoundedFlow lo hi s t, g.val ≤ f.val) {S : Finset V} :
    TerminalCut.IsMinimum (cutBound lo hi) {s} {t} S ↔
      s ∈ S ∧ t ∉ S ∧ ∀ v ∈ S, ∀ w ∉ S, IsEmpty (PosResidualHom lo hi f.toFun v w) := by
  rw [f.isMinimum_cutBound_iff_cutBound_eq hst hf]
  exact and_congr_right fun hs ↦ and_congr_right fun ht ↦ f.cutBound_eq_val_iff hs ht

/-- For a bounded `s`–`t` assignment of largest value, a vertex lies on the source side of every
minimum cut exactly when it is reachable from `s` along positive residual arrows. -/
theorem forall_isMinimum_mem_iff (hst : s ≠ t) (f : BoundedFlow lo hi s t)
    (hf : ∀ g : BoundedFlow lo hi s t, g.val ≤ f.val) {v : V} :
    (∀ S, TerminalCut.IsMinimum (cutBound lo hi) {s} {t} S → v ∈ S) ↔
      ArrowReachable (PosResidualHom lo hi f.toFun) s v := by
  classical
  refine ⟨fun h ↦ ?_, fun h S hS ↦ ?_⟩
  · let R := univ.filter (ArrowReachable (PosResidualHom lo hi f.toFun) s)
    have hR : ∀ v, v ∈ R ↔ ArrowReachable (PosResidualHom lo hi f.toFun) s v := by simp [R]
    have hst' := (f.forall_val_le_iff_not_arrowReachable hst).1 hf
    exact (hR v).1 (h R ((f.isMinimum_cutBound_iff_cutBound_eq hst hf).2
      ⟨(hR s).2 (.refl s), mt (hR t).1 hst', f.cutBound_eq_val_of_forall_mem_iff hR hst'⟩))
  · obtain ⟨hs, -, hS⟩ := (f.isMinimum_cutBound_iff_isEmpty hst hf).1 hS
    exact ArrowReachable.mem_of_mem (S := ↑S) hS hs h

/-- For a bounded `s`–`t` assignment of largest value, a vertex lies on the source side of no
minimum cut exactly when `t` is reachable from it along positive residual arrows. -/
theorem forall_isMinimum_notMem_iff (hst : s ≠ t) (f : BoundedFlow lo hi s t)
    (hf : ∀ g : BoundedFlow lo hi s t, g.val ≤ f.val) {v : V} :
    (∀ S, TerminalCut.IsMinimum (cutBound lo hi) {s} {t} S → v ∉ S) ↔
      ArrowReachable (PosResidualHom lo hi f.toFun) v t := by
  classical
  refine ⟨fun h ↦ ?_, fun h S hS hv ↦ ?_⟩
  · let L := univ.filter fun v ↦ ¬ ArrowReachable (PosResidualHom lo hi f.toFun) v t
    have hL : ∀ v, v ∈ L ↔ ¬ ArrowReachable (PosResidualHom lo hi f.toFun) v t := by simp [L]
    have hst' := (f.forall_val_le_iff_not_arrowReachable hst).1 hf
    have hs : s ∈ L := (hL s).2 hst'
    have ht : t ∉ L := fun ht ↦ (hL t).1 ht (.refl t)
    exact not_not.1 (mt (hL v).2 (h L ((f.isMinimum_cutBound_iff_cutBound_eq hst hf).2
      ⟨hs, ht, f.cutBound_eq_val_of_forall_mem_iff_not hL hst'⟩)))
  · obtain ⟨-, ht, hS⟩ := (f.isMinimum_cutBound_iff_isEmpty hst hf).1 hS
    exact ht (ArrowReachable.mem_of_mem (S := ↑S) hS hv h)

/-- For a bounded `s`–`t` assignment of largest value, the smallest minimum cut consists of the
vertices reachable from `s` along positive residual arrows. -/
theorem mem_smallest_iff_arrowReachable (hst : s ≠ t) (f : BoundedFlow lo hi s t)
    (hf : ∀ g : BoundedFlow lo hi s t, g.val ≤ f.val) (hc : IsSubmodular (cutBound lo hi)) {v : V} :
    v ∈ TerminalCut.smallest hc (disjoint_singleton.2 hst) ↔
      ArrowReachable (PosResidualHom lo hi f.toFun) s v := by
  rw [TerminalCut.mem_smallest_iff, f.forall_isMinimum_mem_iff hst hf]

/-- For a bounded `s`–`t` assignment of largest value, the largest minimum cut consists of the
vertices from which `t` is not reachable along positive residual arrows. -/
theorem mem_largest_iff_not_arrowReachable (hst : s ≠ t) (f : BoundedFlow lo hi s t)
    (hf : ∀ g : BoundedFlow lo hi s t, g.val ≤ f.val) (hc : IsSubmodular (cutBound lo hi)) {v : V} :
    v ∈ TerminalCut.largest hc (disjoint_singleton.2 hst) ↔
      ¬ ArrowReachable (PosResidualHom lo hi f.toFun) v t := by
  rw [TerminalCut.mem_largest_iff, ← f.forall_isMinimum_notMem_iff hst hf]
  simp only [not_forall, not_not, exists_prop]

/-- For a bounded `s`–`t` assignment of largest value, the minimum cut is unique exactly when every
vertex is reachable from `s` or reaches `t` along positive residual arrows. -/
theorem existsUnique_isMinimum_iff (hst : s ≠ t) (f : BoundedFlow lo hi s t)
    (hf : ∀ g : BoundedFlow lo hi s t, g.val ≤ f.val) :
    (∃! S, TerminalCut.IsMinimum (cutBound lo hi) {s} {t} S) ↔
      ∀ v, ArrowReachable (PosResidualHom lo hi f.toFun) s v ∨
        ArrowReachable (PosResidualHom lo hi f.toFun) v t := by
  have hst' := (f.forall_val_le_iff_not_arrowReachable hst).1 hf
  refine ⟨fun ⟨S, hS, huniq⟩ v ↦ ?_, fun h ↦ ?_⟩
  · by_cases hv : v ∈ S
    · exact .inl ((f.forall_isMinimum_mem_iff hst hf).1 fun T hT ↦ huniq T hT ▸ hv)
    · exact .inr ((f.forall_isMinimum_notMem_iff hst hf).1 fun T hT ↦ huniq T hT ▸ hv)
  · obtain ⟨S, hS⟩ := TerminalCut.exists_minimum (cutBound lo hi) (disjoint_singleton.2 hst)
    refine ⟨S, hS, fun T hT ↦ ext fun v ↦ ?_⟩
    have hmem := f.forall_isMinimum_mem_iff hst hf (v := v)
    have hnotMem := f.forall_isMinimum_notMem_iff hst hf (v := v)
    rcases h v with hv | hv
    · exact iff_of_true (hmem.2 hv T hT) (hmem.2 hv S hS)
    · exact iff_of_false (hnotMem.2 hv T hT) (hnotMem.2 hv S hS)

omit [DecidableEq V] in
/-- Residual reachability from the source is the same for any two bounded `s`–`t` assignments of
largest value. -/
theorem arrowReachable_source_iff (hst : s ≠ t) {f g : BoundedFlow lo hi s t}
    (hf : ∀ h : BoundedFlow lo hi s t, h.val ≤ f.val)
    (hg : ∀ h : BoundedFlow lo hi s t, h.val ≤ g.val) {v : V} :
    ArrowReachable (PosResidualHom lo hi f.toFun) s v ↔
      ArrowReachable (PosResidualHom lo hi g.toFun) s v := by
  classical
  rw [← f.forall_isMinimum_mem_iff hst hf, g.forall_isMinimum_mem_iff hst hg]

omit [DecidableEq V] in
/-- Residual reachability of the sink is the same for any two bounded `s`–`t` assignments of
largest value. -/
theorem arrowReachable_sink_iff (hst : s ≠ t) {f g : BoundedFlow lo hi s t}
    (hf : ∀ h : BoundedFlow lo hi s t, h.val ≤ f.val)
    (hg : ∀ h : BoundedFlow lo hi s t, h.val ≤ g.val) {v : V} :
    ArrowReachable (PosResidualHom lo hi f.toFun) v t ↔
      ArrowReachable (PosResidualHom lo hi g.toFun) v t := by
  classical
  rw [← f.forall_isMinimum_notMem_iff hst hf, g.forall_isMinimum_notMem_iff hst hg]

end LinearOrder

end BoundedFlow

/-! ### Ordinary flows -/

namespace Flow

variable [LinearOrder K] [IsOrderedAddMonoid K] {cap : Assignment Q K} {s t : V}

omit [IsOrderedAddMonoid K] in
/-- An ordinary `s`–`t` flow has the largest value among ordinary flows exactly when it has the
largest value among all capacity-feasible `s`–`t` assignments, including those of negative
value. -/
theorem forall_val_le_iff_forall_boundedFlow (f : Flow cap s t) :
    (∀ g : Flow cap s t, g.val ≤ f.val) ↔ ∀ g : BoundedFlow 0 cap s t, g.val ≤ f.val := by
  refine ⟨fun hf g ↦ ?_, fun hf g ↦ hf g.toBoundedFlow⟩
  rcases le_total g.val 0 with hg | hg
  · exact hg.trans f.val_nonneg
  · exact hf ⟨g, g.val_def ▸ hg⟩

/-- **Optimality criterion.** An ordinary flow between distinct terminals is maximum exactly when
there is no augmenting path: `t` is not reachable from `s` along positive residual arrows. -/
theorem forall_val_le_iff_not_arrowReachable (hst : s ≠ t) (f : Flow cap s t) :
    (∀ g : Flow cap s t, g.val ≤ f.val) ↔ ¬ ArrowReachable (PosResidualHom 0 cap f.toFun) s t := by
  rw [forall_val_le_iff_forall_boundedFlow,
    f.toBoundedFlow.forall_val_le_iff_not_arrowReachable hst]

/-- **Optimality criterion.** An ordinary flow between distinct terminals is maximum exactly when
its value equals the capacity of the arrows leaving some vertex set containing `s` but not `t`. -/
theorem forall_val_le_iff_exists_arrowSum_eq [DecidableEq V] (hst : s ≠ t) (f : Flow cap s t) :
    (∀ g : Flow cap s t, g.val ≤ f.val) ↔
      ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ arrowSum cap S Sᶜ = f.val := by
  simp only [forall_val_le_iff_forall_boundedFlow,
    f.toBoundedFlow.forall_val_le_iff_exists_cutBound_eq hst, cutBound_zero_left]

end Flow

end TauCeti
