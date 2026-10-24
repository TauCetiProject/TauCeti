/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import TauCeti.Combinatorics.Network.Decomposition

/-!
# Acyclic assignments and acyclic flows

An arrow assignment is *acyclic* when no directed cycle traverses only arrows of positive value.
Cancelling such cycles one at a time, each by its least arrow value, turns every nonnegative
assignment on a finite arrow family into an acyclic one that is arrowwise no larger and has the
same excess at every vertex. For an ordinary `s`–`t` flow this gives an acyclic flow of the same
value. A nonnegative acyclic assignment vanishes on every loop and on at least one arrow of every
pair of opposite arrows. The path–cycle decomposition of an acyclic assignment has no cycles, so
an acyclic ordinary flow carries at most its value on every arrow.

Acyclicity is stronger than having a decomposition without cycles: unit flows along
`s → a → b → t` and `s → b → a → t` add up to a flow that these two paths decompose, but whose
arrows of positive value contain the cycle `a → b → a`.

## Main results

* `TauCeti.Assignment.IsAcyclic.apply_eq_zero_or_apply_eq_zero` and
  `TauCeti.Assignment.IsAcyclic.apply_eq_zero_of_loop`: a nonnegative acyclic assignment vanishes
  on one of any two opposite arrows, and on every loop.
* `TauCeti.exists_isAcyclic_le`: **cycle cancelling**. Below every nonnegative assignment lies an
  acyclic nonnegative assignment with the same excess at every vertex, whose values lie in any
  additive subgroup containing the values of the original assignment.
* `TauCeti.Flow.exists_isAcyclic_mem` and `TauCeti.Flow.exists_isAcyclic`: below every ordinary
  flow lies an acyclic flow of the same value.
* `TauCeti.PathCycleDecomposition.cycles_eq_nil_of_isAcyclic`: a path–cycle decomposition of an
  acyclic assignment has no cycles.
* `TauCeti.Flow.toFun_le_val_of_isAcyclic`: an acyclic ordinary flow carries at most its value
  on every arrow.

## References

* L. R. Ford, D. R. Fulkerson, *Flows in Networks*, Princeton University Press, 1962.
* R. K. Ahuja, T. L. Magnanti, J. B. Orlin, *Network Flows: Theory, Algorithms, and
  Applications*, Prentice Hall, 1993, Section 3.5.
-/

public section

namespace TauCeti

open Finset Relation

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

namespace Assignment

section LT

variable [Zero K] [LT K]

/-- An acyclic assignment is not positive on two opposite arrows. -/
theorem IsAcyclic.not_pos_and_pos {f : Assignment Q K} (hf : f.IsAcyclic) {x y : V} (e : Q x y)
    (e' : Q y x) : ¬(0 < f e ∧ 0 < f e') := fun h ↦
  (isAcyclic_iff_forall_not_transGen f).1 hf x (.tail (.single ⟨e, h.1⟩) ⟨e', h.2⟩)

end LT

section Preorder

variable [Zero K] [Preorder K]

@[simp]
theorem isAcyclic_zero : (0 : Assignment Q K).IsAcyclic := by
  rw [isAcyclic_iff_forall_not_transGen]
  intro v h
  obtain ⟨_, _, _, he⟩ := TransGen.tail'_iff.1 h
  simp at he

/-- An assignment below an acyclic one is acyclic. -/
theorem IsAcyclic.anti {f g : Assignment Q K} (hfg : f ≤ g) (hg : g.IsAcyclic) : f.IsAcyclic :=
  (isAcyclic_def f).2 fun _ c hc hpos ↦
    (isAcyclic_def g).1 hg c hc fun a ha ↦ (hpos a ha).trans_le (hfg _ _ a.2.2)

end Preorder

section PartialOrder

variable [Zero K] [PartialOrder K] {f : Assignment Q K}

/-- A nonnegative acyclic assignment vanishes on one of any two opposite arrows. -/
theorem IsAcyclic.apply_eq_zero_or_apply_eq_zero (hf : f.IsAcyclic) (hf₀ : 0 ≤ f) {x y : V}
    (e : Q x y) (e' : Q y x) : f e = 0 ∨ f e' = 0 := by
  by_contra! h
  exact hf.not_pos_and_pos e e' ⟨(hf₀ _ _ e).lt_of_ne' h.1, (hf₀ _ _ e').lt_of_ne' h.2⟩

/-- A nonnegative acyclic assignment vanishes on every loop. -/
theorem IsAcyclic.apply_eq_zero_of_loop (hf : f.IsAcyclic) (hf₀ : 0 ≤ f) {x : V} (e : Q x x) :
    f e = 0 :=
  (hf.apply_eq_zero_or_apply_eq_zero hf₀ e e).elim id id

end PartialOrder

end Assignment

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

/-! ### Cycle cancelling -/

section CycleCancelling

variable [LinearOrder K] [IsOrderedAddMonoid K]

/-- **Cycle cancelling.** Below every nonnegative arrow assignment `f` on a finite arrow family
lies an acyclic nonnegative assignment with the same excess as `f` at every vertex. If the values
of `f` lie in an additive subgroup `H`, then so do those of the acyclic assignment. -/
theorem exists_isAcyclic_le (H : AddSubgroup K) {f : Assignment Q K} (hf : 0 ≤ f)
    (hH : ∀ ⦃x y : V⦄ (e : Q x y), f e ∈ H) :
    ∃ g : Assignment Q K, g.IsAcyclic ∧ 0 ≤ g ∧ g ≤ f ∧ (∀ v, excessAt g v = excessAt f v) ∧
      ∀ ⦃x y : V⦄ (e : Q x y), g e ∈ H := by
  classical
  -- Induct on the number of arrows of positive value.
  suffices ∀ n (f : Assignment Q K), 0 ≤ f → (∀ ⦃x y : V⦄ (e : Q x y), f e ∈ H) →
      #{a : Σ x y, Q x y | 0 < f a.2.2} = n →
      ∃ g : Assignment Q K, g.IsAcyclic ∧ 0 ≤ g ∧ g ≤ f ∧
        (∀ v, excessAt g v = excessAt f v) ∧ ∀ ⦃x y : V⦄ (e : Q x y), g e ∈ H from
    this _ f hf hH rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf hH hn
  subst hn
  by_cases hacyc : f.IsAcyclic
  · exact ⟨f, hacyc, hf, le_rfl, fun _ ↦ rfl, hH⟩
  -- Subtract a cycle of positive arrows, weighted by its bottleneck: this leaves a nonnegative
  -- assignment with the same excess, values in `H`, and fewer arrows of positive value.
  obtain ⟨v, c, hc, hpos⟩ :
      ∃ v, ∃ c : ArrowWalk Q v v, c.IsCycle ∧ ∀ a ∈ c.arrows, 0 < f a.2.2 := by
    rw [Assignment.isAcyclic_def] at hacyc
    push Not at hacyc
    exact hacyc
  have hne : c.arrows ≠ [] := fun h ↦
    ((ArrowWalk.isCycle_def c).1 hc).1.ne' (ArrowWalk.arrows_eq_nil_iff.1 h)
  have hqH : c.bottleneck f hne ∈ H :=
    ArrowWalk.bottleneck_mem (A := (H : Set K)) fun a _ ↦ hH a.2.2
  obtain ⟨g, hg, hg₀, hgf, hexc, hgH⟩ :=
    ih _ (card_filter_pos_sub_walkAssignment_bottleneck_lt hc.nodup_arrows hne hpos) _
      (sub_nonneg.2 (walkAssignment_bottleneck_le hf hc.nodup_arrows hne))
      (fun x y e ↦ H.sub_mem (hH e) (walkAssignment_mem c hqH e)) rfl
  refine ⟨g, hg, hg₀, hgf.trans <| sub_le_self _ <|
    walkAssignment_nonneg c (ArrowWalk.lt_bottleneck_iff.2 hpos).le, fun v ↦ ?_, hgH⟩
  rw [hexc, excessAt_sub, (isCirculation_iff _).1 (isCirculation_walkAssignment _ _), sub_zero]

variable {cap : Assignment Q K} {s t : V}

/-- **Acyclic flows.** Every ordinary `s`–`t` flow `f` has an acyclic ordinary `s`–`t` flow of the
same value that is arrowwise at most `f`. If the values of `f` lie in an additive subgroup `H`,
then so do those of the acyclic flow. -/
theorem Flow.exists_isAcyclic_mem (f : Flow cap s t) (H : AddSubgroup K)
    (hH : ∀ ⦃x y : V⦄ (e : Q x y), f.toFun e ∈ H) :
    ∃ g : Flow cap s t, g.toFun.IsAcyclic ∧ g.val = f.val ∧ g.toFun ≤ f.toFun ∧
      ∀ ⦃x y : V⦄ (e : Q x y), g.toFun e ∈ H := by
  obtain ⟨g, hg, hg₀, hgf, hexc, hgH⟩ := exists_isAcyclic_le H (fun _ _ e ↦ f.nonneg e) hH
  let g' : Flow cap s t :=
    { toFun := g
      mem_Icc := ⟨hg₀, hgf.trans f.mem_Icc.2⟩
      conserve v hvs hvt := (hexc v).trans (f.conserve v hvs hvt)
      excessAt_sink_nonneg := (hexc t).symm ▸ f.excessAt_sink_nonneg }
  exact ⟨g', hg, g'.val_def.trans ((hexc t).trans f.val_def.symm), hgf, hgH⟩

/-- **Acyclic flows.** Every ordinary `s`–`t` flow `f` has an acyclic ordinary `s`–`t` flow of the
same value that is arrowwise at most `f`. -/
theorem Flow.exists_isAcyclic (f : Flow cap s t) :
    ∃ g : Flow cap s t, g.toFun.IsAcyclic ∧ g.val = f.val ∧ g.toFun ≤ f.toFun :=
  let ⟨g, hg, hval, hle, _⟩ := f.exists_isAcyclic_mem ⊤ fun _ _ _ ↦ AddSubgroup.mem_top _
  ⟨g, hg, hval, hle⟩

end CycleCancelling

/-! ### Decompositions of acyclic assignments -/

section Decomposition

variable [PartialOrder K] [IsOrderedAddMonoid K] {f : Assignment Q K}

/-- A path–cycle decomposition of an acyclic assignment has no cycles. -/
theorem PathCycleDecomposition.cycles_eq_nil_of_isAcyclic (D : PathCycleDecomposition f)
    (hf : f.IsAcyclic) : D.cycles = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun c hc ↦
    (Assignment.isAcyclic_def f).1 hf c.walk (D.isCycle_walk c hc) fun a ha ↦ by
      have hle := D.assignment_le_of_mem_cycles hc a.1 a.2.1 a.2.2
      rw [WeightedClosedWalk.assignment_def,
        walkAssignment_eq_of_mem (D.isCycle_walk c hc).nodup_arrows _ ha] at hle
      exact (D.weight_pos_of_mem_cycles c hc).trans_le hle

/-- The paths of a path–cycle decomposition of an acyclic assignment add up to the assignment. -/
theorem PathCycleDecomposition.pathAssignment_eq_of_isAcyclic (D : PathCycleDecomposition f)
    (hf : f.IsAcyclic) : D.pathAssignment = f := by
  conv_rhs => rw [← D.pathAssignment_add_cycleAssignment]
  simp [D.cycleAssignment_def, D.cycles_eq_nil_of_isAcyclic hf]

end Decomposition

section LinearOrder

variable [LinearOrder K] [IsOrderedAddMonoid K] {cap : Assignment Q K} {s t : V}

/-- An acyclic ordinary `s`–`t` flow carries at most its value on every arrow. -/
theorem Flow.toFun_le_val_of_isAcyclic (f : Flow cap s t) (hf : f.toFun.IsAcyclic) {x y : V}
    (e : Q x y) : f.toFun e ≤ f.val := by
  obtain ⟨D⟩ := nonempty_pathCycleDecomposition (f := f.toFun) fun _ _ e ↦ f.nonneg e
  rw [← D.pathAssignment_eq_of_isAcyclic hf, ← D.sum_weight_paths_eq_val,
    PathCycleDecomposition.pathAssignment_def]
  simp only [Pi.list_sum_apply, List.map_map, Function.comp_def, WeightedWalk.assignment_def]
  refine List.sum_le_sum fun p hp ↦ ?_
  have hq := (D.weight_pos_of_mem_paths p hp).le
  exact walkAssignment_le (D.isPath_walk p hp).nodup_arrows hq e

end LinearOrder

end TauCeti
