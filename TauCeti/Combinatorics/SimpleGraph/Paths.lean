/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Cutting and closing up paths and cycles

This file collects general facts about paths and cycles in a simple graph, complementing Mathlib's
`Mathlib/Combinatorics/SimpleGraph/Paths.lean`.

## Main results

* `SimpleGraph.Walk.IsPath.start_notMem_tail_support`: a path does not return to its start.
* `SimpleGraph.Walk.IsCycle.isPath_append_of_append_append`: cutting an arc of positive length
  out of a cycle leaves a path.
* `SimpleGraph.Walk.mem_support_append_of_mem_support_append_append`: the vertices of a closed
  walk outside the interior of such an arc lie on the remaining path.
* `SimpleGraph.Walk.IsPath.isCycle_append_append_reverse`: two paths from a common vertex close
  up with a third path into a cycle.
-/

public section

universe u

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V}

/-- A path does not return to its start. -/
theorem IsPath.start_notMem_tail_support {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [← cons_tail_support] at h
  exact (List.nodup_cons.1 h).1

/-- Removing a subwalk of positive length from a cycle leaves a path: if `W₁`, `A`, `W₂` traverse
a cycle in turn and `A` is not trivial, then `W₂` followed by `W₁` is a path. -/
theorem IsCycle.isPath_append_of_append_append {u a b : V} {W₁ : G.Walk u a} {A : G.Walk a b}
    {W₂ : G.Walk b u} (hc : (W₁.append (A.append W₂)).IsCycle) (hA : ¬A.Nil) :
    (W₂.append W₁).IsPath := by
  have hnd := hc.support_nodup
  rw [tail_support_append, tail_support_append] at hnd
  have hbA : b ∈ A.support.tail := end_mem_tail_support hA
  rw [isPath_def, support_append, ← cons_tail_support W₂]
  simp only [List.nodup_append, List.nodup_cons, List.cons_append, List.mem_append] at hnd ⊢
  grind

/-- If `W₁`, `A`, `W₂` traverse a closed walk in turn, then every vertex of it that is not an
interior vertex of `A` lies on `W₂` followed by `W₁`. -/
theorem mem_support_append_of_mem_support_append_append {u a b v : V} {W₁ : G.Walk u a}
    {A : G.Walk a b} {W₂ : G.Walk b u} (hv : v ∈ (W₁.append (A.append W₂)).support)
    (hA : v ∈ A.support → v = a ∨ v = b) : v ∈ (W₂.append W₁).support := by
  rw [mem_support_append_iff, mem_support_append_iff] at hv
  rw [mem_support_append_iff]
  obtain hv | hv | hv := hv
  · exact .inr hv
  · obtain rfl | rfl := hA hv
    exacts [.inr W₁.end_mem_support, .inl W₂.start_mem_support]
  · exact .inl hv

/-- Two paths `P` and `Q` from `x` to distinct vertices `a` and `b`, sharing only `x`, close up
with a path `R` from `b` to `a` meeting them only at `a` and `b` into a cycle. -/
theorem IsPath.isCycle_append_append_reverse {x a b : V} {P : G.Walk x a} {Q : G.Walk x b}
    {R : G.Walk b a} (hP : P.IsPath) (hQ : Q.IsPath) (hR : R.IsPath) (hab : a ≠ b)
    (hPQ : ∀ v ∈ P.support, v ∈ Q.support → v = x)
    (hPR : ∀ v ∈ P.support, v ∈ R.support → v = a)
    (hQR : ∀ v ∈ Q.support, v ∈ R.support → v = b) :
    ((Q.append R).append P.reverse).IsCycle := by
  have hp : (Q.append R).IsPath := by
    refine (isPath_append _ _).2 ⟨hQ, hR.tail, fun v hvQ hvR ↦ ?_⟩
    exact hR.start_notMem_tail_support (hQR v hvQ (List.mem_of_mem_tail hvR) ▸ hvR)
  have hq : P.reverse.IsPath := hP.reverse
  refine hp.isCycle_append hq (fun v hvp hvq ↦ ?_) (.inl ?_)
  · have hvx : v ≠ x := fun hvx ↦ hp.start_notMem_tail_support (hvx ▸ hvp)
    have hva : v ≠ a := fun hva ↦ hq.start_notMem_tail_support (hva ▸ hvq)
    have hvP : v ∈ P.support := by simpa using List.mem_of_mem_tail hvq
    rcases (mem_support_append_iff _ _).1 (List.mem_of_mem_tail hvp) with hv | hv
    exacts [hvx (hPQ v hvP hv), hva (hPR v hvP hv)]
  · have hxR : x ∉ R.support := fun h ↦
      hab ((hPR x P.start_mem_support h).symm.trans (hQR x Q.start_mem_support h))
    have h₁ : Q.length ≠ 0 := fun h0 ↦ hxR (eq_of_length_eq_zero h0 ▸ R.start_mem_support)
    have h₂ : R.length ≠ 0 := fun h0 ↦ hab (eq_of_length_eq_zero h0).symm
    rw [length_append]
    omega

end SimpleGraph.Walk
