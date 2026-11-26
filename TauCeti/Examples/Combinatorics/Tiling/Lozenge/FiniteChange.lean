/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.FiniteChange
public import TauCeti.Combinatorics.Tiling.Lozenge.Flip
public import TauCeti.Combinatorics.Tiling.Lozenge.RowTiling

/-!
# Checks: finite changes preserve lozenge counts

* `T_a ∖ T_b = {(0,3), ((−1,0),1), ((0,−1),2)}` and `T_b ∖ T_a = {(0,1), (0,2), ((−1,−1),3)}`,
  where `T_a = highFlipEdges 0` and `T_b = lowFlipEdges 0` are the two tilings of the unit
  hexagon: one edge of each direction on each side. A flip of a plane tiling changes it on these
  six edges, and the counts agree, as `IsTiling.ncard_sdiff_inter_eq` predicts.
* The tilings `M₁ = edgesOfDir 0` and `M₃ = edgesOfDir 2` differ on infinitely many edges, so the
  theorem says nothing about them, although their numbers of type-1 lozenges differ.
* Row tilings `M_ε`, `M_ε'` with `ε`, `ε'` differing at one coordinate `x₀` differ along the whole
  column of edges `((x₀, y), 1)`, and the theorem says nothing about them either.
-/

public section

namespace TauCeti.Examples.LozengeFiniteChangeChecks

open TauCeti

/-- The set of edges satisfying a uniquely satisfied predicate has one element. -/
theorem ncard_eq_one_of_existsUnique {s : Set TriEdge} {k : Fin 3}
    (h : ∃! e, e ∈ s ∧ e.k = k) : (s ∩ edgesOfDir k).ncard = 1 := by
  obtain ⟨e, he, hu⟩ := h
  exact Set.ncard_eq_one.2 ⟨e, Set.eq_singleton_iff_unique_mem.2
    ⟨⟨he.1, mem_edgesOfDir.2 he.2⟩, fun x hx => hu x ⟨hx.1, mem_edgesOfDir.1 hx.2⟩⟩⟩

/-! ### The two tilings of the unit hexagon -/

/-- `T_a ∖ T_b = T_a = {(0,3), ((−1,0),1), ((0,−1),2)}`. -/
example : highFlipEdges 0 \ lowFlipEdges 0 = {⟨0, 2⟩, ⟨(-1, 0), 0⟩, ⟨(0, -1), 1⟩} := by
  rw [(disjoint_highFlipEdges_lowFlipEdges 0).sdiff_eq_left, highFlipEdges_def]
  simp

/-- `T_b ∖ T_a = T_b = {(0,1), (0,2), ((−1,−1),3)}`. -/
example : lowFlipEdges 0 \ highFlipEdges 0 = {⟨0, 0⟩, ⟨0, 1⟩, ⟨(-1, -1), 2⟩} := by
  rw [(disjoint_highFlipEdges_lowFlipEdges 0).symm.sdiff_eq_left, lowFlipEdges_def]
  simp

/-- `T_a ∖ T_b` and `T_b ∖ T_a` contain one edge of each direction. -/
example (k : Fin 3) :
    (highFlipEdges 0 \ lowFlipEdges 0 ∩ edgesOfDir k).ncard = 1 ∧
      (lowFlipEdges 0 \ highFlipEdges 0 ∩ edgesOfDir k).ncard = 1 := by
  rw [(disjoint_highFlipEdges_lowFlipEdges 0).sdiff_eq_left,
    (disjoint_highFlipEdges_lowFlipEdges 0).symm.sdiff_eq_left]
  exact ⟨ncard_eq_one_of_existsUnique (existsUnique_mem_highFlipEdges_k 0 k),
    ncard_eq_one_of_existsUnique (existsUnique_mem_lowFlipEdges_k 0 k)⟩

/-- A flip of a plane tiling changes finitely many edges, so the theorem applies to it. -/
example {M M' : Set TriEdge} {v : ℤ × ℤ} (hM : IsTiling Set.univ M) (hf : IsFlipAt v M M')
    (k : Fin 3) : (M \ M' ∩ edgesOfDir k).ncard = (M' \ M ∩ edgesOfDir k).ncard :=
  hM.ncard_sdiff_inter_eq (hf.isTiling hM) (by
    rw [hf.symmDiff_eq fun _ _ _ he _ he' hef he'f => hM.eq_of_mem_edges he he' hef he'f]
    rw [highFlipEdges_def, lowFlipEdges_def]
    exact Set.toFinite _) k

/-! ### Tilings differing on infinitely many edges -/

/-- A set containing every edge `((x, 0), k)`, `x ∈ ℤ`, is infinite. -/
theorem infinite_of_forall_mem {s : Set TriEdge} {k : Fin 3} (h : ∀ x : ℤ, ⟨(x, 0), k⟩ ∈ s) :
    s.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun x : ℤ => (⟨(x, 0), k⟩ : TriEdge))
    (fun x y hxy => by simpa using congrArg (fun e : TriEdge => e.v.1) hxy) h

/-- `M₁` and `M₃` differ on infinitely many edges. -/
example : (symmDiff (edgesOfDir 0) (edgesOfDir 2)).Infinite :=
  infinite_of_forall_mem (k := 0) fun x => Or.inl ⟨mem_edgesOfDir.2 rfl, by simp⟩

/-- Row tilings whose sequences differ at `x₀` differ along the whole column of edges
`((x₀, y), 1)`, so they differ on infinitely many edges. -/
example {ε ε' : ℤ → Bool} {x₀ : ℤ} (h : ε x₀ ≠ ε' x₀) :
    (symmDiff {e | rowTiling ε e = true} {e | rowTiling ε' e = true}).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun y : ℤ => (⟨(x₀, y), 0⟩ : TriEdge))
    (fun y y' hyy' => by simpa using congrArg (fun e : TriEdge => e.v.2) hyy') fun y => ?_
  cases hε : ε x₀ <;> cases hε' : ε' x₀ <;> simp_all [Set.mem_symmDiff]

end TauCeti.Examples.LozengeFiniteChangeChecks
