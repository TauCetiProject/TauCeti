/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Continuous
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Closed
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Generation of the graded pieces of the closed lower central series

The brackets of a topological generating set with a graded piece topologically generate the next
piece. For a compact Hausdorff group and a finite generating set, their sums fill the next piece.
The distinction matters because the closed lower central series terms need not be open.
-/

public section

open scoped commutatorElement

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The brackets with a topological generating set generate the next closed-series graded piece
after taking closure. -/
theorem topologicalClosure_closure_lcsBracket_eq_top (n : ℕ) {S : Set G}
    (hS : (Subgroup.closure S).topologicalClosure = ⊤) :
    (AddSubgroup.closure (Set.range (fun sy : S × gradedPiece 0 G n ↦
      gradedBracket 0 G 0 n (gradedMkZero 0 G sy.1) sy.2))).topologicalClosure = ⊤ := by
  let W : AddSubgroup (gradedPiece 0 G (0 + n + 1)) :=
    (AddSubgroup.closure (Set.range (fun sy : S × gradedPiece 0 G n ↦
      gradedBracket 0 G 0 n (gradedMkZero 0 G sy.1) sy.2))).topologicalClosure
  have hWclosed : IsClosed (W : Set (gradedPiece 0 G (0 + n + 1))) :=
    AddSubgroup.isClosed_topologicalClosure _
  have hbracket (g : G) (y : gradedPiece 0 G n) :
      gradedBracket 0 G 0 n (gradedMkZero 0 G g) y ∈ W := by
    let V : Subgroup G :=
      { carrier := {g | gradedBracket 0 G 0 n (gradedMkZero 0 G g) y ∈ W}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simpa only [Set.mem_ofPred_eq, gradedMkZero_mul, map_add, AddMonoidHom.add_apply]
            using W.add_mem ha hb
        inv_mem' := by
          intro a ha
          simpa only [Set.mem_ofPred_eq, gradedMkZero_inv, map_neg, AddMonoidHom.neg_apply]
            using W.neg_mem ha }
    have hVclosed : IsClosed (V : Set G) := by
      convert hWclosed.preimage ((continuous_gradedBracket (p := 0) (G := G) 0 n).comp
        ((continuous_gradedMkZero (p := 0) (G := G)).prodMk
          (continuous_const : Continuous fun _ : G ↦ y))) using 1
      rfl
    have hSV : Subgroup.closure S ≤ V := (Subgroup.closure_le V).mpr (by
      rintro s hs
      exact AddSubgroup.le_topologicalClosure _
        (AddSubgroup.subset_closure ⟨(⟨s, hs⟩, y), rfl⟩))
    have htop := Subgroup.topologicalClosure_minimal _ hSV hVclosed
    exact htop (hS.symm ▸ Subgroup.mem_top g)
  let K : Subgroup G := pLowerCentralSeries 0 G n
  let H : Subgroup G := pLowerCentralSeries 0 G (0 + n + 1)
  let U : Subgroup H :=
    { carrier := {x | gradedMk 0 G (0 + n + 1) x ∈ W}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simpa only [H, Set.mem_ofPred_eq, gradedMk_mul] using W.add_mem ha hb
      inv_mem' := by
        intro a ha
        simpa only [H, Set.mem_ofPred_eq, gradedMk_inv] using W.neg_mem ha }
  have hUclosed : IsClosed (U : Set H) :=
    hWclosed.preimage (continuous_gradedMk (0 + n + 1))
  have hHclosed : IsClosed (H : Set G) := isClosed_pLowerCentralSeries _
  have hUambient : IsClosed ((U : Subgroup H).map H.subtype : Set G) := by
    convert hHclosed.isClosedEmbedding_subtypeVal.isClosedMap (U : Set H) hUclosed using 1
    ext z
    simp only [SetLike.mem_coe, Subgroup.mem_map, Set.mem_image]
    rfl
  have hcomm : ⁅(⊤ : Subgroup G), K⁆ ≤ U.map H.subtype := by
    refine Subgroup.commutator_le.mpr ?_
    intro b _ a ha
    have hba : ⁅b, a⁆ ∈ H :=
      commutator_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero 0 b) ha
    refine ⟨⟨⁅b, a⁆, hba⟩, ?_, rfl⟩
    have hb := hbracket b (gradedMk 0 G n ⟨a, ha⟩)
    rw [← gradedMk_zero (p := 0) (G := G) ⟨b, mem_pLowerCentralSeries_zero 0 b⟩] at hb
    rw [gradedBracket_gradedMk] at hb
    simpa [U] using hb
  have hseries : H ≤ U.map H.subtype := by
    have heq : H = ⁅(⊤ : Subgroup G), K⁆.topologicalClosure := by
      simpa only [K, H, zero_add, closedLowerCentralSeries_def, Subgroup.commutator_comm] using
        (closedLowerCentralSeries_succ (G := G) n)
    calc
      H = ⁅(⊤ : Subgroup G), K⁆.topologicalClosure := heq
      _ ≤ U.map H.subtype := Subgroup.topologicalClosure_minimal _ hcomm hUambient
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨x, rfl⟩ := gradedMk_surjective (p := 0) (G := G) (0 + n + 1) z
  obtain ⟨y, hy, hxy⟩ := hseries x.2
  have hxy' : y = x := Subtype.ext hxy
  simpa [U, hxy'] using hy

/-- For a finite generating set in a compact Hausdorff group, every class in the next graded
piece is one sum of brackets with the generators. -/
theorem exists_sum_lcsBracket_eq [CompactSpace G] [T2Space G] (n : ℕ)
    (S : Finset G) (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤)
    (z : gradedPiece 0 G (0 + n + 1)) :
    ∃ y : S → gradedPiece 0 G n,
      (∑ s : S, gradedBracket 0 G 0 n (gradedMkZero 0 G s) (y s)) = z := by
  classical
  have : CompactSpace (pLowerCentralSeries 0 G n) :=
    isCompact_iff_compactSpace.mp (isClosed_pLowerCentralSeries n).isCompact
  have : CompactSpace (gradedPiece 0 G n) := inferInstance
  have : CompactSpace (S → gradedPiece 0 G n) := inferInstance
  have : IsClosed ((pLowerCentralSeries 0 G (0 + n + 1 + 1)).subgroupOf
      (pLowerCentralSeries 0 G (0 + n + 1)) : Set (pLowerCentralSeries 0 G (0 + n + 1))) := by
    exact (isClosed_pLowerCentralSeries (0 + n + 1 + 1)).preimage continuous_subtype_val
  have : T2Space (gradedPiece 0 G (0 + n + 1)) := QuotientGroup.instT2Space
  let f : (S → gradedPiece 0 G n) →+ gradedPiece 0 G (0 + n + 1) :=
    { toFun := fun y ↦ ∑ s : S, gradedBracket 0 G 0 n (gradedMkZero 0 G s) (y s)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib] }
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro s _
    exact (continuous_gradedBracket (p := 0) (G := G) 0 n).comp
      (continuous_const.prodMk (continuous_apply s))
  have hrange : IsClosed (f.range : Set (gradedPiece 0 G (0 + n + 1))) :=
    (isCompact_range hf).isClosed
  have hgen (s : S) (y : gradedPiece 0 G n) :
      gradedBracket 0 G 0 n (gradedMkZero 0 G s) y ∈ f.range := by
    refine ⟨Pi.single s y, ?_⟩
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ hts
      simp [hts]
    · intro hs
      exact False.elim (hs (Finset.mem_attach S s))
  have hW : (AddSubgroup.closure (Set.range (fun sy : ↥(S : Set G) × gradedPiece 0 G n ↦
      gradedBracket 0 G 0 n (gradedMkZero 0 G sy.1) sy.2))).topologicalClosure ≤ f.range := by
    refine AddSubgroup.topologicalClosure_minimal _ ((AddSubgroup.closure_le _).mpr ?_) hrange
    rintro _ ⟨⟨s, y⟩, rfl⟩
    exact hgen ⟨s.1, s.2⟩ y
  have htop := topologicalClosure_closure_lcsBracket_eq_top n hS
  have hsurj : f.range = ⊤ := top_le_iff.mp (htop ▸ hW)
  obtain ⟨y, hy⟩ := hsurj.symm ▸ AddSubgroup.mem_top z
  exact ⟨y, hy⟩

end TauCeti
