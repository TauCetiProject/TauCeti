/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Loops on the boundary of a cylinder

For a closed subset `S` of an arbitrary space, the frontier inclusion of `S × [a, b]`
is surjective on fundamental groups at every boundary basepoint. No connectedness,
local connectedness, compactness or manifold assumption on `S` is needed.

Loops based on an end face are moved vertically into that face. A point on the side
boundary can first be joined vertically to an end face, and basepoint change transports
surjectivity back. For product models of handlebodies, this is the boundary surjection
used in the van Kampen argument for Heegaard splittings.

## References

* J. Hempel, *3-Manifolds*, Chapter 2 (handlebodies and their boundary inclusions).
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {s : Set X} {a b c : ℝ}

private lemma mk_mem_frontier_prod_Icc_of_mem_frontier {y : X}
    (hy : y ∈ s) (hc : c ∈ frontier (Icc a b)) :
    (y, c) ∈ frontier (s ×ˢ Icc a b) := by
  rw [frontier_prod_eq]
  exact Or.inl ⟨subset_closure hy, hc⟩

/-- A loop in a closed cylinder based on an end face can be moved into the frontier,
without moving its basepoint. This also includes a degenerate interval. -/
private theorem exists_path_frontier_prod_Icc (hs : IsClosed s)
    (hc : c ∈ frontier (Icc a b)) (x : s) :
    let hface := mk_mem_frontier_prod_Icc_of_mem_frontier x.2 hc
    let hsub := (hs.prod isClosed_Icc).frontier_subset
    ∀ q : Path (⟨(x.1, c), x.2, isClosed_Icc.frontier_subset hc⟩ : s ×ˢ Icc a b)
        ⟨(x.1, c), x.2, isClosed_Icc.frontier_subset hc⟩,
      ∃ p : Path (⟨(x.1, c), hface⟩ : frontier (s ×ˢ Icc a b)) ⟨(x.1, c), hface⟩,
        (p.map (continuous_inclusion hsub)).Homotopic q := by
  intro hface hsub q
  let p : Path (⟨(x.1, c), hface⟩ : frontier (s ×ˢ Icc a b)) ⟨(x.1, c), hface⟩ :=
    { toFun := fun t => ⟨((q t).1.1, c),
        mk_mem_frontier_prod_Icc_of_mem_frontier (q t).2.1 hc⟩
      continuous_toFun := by fun_prop
      source' := by apply Subtype.ext; simp
      target' := by apply Subtype.ext; simp }
  refine ⟨p, ⟨?_⟩⟩
  refine
    { toFun := fun z => ⟨((q z.2).1.1, (1 - (z.1 : ℝ)) * c + z.1 * (q z.2).1.2),
        (q z.2).2.1, ?_⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun t => by apply Subtype.ext; simp [p]
      map_one_left := fun t => by apply Subtype.ext; simp
      prop' := ?_ }
  · exact (convex_Icc a b) (isClosed_Icc.frontier_subset hc) (q z.2).2.2
      (sub_nonneg.mpr z.1.2.2) z.1.2.1 (by ring)
  · intro t u hu
    rcases hu with hu | hu <;> rcases hu with rfl <;>
      apply Subtype.ext <;> simp [p] <;> ring

/-- At an end-face basepoint, the frontier inclusion of a closed cylinder is surjective
on fundamental groups. -/
private theorem fundamentalGroupMap_frontier_prod_Icc_surjective_of_mem_frontier
    (hs : IsClosed s) (hc : c ∈ frontier (Icc a b)) (x : s) :
    let hface := mk_mem_frontier_prod_Icc_of_mem_frontier x.2 hc
    Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (hs.prod isClosed_Icc).frontier_subset)
      (⟨(x.1, c), hface⟩ : frontier (s ×ˢ Icc a b))) := by
  intro hface γ
  obtain ⟨q, hq⟩ := Quotient.exists_rep γ.asHom
  obtain ⟨p, hp⟩ := exists_path_frontier_prod_Icc hs hc x q
  refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p), ?_⟩
  rw [FundamentalGroup.map_fromPath]
  apply CategoryTheory.End.ext
  exact (Quotient.sound hp).trans hq

/-- The frontier of a closed cylinder surjects onto its fundamental group at every boundary
basepoint. The interval may be degenerate or empty; in the empty case there is no basepoint. -/
theorem fundamentalGroupMap_frontier_prod_Icc_surjective
    (hs : IsClosed s) (z : frontier (s ×ˢ Icc a b)) :
    Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (hs.prod isClosed_Icc).frontier_subset) z) := by
  let j : C(frontier (s ×ˢ Icc a b), s ×ˢ Icc a b) :=
    ContinuousMap.inclusion (hs.prod isClosed_Icc).frontier_subset
  have hz := (hs.prod isClosed_Icc).frontier_subset z.2
  have hcases := z.2
  simp only [frontier_prod_eq, mem_union, mem_prod] at hcases
  rcases hcases with hend | hside
  · exact fundamentalGroupMap_frontier_prod_Icc_surjective_of_mem_frontier hs hend.2
      ⟨z.1.1, hz.1⟩
  · have hab : a ≤ b := hz.2.1.trans hz.2.2
    have hb : b ∈ frontier (Icc a b) := by simp [frontier_Icc hab]
    let w : frontier (s ×ˢ Icc a b) :=
      ⟨(z.1.1, b), mk_mem_frontier_prod_Icc_of_mem_frontier hz.1 hb⟩
    let p : Path z w :=
      { toFun := fun t => ⟨(z.1.1, (1 - (t : ℝ)) * z.1.2 + t * b), by
          simp only [frontier_prod_eq, mem_union, mem_prod]
          exact Or.inr ⟨hside.1, subset_closure ((convex_Icc a b) hz.2 ⟨hab, le_rfl⟩
            (sub_nonneg.mpr t.2.2) t.2.1 (by ring))⟩⟩
        continuous_toFun := by fun_prop
        source' := by apply Subtype.ext; simp
        target' := by apply Subtype.ext; simp [w] }
    exact fundamentalGroupMap_surjective_of_path j p
      (fundamentalGroupMap_frontier_prod_Icc_surjective_of_mem_frontier hs hb ⟨z.1.1, hz.1⟩)

end TauCeti
