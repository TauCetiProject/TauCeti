/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.ProperSubgraph

/-!
# Edge factors in minimal numerical types of genus one

This file records the possible quotients of a positive intersection number by the weights at its
two endpoints when both components have self-intersection `-2w` inside a numerical type with more
than two components. These five pairs are the local input used by the finite classifications of
genus-one trees.

## References

* [Stacks Project, Lemma 55.5.3, Tag 0C7M](https://stacks.math.columbia.edu/tag/0C7M).
-/

public section

namespace TauCeti.NumericalType

universe u

variable {T : NumericalType.{u}}

/-- The endpoint-factor pairs allowed by the proper two-vertex `(-2)` subgraph classification. -/
def IsGenusOneEdgeFactor (p q : ℤ) : Prop :=
  (p = 1 ∧ q = 1) ∨ (p = 2 ∧ q = 1) ∨ (p = 1 ∧ q = 2) ∨
    (p = 3 ∧ q = 1) ∨ (p = 1 ∧ q = 3)

/-- The five possible endpoint-factor pairs in explicit form. -/
theorem isGenusOneEdgeFactor_iff {p q : ℤ} :
    IsGenusOneEdgeFactor p q ↔
      (p = 1 ∧ q = 1) ∨ (p = 2 ∧ q = 1) ∨ (p = 1 ∧ q = 2) ∨
        (p = 3 ∧ q = 1) ∨ (p = 1 ∧ q = 3) :=
  Iff.rfl

/-- A positive intersection between two components of self-intersection `-2w` has one of the five
endpoint-factor pairs used in the genus-one classification. -/
theorem exists_genusOneEdgeFactors (hcard : 2 < Fintype.card T.Component)
    {i j : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hij : 0 < T.intersection i j) :
    ∃ p q : ℤ, IsGenusOneEdgeFactor p q ∧
      T.intersection i j = T.weight i * p ∧ T.intersection i j = T.weight j * q := by
  obtain ⟨w, hmem⟩ := T.exists_weight_intersection_triple_mem hcard hi hj hij
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  rcases hmem with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ |
      ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
  · exact ⟨1, 1, by simp [IsGenusOneEdgeFactor], by omega, by omega⟩
  · exact ⟨2, 1, by simp [IsGenusOneEdgeFactor], by omega, by omega⟩
  · exact ⟨1, 2, by simp [IsGenusOneEdgeFactor], by omega, by omega⟩
  · exact ⟨3, 1, by simp [IsGenusOneEdgeFactor], by omega, by omega⟩
  · exact ⟨1, 3, by simp [IsGenusOneEdgeFactor], by omega, by omega⟩

end TauCeti.NumericalType
