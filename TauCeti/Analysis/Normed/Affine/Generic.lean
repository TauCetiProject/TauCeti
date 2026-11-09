/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.AffineSpace.Codimension
public import TauCeti.LinearAlgebra.AffineSpace.Transverse
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Points avoiding countably many affine subspaces

The common complement of countably many proper affine subspaces of a finite-dimensional real
normed space is a dense `Gδ` set, and it is open for finitely many subspaces. Hence a point
avoiding all the subspaces can be found in any nonempty open set, in particular arbitrarily
close to any given point.

For obstacles of codimension at least two, a freely chosen intermediate vertex avoids all the
affine spans of an obstacle with either of two fixed endpoints. Both full lines from the
endpoints to the vertex, and hence both segments, then avoid every obstacle. Only the vertex is
varied: both endpoints stay fixed, and they need only avoid the union of the obstacles.

## Main results

* `AffineSubspace.dense_setOf_forall_notMem`, `AffineSubspace.isGδ_setOf_forall_notMem` and
  `AffineSubspace.isOpen_setOf_forall_notMem`: the topology of the common complement.
* `AffineSubspace.exists_mem_open_forall_notMem`: a point of any nonempty open set avoiding all
  the subspaces.
* `AffineSubspace.exists_mem_open_lineMap_notMem`: a vertex for two segments from fixed
  endpoints that avoid every obstacle of codimension at least two.

## Attribution

Adapted from `Mei/Geometry/Affine/Generic.lean` in Mei at commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca/Mei/Geometry/Affine/Generic.lean
-/

public section

namespace AffineSubspace

section Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A proper real affine subspace has empty interior, even without a
finite-dimensionality assumption. -/
theorem interior_eq_empty_of_ne_top (S : AffineSubspace ℝ V) (hS : S ≠ ⊤) :
    interior (S : Set V) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hspan := isOpen_interior.affineSpan_eq_top ⟨x, hx⟩
  have hle : affineSpan ℝ (interior (S : Set V)) ≤ S :=
    affineSpan_le.mpr interior_subset
  exact hS (top_le_iff.mp (hspan ▸ hle))

/-- The complement of a proper real affine subspace is dense. -/
theorem dense_compl_of_ne_top (S : AffineSubspace ℝ V) (hS : S ≠ ⊤) :
    Dense (S : Set V)ᶜ :=
  interior_eq_empty_iff_dense_compl.mp (S.interior_eq_empty_of_ne_top hS)

variable [FiniteDimensional ℝ V]

/-- Countably many proper affine subspaces have dense common complement. -/
theorem dense_setOf_forall_notMem {ι : Sort*} [Countable ι] (A : ι → AffineSubspace ℝ V)
    (hA : ∀ i, A i ≠ ⊤) : Dense {x | ∀ i, x ∉ A i} := by
  simp only [Set.ofPred_forall]
  exact dense_iInter_of_isOpen
    (fun i => (A i).closed_of_finiteDimensional.isOpen_compl)
    (fun i => (A i).dense_compl_of_ne_top (hA i))

/-- The common complement of countably many affine subspaces is a countable intersection of
open sets. -/
theorem isGδ_setOf_forall_notMem {ι : Sort*} [Countable ι] (A : ι → AffineSubspace ℝ V) :
    IsGδ {x | ∀ i, x ∉ A i} := by
  simp only [Set.ofPred_forall]
  exact IsGδ.iInter_of_isOpen (fun i => (A i).closed_of_finiteDimensional.isOpen_compl)

/-- The common complement of finitely many affine subspaces is open. -/
theorem isOpen_setOf_forall_notMem {ι : Sort*} [Finite ι] (A : ι → AffineSubspace ℝ V) :
    IsOpen {x | ∀ i, x ∉ A i} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite (fun i => (A i).closed_of_finiteDimensional.isOpen_compl)

/-- Every nonempty open set contains a point outside countably many proper affine subspaces. -/
theorem exists_mem_open_forall_notMem {ι : Sort*} [Countable ι]
    (A : ι → AffineSubspace ℝ V) (hA : ∀ i, A i ≠ ⊤)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ i, x ∉ A i := by
  obtain ⟨x, hxU, hxA⟩ := (dense_setOf_forall_notMem A hA).inter_open_nonempty U hU hne
  exact ⟨x, hxU, hxA⟩

/-- Points outside countably many proper affine subspaces exist arbitrarily close to any
given point. -/
theorem exists_dist_lt_forall_notMem {ι : Sort*} [Countable ι]
    (A : ι → AffineSubspace ℝ V) (hA : ∀ i, A i ≠ ⊤)
    (x : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ y, dist y x < ε ∧ ∀ i, y ∉ A i :=
  exists_mem_open_forall_notMem A hA Metric.isOpen_ball (Metric.nonempty_ball.mpr hε)

/-- A set covered by countably many affine subspaces of codimension at least two can be avoided
by both full lines from two fixed endpoints to a vertex chosen in any nonempty open set. The
vertex may simultaneously avoid any further countable family of proper affine subspaces.

The endpoints need only avoid the set `E` itself, not its affine cover; the prescribed open set
constrains the vertex, not the lines. -/
theorem exists_mem_open_lineMap_notMem {ι κ : Type*} [Countable ι] [Countable κ]
    (S : κ → AffineSubspace ℝ V)
    (hS : ∀ k, Module.finrank ℝ (S k).direction + 1 < Module.finrank ℝ V)
    (A : ι → AffineSubspace ℝ V) (hA : ∀ i, A i ≠ ⊤)
    {E : Set V} (hE : E ⊆ ⋃ k, (S k : Set V))
    {x y : V} (hx : x ∉ E) (hy : y ∉ E)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, (∀ i, z ∉ A i) ∧ ∀ t : ℝ,
      AffineMap.lineMap x z t ∉ E ∧ AffineMap.lineMap y z t ∉ E := by
  let B : (κ ⊕ κ) ⊕ ι → AffineSubspace ℝ V := Sum.elim
    (Sum.elim (fun k => affineSpan ℝ (insert x (S k : Set V)))
      (fun k => affineSpan ℝ (insert y (S k : Set V)))) A
  have hB : ∀ i, B i ≠ ⊤ := by
    rintro ((k | k) | i)
    · exact (S k).affineSpan_insert_ne_top_of_finrank_direction_add_one_lt (hS k) x
    · exact (S k).affineSpan_insert_ne_top_of_finrank_direction_add_one_lt (hS k) y
    · exact hA i
  obtain ⟨z, hzU, hz⟩ := exists_mem_open_forall_notMem B hB hU hne
  have havoid (p : V) (hp : p ∉ E) (hzp : ∀ k, z ∉ affineSpan ℝ (insert p (S k : Set V)))
      (t : ℝ) : AffineMap.lineMap p z t ∉ E := by
    by_cases ht : t = 0
    · simpa [ht] using hp
    · intro htE
      obtain ⟨k, htk⟩ := Set.mem_iUnion.mp (hE htE)
      exact (S k).lineMap_notMem_of_notMem_affineSpan_insert_of_ne_zero (hzp k) ht htk
  exact ⟨z, hzU, fun i => hz (.inr i), fun t =>
    ⟨havoid x hx (fun k => hz (.inl (.inl k))) t,
      havoid y hy (fun k => hz (.inl (.inr k))) t⟩⟩

end Topology

end AffineSubspace
