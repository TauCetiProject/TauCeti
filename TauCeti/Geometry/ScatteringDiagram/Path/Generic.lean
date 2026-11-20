/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Normed.Affine.Generic
public import TauCeti.Geometry.ScatteringDiagram.SingularSupport

/-!
# Two transverse segments between allowed wall endpoints

For a countable family of codimension-one polyhedra, endpoints off all walls can
be joined through a freely chosen vertex by two segments transverse to every
wall and avoiding the actual singular support. The vertex lies off every wall
and may be chosen in any nonempty open set. In fact both full affine lines
avoid the singular support. The segments are not required to remain in the
prescribed open set.

Adapted from `Mei/Geometry/Convex/Polyhedron/GenericPath.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

open Set AffineSubspace

namespace TauCeti

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Between endpoints outside a countable family of walls, an intermediate vertex can be chosen
in any nonempty open set so that it avoids all walls, both segment directions
are transverse to every wall, and both full affine lines avoid actual singular support.

The endpoints need not avoid the affine subspaces covering singular support. -/
theorem exists_mem_open_two_transverse_lineMaps [Countable ι]
    (W : ι → Set V) (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    {x y : V} (hx : ∀ i, x ∉ W i) (hy : ∀ i, y ∉ W i)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, (∀ i, z ∉ W i) ∧
      (∀ i, z - x ∉ (affineSpan ℝ (W i)).direction ∧
        z - y ∉ (affineSpan ℝ (W i)).direction) ∧
      ∀ t : ℝ, AffineMap.lineMap x z t ∉ singularSupport W ∧
        AffineMap.lineMap y z t ∉ singularSupport W := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain ⟨z, hz⟩ := hne
    exact ⟨z, hz, by simp, by simp, by simp [mem_singularSupport]⟩
  let : FiniteDimensional ℝ V := .of_finrank_pos (by
    have := hdim (Classical.arbitrary ι)
    omega)
  obtain ⟨S, hcount, hcover, hS⟩ := exists_countable_singularSupport_cover W hpoly hdim
  let : Countable S := hcount.to_subtype
  let A : ι ⊕ (ι ⊕ ι) → AffineSubspace ℝ V := Sum.elim
    (fun i => affineSpan ℝ (W i))
    (Sum.elim (fun i => mk' x ((affineSpan ℝ (W i)).direction))
      (fun i => mk' y ((affineSpan ℝ (W i)).direction)))
  have hA : ∀ i, A i ≠ ⊤ := by
    intro i
    rcases i with i | i | i
    · exact (affineSpan ℝ (W i)).ne_top_of_finrank_direction_add_one_eq (hdim i)
    · apply (mk' x ((affineSpan ℝ (W i)).direction)).ne_top_of_finrank_direction_add_one_eq
      rw [AffineSubspace.direction_mk']
      exact hdim i
    · apply (mk' y ((affineSpan ℝ (W i)).direction)).ne_top_of_finrank_direction_add_one_eq
      rw [AffineSubspace.direction_mk']
      exact hdim i
  have hcover' : singularSupport W ⊆ ⋃ k : S, (k.val : Set V) := by
    intro p hp
    obtain ⟨B, hB, hpB⟩ := Set.mem_iUnion₂.mp (hcover hp)
    exact Set.mem_iUnion.mpr ⟨⟨B, hB⟩, hpB⟩
  have hxE : x ∉ singularSupport W := fun hp => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (singularSupport_subset_iUnion W (fun i => (hpoly i).isClosed) hp)
    exact hx i hi
  have hyE : y ∉ singularSupport W := fun hp => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (singularSupport_subset_iUnion W (fun i => (hpoly i).isClosed) hp)
    exact hy i hi
  obtain ⟨z, hzU, hzA, hzE⟩ := AffineSubspace.exists_mem_open_two_lineMaps_avoid_set
    (fun k : S => k.val) (fun k => hS k.val k.property) A hA hcover' hxE hyE hU hne
  refine ⟨z, hzU, ?_, ?_, hzE⟩
  · intro i hzi
    exact hzA (.inl i) (subset_affineSpan ℝ (W i) hzi)
  · intro i
    exact ⟨by simpa only [A, Sum.elim_inr, Sum.elim_inl, mem_mk', vsub_eq_sub]
        using hzA (.inr (.inl i)),
      by simpa only [A, Sum.elim_inr, mem_mk', vsub_eq_sub]
        using hzA (.inr (.inr i))⟩

end TauCeti
