/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Stratification.Basic

/-!
# Closed charts subordinate to finite semilinear covers

A finite rational semilinear cover of a semilinear domain admits a disjoint
partition by relative interiors of closed rational-normal polyhedra. Every
interior lies in a chosen cover member, and membership in every other cover
member is constant there. Each patch is recovered by selecting the interiors
it contains, even when the original cover overlaps. Closing a chart adds only
limits from the domain inside its chosen patch.

The construction restricts the common sign-cell stratification of the domain
and the cover. It retains boundary strata and arbitrary real offsets.

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/Stratification/Cover.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

open Set

namespace TauCeti

variable {N V ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Finite ι]

/-- Finite overlapping semilinear covers admit closed polyhedral charts with
pairwise disjoint relative interiors subordinate to the cover. The same charts
recover every patch intersection,
so passing to another patch retains all strata already present on the overlap. -/
theorem IsRationalSemilinear.exists_cover_polyhedralCharts
    {S : Set V} (hS : IsRationalSemilinear h S)
    (U : ι → Set V) (hU : ∀ a, IsRationalSemilinear h (U a))
    (hcover : S ⊆ ⋃ a, U a) :
    ∃ (κ : Type) (_ : Finite κ) (B : κ → Set V) (patch : κ → ι),
      (∀ j, (B j).Nonempty ∧ IsRationalNormalPolyhedron h (B j) ∧
        (intrinsicInterior ℝ (B j)).Nonempty ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (B j)) ∧
        intrinsicInterior ℝ (B j) ⊆ S ∩ U (patch j) ∧
        B j ⊆ closure (S ∩ U (patch j))) ∧
      (Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B j))
        (intrinsicInterior ℝ (B l))) ∧
      (⋃ j, intrinsicInterior ℝ (B j)) = S ∧
      (∀ j a, intrinsicInterior ℝ (B j) ⊆ U a ∨
        Disjoint (intrinsicInterior ℝ (B j)) (U a)) ∧
      ∀ a, ⋃ (j) (_ : intrinsicInterior ℝ (B j) ⊆ U a),
        intrinsicInterior ℝ (B j) = S ∩ U a := by
  classical
  let := h.finiteDimensional
  let domains : Option ι → Set V := fun a => a.elim S U
  have hdomains : ∀ a, IsRationalSemilinear h (domains a) := by
    intro a
    cases a with
    | none => exact hS
    | some a => exact hU a
  obtain ⟨ν, hν, C, hC, hdisj, hCcover, hmem⟩ :=
    IsRationalSemilinear.exists_common_intrinsicInteriors hdomains
  let x (j : ν) := (hC j).2.2.1.choose
  have hx (j : ν) : x j ∈ intrinsicInterior ℝ (C j) := (hC j).2.2.1.choose_spec
  let κ := {j : ν // x j ∈ S}
  have hsub (j : κ) : intrinsicInterior ℝ (C j.val) ⊆ S := by
    intro y hy
    exact (hmem j.val (x j.val) (hx _) y hy none).mp j.property
  have hpatch (j : κ) : ∃ a, x j.val ∈ U a := mem_iUnion.mp (hcover j.property)
  choose patch hpatch using hpatch
  have hsubpatch (j : κ) : intrinsicInterior ℝ (C j.val) ⊆ S ∩ U (patch j) := by
    intro y hy
    exact ⟨hsub j hy, (hmem j.val (x j.val) (hx _) y hy (some (patch j))).mp
      (hpatch j)⟩
  refine ⟨κ, inferInstance, fun j => C j.val, patch, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    refine ⟨(hC j.val).1, (hC j.val).2.1, (hC j.val).2.2.1,
      (hC j.val).2.2.2, hsubpatch j, ?_⟩
    intro y hy
    apply closure_mono (hsubpatch j)
    exact closure_mono
      ((hC j.val).2.1.convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
        (hx j.val) (subset_intrinsicClosure hy))
      (segment_subset_closure_openSegment (right_mem_segment ℝ (x j.val) y))
  · intro j l hjl
    exact hdisj (Subtype.coe_injective.ne hjl)
  · apply Subset.antisymm
    · exact iUnion_subset hsub
    · intro y hy
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hCcover.symm ▸ mem_univ y)
      have hjS : x j ∈ S := (hmem j y hj (x j) (hx j) none).mp hy
      exact mem_iUnion.mpr ⟨⟨j, hjS⟩, hj⟩
  · intro j a
    by_cases ha : x j.val ∈ U a
    · exact Or.inl fun y hy => (hmem j.val (x j.val) (hx _) y hy (some a)).mp ha
    · exact Or.inr (disjoint_left.mpr fun y hy hya =>
        ha ((hmem j.val y hy (x j.val) (hx _) (some a)).mp hya))
  · intro a
    apply Subset.antisymm
    · exact iUnion₂_subset fun j hj => subset_inter (hsub j) hj
    · intro y hy
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hCcover.symm ▸ mem_univ y)
      have hjS : x j ∈ S := (hmem j y hj (x j) (hx j) none).mp hy.1
      refine mem_iUnion₂.mpr ⟨⟨j, hjS⟩, ?_, hj⟩
      intro z hz
      exact (hmem j y hj z hz (some a)).mp hy.2

end TauCeti
