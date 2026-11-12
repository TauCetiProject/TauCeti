/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.Topology.Covering.Proper
public import Mathlib.Data.Set.Card

/-!
# Properness of the orientation cover

When `ι` has cardinality equal to the rank of the finite-dimensional model fibre, the
orientation cover has exactly two points over every base point, so its projection is proper.
Under this hypothesis, orientation covers of bundles over compact bases are compact.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §9.
-/

public section

open Bundle Set Module

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type*} [Fintype ι] [FiniteDimensional ℝ F]

/-- The fibre through an orientation consists of that orientation and its opposite. -/
theorem preimage_proj_singleton (hι : Fintype.card ι = finrank ℝ F)
    (p : VectorBundleOrientationCover F E ι) :
    proj ⁻¹' {p.proj} = {p, deck p} := by
  ext q
  simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
  exact ⟨eq_or_eq_deck hι, fun h ↦ h.elim (fun h ↦ h ▸ rfl)
    (fun h ↦ h ▸ proj_deck p)⟩

/-- Every fibre of the orientation cover has exactly two points, including in rank zero. -/
@[simp]
theorem encard_preimage_proj_singleton (hι : Fintype.card ι = finrank ℝ F) (b : B) :
    (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)).encard = 2 := by
  obtain ⟨p, rfl⟩ := surjective_proj (E := E) hι b
  rw [preimage_proj_singleton hι p]
  exact encard_pair (deck_ne_self p).symm

/-- The orientation-cover projection is proper, since it is a covering with finite fibres. -/
theorem isProperMap_proj (hι : Fintype.card ι = finrank ℝ F) :
    IsProperMap (proj : VectorBundleOrientationCover F E ι → B) := by
  refine (isCoveringMap_proj hι).isProperMap fun b ↦ ?_
  exact (finite_of_encard_eq_coe (encard_preimage_proj_singleton hι b)).to_subtype

/-- The orientation cover of a finite-rank bundle over a compact base is compact. -/
theorem compactSpace [CompactSpace B] (hι : Fintype.card ι = finrank ℝ F) :
    CompactSpace (VectorBundleOrientationCover F E ι) :=
  isCompact_univ_iff.mp (by
    simpa using (isProperMap_proj (E := E) hι).isCompact_preimage isCompact_univ)

end TauCeti.VectorBundleOrientationCover
