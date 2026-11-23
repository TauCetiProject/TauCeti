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

When `ι` has cardinality equal to `finrank ℝ F`, the orientation cover has exactly two points over
every base point, so its projection is proper: a nonempty `ι` forces `F` to have positive finite
rank, while an empty `ι` gives the two orientations `±positiveOrientation` without assuming
`FiniteDimensional ℝ F`. Under this hypothesis, orientation covers of bundles over compact bases
are compact.

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
  {ι : Type*} [Fintype ι]

/-- The fibre through an orientation consists of that orientation and its opposite. -/
theorem preimage_proj_singleton (hι : Fintype.card ι = finrank ℝ F)
    (p : VectorBundleOrientationCover F E ι) :
    proj ⁻¹' {p.proj} = {p, deck p} := by
  ext q
  simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
  exact ⟨eq_or_eq_deck hι, fun h ↦ h.elim (fun h ↦ h ▸ rfl)
    (fun h ↦ h ▸ proj_deck p)⟩

/-- Every fibre of the orientation cover has exactly two points when `Fintype.card ι = finrank ℝ F`,
without assuming `FiniteDimensional ℝ F` (an empty `ι` has the two orientations
`±positiveOrientation`, and a nonempty `ι` forces positive finite rank). -/
@[simp]
theorem encard_preimage_proj_singleton (hι : Fintype.card ι = finrank ℝ F) (b : B) :
    (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)).encard = 2 := by
  have ⟨p, hp⟩ : ∃ p : VectorBundleOrientationCover F E ι, p.proj = b := by
    rcases isEmpty_or_nonempty ι with _ | _
    · exact ⟨⟨b, ((trivializationAt F E b).mapOrientation ι
        (FiberBundle.mem_baseSet_trivializationAt' b)).symm positiveOrientation⟩, rfl⟩
    · have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (hι ▸ Fintype.card_pos)
      exact surjective_proj (E := E) hι b
  rw [← hp, preimage_proj_singleton hι p]
  exact encard_pair (deck_ne_self p).symm

/-- The orientation-cover projection is proper when `Fintype.card ι = finrank ℝ F`, since it is a
covering with finite fibres. -/
theorem isProperMap_proj (hι : Fintype.card ι = finrank ℝ F) :
    IsProperMap (proj : VectorBundleOrientationCover F E ι → B) := by
  refine (isCoveringMap_proj hι).isProperMap fun b ↦ ?_
  exact (finite_of_encard_eq_coe (encard_preimage_proj_singleton hι b)).to_subtype

/-- When `Fintype.card ι = finrank ℝ F`, the orientation cover of a bundle over a compact base is
compact. -/
theorem compactSpace [CompactSpace B] (hι : Fintype.card ι = finrank ℝ F) :
    CompactSpace (VectorBundleOrientationCover F E ι) :=
  isCompact_univ_iff.mp (by
    simpa using (isProperMap_proj (E := E) hι).isCompact_preimage isCompact_univ)

end TauCeti.VectorBundleOrientationCover
