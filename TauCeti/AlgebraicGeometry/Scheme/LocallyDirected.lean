/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Opens of locally directed colimits of schemes

Let `F : J ⥤ Scheme` be a locally directed diagram of open immersions indexed by a small thin
category, so that its colimit is the scheme glued from the `F j` along the images of the
transition maps (`AlgebraicGeometry.Scheme.IsLocallyDirected.openCover`). This file describes how
the images of the `F j` in the colimit meet.

## Main results

* `AlgebraicGeometry.Scheme.IsLocallyDirected.preimage_opensRange_ι_le`: the part of `F j` lying
  over the image of `F i` is contained in the image of `F f`, for any `f : i ⟶ j`.
* `AlgebraicGeometry.Scheme.IsLocallyDirected.preimage_le_iSup_preimage_inf_opensRange`: the
  preimage in `F j` of an open contained in the image of `F i` is covered by its intersections with
  the images of the `F k` mapping to both `F i` and `F j`.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IsLocallyDirected

universe u

variable {J : Type u} [SmallCategory J] (F : J ⥤ Scheme.{u})
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected]
  [Quiver.IsThin J]

/-- In the colimit of a thin locally directed diagram of open immersions, the part of `F j` lying
over the image of `F i` is contained in the image of `F f`, for any `f : i ⟶ j`. -/
theorem preimage_opensRange_ι_le {i j : J}
    (f : i ⟶ j) : colimit.ι F j ⁻¹ᵁ (colimit.ι F i).opensRange ≤ (F.map f).opensRange := by
  rintro y ⟨x, hx⟩
  obtain ⟨k, fi, fj, z, rfl, rfl⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp hx
  exact ⟨F.map fi z, by rw [← Scheme.Hom.comp_apply, ← F.map_comp, Subsingleton.elim (fi ≫ f) fj]⟩

/-- In the colimit of a thin locally directed diagram of open immersions, the opens
`U ⊓ ιₖ(F k)`, for `k` mapping to both `i` and `j`, cover the preimage in `F j` of an open `U`
contained in the image of `F i`. -/
theorem preimage_le_iSup_preimage_inf_opensRange
    {i j : J} {U : (colimit F).Opens} (hU : U ≤ (colimit.ι F i).opensRange) :
    colimit.ι F j ⁻¹ᵁ U ≤
      ⨆ k : Σ k : J, (k ⟶ j) × (k ⟶ i), colimit.ι F j ⁻¹ᵁ (U ⊓ (colimit.ι F k.1).opensRange) := by
  intro y hy
  obtain ⟨x, hx⟩ := hU hy
  obtain ⟨k, fi, fj, z, rfl, rfl⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp hx
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨k, fj, fi⟩, hy, z, ?_⟩
  rw [← Scheme.Hom.comp_apply, colimit.w]

end AlgebraicGeometry.Scheme.IsLocallyDirected
