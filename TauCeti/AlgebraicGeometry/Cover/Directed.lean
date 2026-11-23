/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# The locally directed refinement of an open cover

Every open cover `𝒰` of a scheme `S` is refined by the open cover of `S` by the opens contained in
the image of a member of `𝒰`. These opens form a basis of the topology of `S`, so ordering them by
inclusion makes this refinement locally directed in the sense of
`AlgebraicGeometry.Scheme.Cover.LocallyDirected`, with a thin index category. Constructions that
need a locally directed cover, such as gluing along
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`, thereby apply over an arbitrary open cover.

## Main declarations

* `AlgebraicGeometry.Scheme.OpenCover.directedRefinement`: the open cover of `S` by the opens
  contained in the image of a member of `𝒰`, ordered by inclusion and locally directed.
* `AlgebraicGeometry.Scheme.OpenCover.fromDirectedRefinement`: the refinement morphism to `𝒰`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.OpenCover

variable {S : Scheme.{u}} (𝒰 : S.OpenCover)

/-- The open cover of `S` by the opens contained in the image of a member of `𝒰`, indexed by these
opens. -/
@[expose, simps X f]
def directedRefinement : S.OpenCover where
  I₀ := {V : S.Opens // ∃ i, V ≤ (𝒰.f i).opensRange}
  X V := V.val
  f V := V.val.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨⟨(𝒰.f (𝒰.idx x)).opensRange, 𝒰.idx x, le_rfl⟩, ?_⟩, inferInstance⟩
    simpa using 𝒰.covers x

/-- The opens of the directed refinement are ordered by inclusion. -/
instance : Preorder 𝒰.directedRefinement.I₀ :=
  inferInstanceAs (Preorder {V : S.Opens // ∃ i, V ≤ (𝒰.f i).opensRange})

theorem directedRefinement_le_iff {V W : 𝒰.directedRefinement.I₀} : V ≤ W ↔ V.val ≤ W.val :=
  Iff.rfl

/-- The opens contained in the image of a member of `𝒰` form a basis of the topology of `S`, so
the directed refinement is locally directed by inclusion. -/
noncomputable instance : 𝒰.directedRefinement.LocallyDirected :=
  .ofIsBasisOpensRange (fun {V W} ↦ by
      simp only [directedRefinement, Scheme.Opens.opensRange_ι]
      exact Iff.rfl) <| by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro U x hx
    refine ⟨_, ⟨⟨U ⊓ (𝒰.f (𝒰.idx x)).opensRange, 𝒰.idx x, inf_le_right⟩, rfl⟩, ?_, ?_⟩
    all_goals simp only [directedRefinement, Scheme.Opens.opensRange_ι]
    exacts [⟨hx, 𝒰.covers x⟩, inf_le_left]

/-- Every open of the directed refinement lies over a member of `𝒰`: the directed refinement
refines `𝒰`. -/
noncomputable def fromDirectedRefinement :
    𝒰.directedRefinement.toPreZeroHypercover.Hom 𝒰.toPreZeroHypercover where
  s₀ V := V.property.choose
  h₀ V := IsOpenImmersion.lift (𝒰.f V.property.choose) V.val.ι (by
    have h : (V.val : Set S) ⊆ (𝒰.f V.property.choose).opensRange := V.property.choose_spec
    rwa [← Scheme.Opens.range_ι V.val] at h)
  w₀ _ := IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.Scheme.OpenCover
