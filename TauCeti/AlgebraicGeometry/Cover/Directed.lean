/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Locally directed open covers

Every open cover `𝒰` of a scheme `S` is refined by the open cover of `S` by the opens contained in
the image of a member of `𝒰`. These opens form a basis of the topology of `S`, so ordering them by
inclusion makes this refinement locally directed in the sense of
`AlgebraicGeometry.Scheme.Cover.LocallyDirected`, with a thin index category. Constructions that
need a locally directed cover, such as gluing along
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`, thereby apply over an arbitrary open cover.

The affine opens of `S` form such a locally directed cover, `S.directedAffineCover`. Pulling it
back along a scheme `X` over `S` and lifting Mathlib's colimit of a locally directed open cover,
`AlgebraicGeometry.Scheme.OpenCover.isColimitCoconeOfLocallyDirected`, to `Over S` shows that `X`
is the colimit, in `Over S`, of its restrictions `X ×_S U` to the affine opens `U` of `S`.

## Main declarations

* `AlgebraicGeometry.Scheme.OpenCover.directedRefinement`: the open cover of `S` by the opens
  contained in the image of a member of `𝒰`, ordered by inclusion and locally directed.
* `AlgebraicGeometry.Scheme.OpenCover.fromDirectedRefinement`: the refinement morphism to `𝒰`.
* `AlgebraicGeometry.Scheme.colimitPresentationAffineOpens`: a scheme over `S` is the colimit of
  its restrictions to the affine opens of `S`.
-/

public section

open CategoryTheory Limits

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

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) (X : Over S)

/-- A scheme `X` over `S` is the colimit, in `Over S`, of its restrictions `X ×_S U` to the affine
opens `U` of `S`, ordered by inclusion, with the projections `X ×_S U ⟶ X`. -/
@[expose] noncomputable def colimitPresentationAffineOpens : ColimitPresentation S.affineOpens X :=
  let 𝒱 : X.left.OpenCover := S.directedAffineCover.pullback₁ X.hom
  { diag := _
    ι := (Over.liftCocone 𝒱.coconeOfLocallyDirected X.hom).ι
    isColimit := Over.isColimitLiftCocone _ X.hom
      (Scheme.OpenCover.isColimitCoconeOfLocallyDirected 𝒱) }

/-- The restriction of `X` to the affine open `U` is `X ×_S U`, lying over `S` through `X`. -/
@[simp]
theorem colimitPresentationAffineOpens_diag_obj (U : S.affineOpens) :
    (S.colimitPresentationAffineOpens X).diag.obj U =
      Over.mk (pullback.fst X.hom U.val.ι ≫ X.hom) :=
  rfl

/-- The transition maps of the presentation are the base changes of the inclusions of affine
opens. -/
@[simp]
theorem colimitPresentationAffineOpens_diag_map_left {U V : S.affineOpens} (f : U ⟶ V) :
    ((S.colimitPresentationAffineOpens X).diag.map f).left =
      pullback.map X.hom U.val.ι X.hom V.val.ι (𝟙 _) (S.homOfLE (leOfHom f)) (𝟙 _)
        (by simp) (by simp) :=
  rfl

/-- The colimit injections of the presentation are the projections `X ×_S U ⟶ X`. -/
@[reassoc (attr := simp)]
theorem colimitPresentationAffineOpens_ι_app_left (U : S.affineOpens) :
    ((S.colimitPresentationAffineOpens X).ι.app U).left = pullback.fst X.hom U.val.ι :=
  rfl

end AlgebraicGeometry.Scheme
