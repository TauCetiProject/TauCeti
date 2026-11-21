/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# The small affine Zariski site as an open cover

This file records that the affine opens of a scheme `X`, indexed by its small affine Zariski site
`X.AffineZariskiSite`, form an open cover of `X`, together with the transition maps of the
pulled-back directed affine cover. For a morphism `g : X ⟶ Y` it also constructs the cover of `X`
by the affine opens lying over affine opens of `Y`.

## Transition maps of the pulled-back directed affine cover

Let `q : T ⟶ X` be a morphism of schemes. Pulling back Mathlib's directed cover of `X` by its
affine opens (`AlgebraicGeometry.Scheme.AffineZariskiSite.directedCover`) along `q` gives a
locally directed cover of `T`, whose member over an affine open `U` is identified with the inverse
image `q⁻¹ U` by `AlgebraicGeometry.pullbackRestrictIsoRestrict`. This file records that, under
these identifications, the transition maps of the pulled-back cover are the inclusions of inverse
images. This is the compatibility needed to glue morphisms out of `T` along this cover with
`AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOfLocallyDirected`.

## Main results

* `Scheme.AffineZariskiSite.isOpenCover_toOpens`: the affine opens of `X`, indexed by the small
  affine Zariski site, form an open cover of `X`.
* `Scheme.AffineZariskiSite.affinePairCover`: for a morphism `g : X ⟶ Y`, the open cover of `X` by
  the spectra of the affine opens `V` of `X` lying over an affine open `U` of `Y`, indexed by the
  pairs `(V, U)` with `V ≤ g⁻¹ U`.
* `Scheme.AffineZariskiSite.directedCover_pullback₁_trans_pullbackRestrictIsoRestrict_hom`: the
  transition map of `(directedCover X).pullback₁ q` along `U ⟶ V` is the inclusion
  `q⁻¹ U ⟶ q⁻¹ V`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open Scheme.AffineZariskiSite

universe u

namespace AlgebraicGeometry.Scheme.AffineZariskiSite

/-- The affine opens of `X` cover `X`, indexed by the small affine Zariski site. -/
theorem isOpenCover_toOpens (X : Scheme.{u}) :
    TopologicalSpace.IsOpenCover fun U : X.AffineZariskiSite ↦ U.toOpens := by
  refine .mk (top_le_iff.1 fun x _ ↦ ?_)
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U.val, U.property⟩, hxU⟩

end AlgebraicGeometry.Scheme.AffineZariskiSite

namespace TauCeti.AlgebraicGeometry.Scheme.AffineZariskiSite

section AffinePair

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The affine opens `V` of `X` lying over an affine open `U` of `Y`, in the sense that
`V ≤ g⁻¹ U`, cover `X`; the cover is indexed by such pairs `(V, U)`. -/
theorem isOpenCover_affinePair :
    TopologicalSpace.IsOpenCover fun p : {p : X.AffineZariskiSite × Y.AffineZariskiSite //
      p.1.toOpens ≤ g ⁻¹ᵁ p.2.toOpens} ↦ p.val.1.toOpens := by
  refine .mk (top_le_iff.1 fun x _ ↦ ?_)
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := g x) (U := ⊤) trivial
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (g.mem_preimage.mpr hxU)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, ⟨U, hU⟩), hVU⟩, hxV⟩

/-- The open cover of `X` by the spectra `Spec Γ(X, V)` of the affine opens `V` of `X` lying over
an affine open `U` of `Y`, indexed by the pairs `(V, U)` with `V ≤ g⁻¹ U`. -/
@[expose]
noncomputable def affinePairCover : X.OpenCover :=
  (_root_.AlgebraicGeometry.Scheme.AffineOpenCover.ofIsOpenCover _ (isOpenCover_affinePair g)
    fun p ↦ p.val.1.property).openCover

/-- The member of `affinePairCover g` over a pair `(V, U)` is `Spec Γ(X, V)`. -/
@[simp]
theorem affinePairCover_X
    (p : {p : X.AffineZariskiSite × Y.AffineZariskiSite // p.1.toOpens ≤ g ⁻¹ᵁ p.2.toOpens}) :
    (affinePairCover g).X p = Spec Γ(X, p.val.1.toOpens) :=
  rfl

/-- The member of `affinePairCover g` over a pair `(V, U)` maps to `X` by the canonical open
immersion `Spec Γ(X, V) ⟶ X`. -/
@[simp]
theorem affinePairCover_f
    (p : {p : X.AffineZariskiSite × Y.AffineZariskiSite // p.1.toOpens ≤ g ⁻¹ᵁ p.2.toOpens}) :
    (affinePairCover g).f p = p.val.1.property.fromSpec :=
  rfl

end AffinePair

variable {X T : Scheme.{u}} (q : T ⟶ X)

/-- Under the identification of the members of the pulled-back directed affine cover with inverse
images of affine opens, its transition map along `U ⟶ V` is the inclusion `q⁻¹ U ⟶ q⁻¹ V`. -/
@[reassoc]
theorem directedCover_pullback₁_trans_pullbackRestrictIsoRestrict_hom
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Scheme.Cover.trans ((directedCover X).pullback₁ q) i ≫
        (pullbackRestrictIsoRestrict q V.toOpens).hom =
      (pullbackRestrictIsoRestrict q U.toOpens).hom ≫
        T.homOfLE (q.preimage_mono (toOpens_mono i.le)) := by
  have hUV : U.toOpens ≤ V.toOpens := toOpens_mono i.le
  -- The transition maps of the pulled-back cover are indexed by its own index type; `change`
  -- presents the transition as the underlying map of pullbacks so that rewriting is type-correct.
  change pullback.map q U.toOpens.ι q V.toOpens.ι (𝟙 _) (X.homOfLE hUV) (𝟙 _)
      (by simp) (by rw [Category.comp_id]; exact (Scheme.homOfLE_ι _ _).symm) ≫ _ = _
  rw [← cancel_mono (q ⁻¹ᵁ V.toOpens).ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι T,
    pullbackRestrictIsoRestrict_hom_ι, pullbackRestrictIsoRestrict_hom_ι]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end TauCeti.AlgebraicGeometry.Scheme.AffineZariskiSite
