/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# Transition maps of the pulled-back directed affine cover

Let `q : T ⟶ X` be a morphism of schemes. Pulling back Mathlib's directed cover of `X` by its
affine opens (`AlgebraicGeometry.Scheme.AffineZariskiSite.directedCover`) along `q` gives a
locally directed cover of `T`, whose member over an affine open `U` is identified with the inverse
image `q⁻¹ U` by `AlgebraicGeometry.pullbackRestrictIsoRestrict`. This file records that, under
these identifications, the transition maps of the pulled-back cover are the inclusions of inverse
images. This is the compatibility needed to glue morphisms out of `T` along this cover with
`AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOfLocallyDirected`.

## Main results

* `Scheme.AffineZariskiSite.directedCover_pullback₁_trans_pullbackRestrictIsoRestrict_hom`: the
  transition map of `(directedCover X).pullback₁ q` along `U ⟶ V` is the inclusion
  `q⁻¹ U ⟶ q⁻¹ V`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open Scheme.AffineZariskiSite

universe u

namespace TauCeti.AlgebraicGeometry.Scheme.AffineZariskiSite

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
