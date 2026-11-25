/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import TauCeti.AlgebraicGeometry.AffineScheme.Basic

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
* `Scheme.Hom.affinePairCover`: for a morphism `g : X ⟶ Y`, the affine open cover
  of `X` by the spectra of the affine opens `V` of `X` lying over an affine open `U` of `Y`,
  indexed by the pairs `(V, U)` with `V ≤ g⁻¹ U`.
* `Scheme.Hom.exists_affinePair_le`: below two such pairs, every point of a common
  affine open lies in a smaller pair below both, in the order of the small affine Zariski sites.
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
  simpa only [directedCover_f, Scheme.Opens.opensRange_ι] using
    (directedCover X).isOpenCover_opensRange

end AlgebraicGeometry.Scheme.AffineZariskiSite

namespace AlgebraicGeometry.Scheme.Hom

section AffinePair

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The affine opens `V` of `X` lying over an affine open `U` of `Y`, in the sense that
`V ≤ g⁻¹ U`, cover `X`; the cover is indexed by such pairs `(V, U)`. -/
theorem isOpenCover_affinePair :
    TopologicalSpace.IsOpenCover fun p : {p : X.AffineZariskiSite × Y.AffineZariskiSite //
      p.1.toOpens ≤ g ⁻¹ᵁ p.2.toOpens} ↦ p.val.1.toOpens :=
  .mk <| (iSup_range' (fun V ↦ V) _).symm.trans
    g.isBasis_range_affineOpens_le_preimage.isOpenCover

/-- The affine open cover of `X` by the spectra `Spec Γ(X, V)` of the affine opens `V` of `X`
lying over an affine open `U` of `Y`, indexed by the pairs `(V, U)` with `V ≤ g⁻¹ U`. -/
@[expose]
noncomputable def affinePairCover : X.AffineOpenCover :=
  _root_.AlgebraicGeometry.Scheme.AffineOpenCover.ofIsOpenCover _ (isOpenCover_affinePair g)
    fun p ↦ p.val.1.property

/-- The member of `affinePairCover g` over a pair `(V, U)` is the spectrum of `Γ(X, V)`. -/
@[simp]
theorem affinePairCover_X
    (p : {p : X.AffineZariskiSite × Y.AffineZariskiSite // p.1.toOpens ≤ g ⁻¹ᵁ p.2.toOpens}) :
    (affinePairCover g).X p = Γ(X, p.val.1.toOpens) :=
  rfl

/-- The member of `affinePairCover g` over a pair `(V, U)` maps to `X` by the canonical open
immersion `Spec Γ(X, V) ⟶ X`. -/
@[simp]
theorem affinePairCover_f
    (p : {p : X.AffineZariskiSite × Y.AffineZariskiSite // p.1.toOpens ≤ g ⁻¹ᵁ p.2.toOpens}) :
    (affinePairCover g).f p = p.val.1.property.fromSpec :=
  rfl

/-- **Refinement of affine pairs.** Let `i = (Vᵢ, Uᵢ)` and `j = (Vⱼ, Uⱼ)` be affine pairs, and `k`
an affine open of `X` below both `Vᵢ` and `Vⱼ` in the small affine Zariski site. Every point of `k`
lies in an affine pair `l` whose affine open of `X` is below `k`, and which is below both `i`
and `j`; here `l` consists of basic opens of `k` and of `Uᵢ`. -/
theorem exists_affinePair_le
    {i j : {p : X.AffineZariskiSite × Y.AffineZariskiSite // p.1.toOpens ≤ g ⁻¹ᵁ p.2.toOpens}}
    {k : X.AffineZariskiSite} (hki : k ≤ i.val.1) (hkj : k ≤ j.val.1) {x : X}
    (hx : x ∈ k.toOpens) :
    ∃ l : {p : X.AffineZariskiSite × Y.AffineZariskiSite // p.1.toOpens ≤ g ⁻¹ᵁ p.2.toOpens},
      x ∈ l.val.1.toOpens ∧ l.val.1 ≤ k ∧ l ≤ i ∧ l ≤ j := by
  obtain ⟨a, b, e, hxa⟩ := exists_basicOpen_le_affine_inter i.val.2.property j.val.2.property (g x)
    ⟨i.property (toOpens_mono hki hx), j.property (toOpens_mono hkj hx)⟩
  obtain ⟨h, hh, hxh⟩ := k.property.exists_basicOpen_le
    (V := g ⁻¹ᵁ (i.val.2.basicOpen a).toOpens) ⟨x, hxa⟩ hx
  exact ⟨⟨(k.basicOpen h, i.val.2.basicOpen a), hh⟩, hxh, k.basicOpen_le h,
    ⟨(k.basicOpen_le h).trans hki, i.val.2.basicOpen_le a⟩,
    ⟨(k.basicOpen_le h).trans hkj, b, e.symm⟩⟩

end AffinePair

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X T : Scheme.{u}} (q : T ⟶ X)

/-- Under the identification of the members of the pulled-back directed affine cover with inverse
images of affine opens, its transition map along `U ⟶ V` is the inclusion `q⁻¹ U ⟶ q⁻¹ V`.

Up to moving the isomorphism `pullbackRestrictIsoRestrict q U.toOpens` to the other side, this is
the transition fact proved inline, in a `have`, in Mathlib's
`AlgebraicGeometry.Scheme.Hom.toNormalization` (`Mathlib/AlgebraicGeometry/Normalization.lean`),
stated here as a named lemma. -/
@[reassoc]
theorem directedCover_pullback₁_trans_pullbackRestrictIsoRestrict_hom
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Scheme.Cover.trans ((directedCover X).pullback₁ q) i ≫
        (pullbackRestrictIsoRestrict q V.toOpens).hom =
      (pullbackRestrictIsoRestrict q U.toOpens).hom ≫
        T.homOfLE (q.preimage_mono (toOpens_mono i.le)) := by
  -- The transition maps of the pulled-back cover are indexed by its own index type; `change`
  -- presents the transition as the underlying map of pullbacks so that rewriting is type-correct.
  change pullback.map q U.toOpens.ι q V.toOpens.ι (𝟙 _) (X.homOfLE (toOpens_mono i.le)) (𝟙 _)
    (by simp) (by simp) ≫ _ = _
  rw [← cancel_mono (q ⁻¹ᵁ V.toOpens).ι]
  simp

end TauCeti.AlgebraicGeometry.Scheme.AffineZariskiSite
