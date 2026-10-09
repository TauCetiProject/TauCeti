/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Prime
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.GlobalSections

/-!
# Global sections of the projective Weierstrass model

For a Weierstrass curve `W` over a commutative ring `R`, the only global functions on the
projective Weierstrass model `W.projModel` are the constants: the structure morphism
`W.projModelOver : W.projModel ⟶ Spec R` induces an isomorphism `R ≅ Γ(W.projModel, 𝒪)` on global
sections. No hypothesis is made on `R` or on `W`; in particular the base may be nonreduced and the
cubic may be singular.

Since the projective model commutes with base change
(`WeierstrassCurve.isPullback_projModelBaseChange`), the same holds after every base change
`Spec R' ⟶ Spec R`: for the base change `π_T : E_T ⟶ T = Spec R'` of the structure morphism, the
unit `𝒪_T ⟶ (π_T)_* 𝒪_{E_T}` is an isomorphism on global sections.

The classes of `Z` and `Y` form a regular sequence in the homogeneous coordinate ring
(`WeierstrassCurve.Projective.isWeaklyRegular_coord_two_coord_one`), so this is an instance of
`AlgebraicGeometry.Proj.isIso_appTop_toSpecZero`.

## Main results

* `WeierstrassCurve.isIso_appTop_projModelOver`: the structure morphism of the projective
  Weierstrass model induces an isomorphism on global sections.
* `WeierstrassCurve.isIso_appTop_pullbackSnd_projModelOver`: the same holds after base change
  along any `Spec R' ⟶ Spec R`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The global functions on the projective Weierstrass model are the constants: the structure
morphism `W.projModel ⟶ Spec R` induces an isomorphism `R ≅ Γ(W.projModel, 𝒪)` on global
sections. -/
instance isIso_appTop_projModelOver : IsIso W.projModelOver.appTop := by
  have := Proj.isIso_appTop_toSpecZero W.toProjective.grading
    (W.toProjective.coord_mem_grading 2) (W.toProjective.coord_mem_grading 1) one_pos one_pos
    W.toProjective.isWeaklyRegular_coord_two_coord_one
  rw [projModelOver_def, Scheme.Hom.comp_appTop]
  have : IsIso (Spec.map W.toProjective.gradingZeroEquiv.toRingEquiv.toCommRingCatIso.hom).appTop :=
    inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  infer_instance

/-- The global functions on the projective Weierstrass model stay constant after base change along
any `Spec R' ⟶ Spec R`: the second projection of `W.projModel ×_{Spec R} Spec R'` induces an
isomorphism `R' ≅ Γ(W.projModel ×_{Spec R} Spec R', 𝒪)` on global sections. -/
instance isIso_appTop_pullbackSnd_projModelOver {R' : Type u} [CommRing R'] (φ : R →+* R') :
    IsIso (pullback.snd W.projModelOver (Spec.map (CommRingCat.ofHom φ))).appTop := by
  -- the base change is the projective model of `W.map φ`
  rw [← (W.isPullback_projModelBaseChange φ).isoPullback_inv_snd, Scheme.Hom.comp_appTop]
  have : IsIso (W.isPullback_projModelBaseChange φ).isoPullback.inv.appTop :=
    inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  infer_instance

end WeierstrassCurve
