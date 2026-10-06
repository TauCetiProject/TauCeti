/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine pushforward of quasicoherent modules

Pushforward between affine schemes and along an affine morphism preserves quasicoherence,
without finiteness, flatness, or separation assumptions. In particular, the pushforward of
the structure sheaf along an affine morphism is quasicoherent. The spectrum case is supplied by
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_specMap` in
`Pushforward/Basic.lean`, based on Mathlib's `isIso_fromTildeΓ_pushforward`.

## References

* The Stacks Project, Tag 01LC (quasicoherence of pushforward).
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Pushforward between affine schemes preserves quasicoherence. -/
private theorem isQuasicoherent_pushforward_of_isAffine [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  have := isQuasicoherent_pushforward_of_iso X.isoSpec M
  have := Scheme.Modules.isQuasicoherent_pushforward_specMap f.appTop
    ((pushforward X.isoSpec.hom).obj M)
  have h := isQuasicoherent_pushforward_of_iso Y.isoSpec.symm
    ((pushforward (Spec.map f.appTop)).obj ((pushforward X.isoSpec.hom).obj M))
  let e : pushforward X.isoSpec.hom ⋙ pushforward (Spec.map f.appTop) ⋙
      pushforward Y.isoSpec.inv ≅ pushforward f :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pushforwardComp X.isoSpec.hom (Spec.map f.appTop)) _ ≪≫
      pushforwardComp _ _ ≪≫ pushforwardCongr (by
        rw [Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso (e.app M) h

/-- Pushforward along an affine scheme morphism preserves quasicoherence.

No finiteness, flatness, or separation hypothesis is needed. -/
instance isQuasicoherent_pushforward_of_isAffineHom (f : X ⟶ Y) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] : ((pushforward f).obj M).IsQuasicoherent := by
  let N := (pushforward f).obj M
  have hrestrict (U : Y.affineOpens) : (N.restrict U.1.ι).IsQuasicoherent := by
    have : IsAffine U.1.toScheme := U.2
    have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
    have h := isQuasicoherent_pushforward_of_isAffine (f ∣_ U.1)
      (M.restrict (f ⁻¹ᵁ U.1).ι)
    exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
      ((restrictPushforwardIso f U.1).app M).symm h
  exact isQuasicoherent_of_isQuasicoherent_restrict_affineOpens N hrestrict

end

end TauCeti.AlgebraicGeometry
