/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pushforward
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Presentation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine pushforward of quasicoherent modules

Pushforward along an affine morphism preserves quasicoherence. The affine calculation reduces
via the canonical spectrum isomorphisms to Mathlib's `isIso_fromTildeΓ_pushforward`.
Restriction to affine opens then supplies the result over an arbitrary base. In particular,
the pushforward of the structure sheaf along an affine morphism is quasicoherent.

## References

* The Stacks Project, Tag 01LC (quasicoherence of pushforward).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

open Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Pushforward along a scheme isomorphism preserves quasicoherence. -/
theorem isQuasicoherent_pushforward_iso (e : X ≅ Y) (M : X.Modules)
    [M.IsQuasicoherent] : ((pushforward e.hom).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((pushforwardIsoRestrict e).app M).symm inferInstance

/-- Pushforward between affine schemes preserves quasicoherence. -/
theorem isQuasicoherent_pushforward_of_isAffine [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  have := isQuasicoherent_pushforward_iso X.isoSpec M
  have := Scheme.Modules.isQuasicoherent_pushforward_specMap f.appTop
    ((pushforward X.isoSpec.hom).obj M)
  have h := isQuasicoherent_pushforward_iso Y.isoSpec.symm
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
theorem isQuasicoherent_pushforward (f : X ⟶ Y) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] : ((pushforward f).obj M).IsQuasicoherent := by
  let N := (pushforward f).obj M
  have hrestrict (U : Y.affineOpens) : (N.restrict U.1.ι).IsQuasicoherent := by
    have : IsAffine U.1.toScheme := U.2
    have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
    have h := isQuasicoherent_pushforward_of_isAffine (f ∣_ U.1)
      (M.restrict (f ⁻¹ᵁ U.1).ι)
    exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
      ((restrictPushforwardIso f U.1).app M).symm h
  have (U : Y.affineOpens) : (N.over U.1).IsQuasicoherent := by
    have : IsAffine U.1.toScheme := U.2
    have := hrestrict U
    obtain ⟨P⟩ := (N.restrict U.1.ι).nonempty_presentation_of_isAffine
    -- Rebind the inverse equivalence on sheaf categories so `Presentation.map` sees
    -- its colimit-preservation instance without unfolding `Scheme.Modules`.
    let F : SheafOfModules U.1.toScheme.ringCatSheaf ⥤
        SheafOfModules (Y.ringCatSheaf.over U.1) := (overEquiv U.1).inverse
    have : Limits.PreservesColimitsOfSize.{u, u} F :=
      (overEquiv U.1).symm.toAdjunction.leftAdjoint_preservesColimits
    let Q := P.map F
      (U.1.sheafOfModulesEquivOverInverseUnit Y.ringCatSheaf).symm
    let e := (overEquiv U.1).unitIso.app (N.over U.1) ≪≫
      (overEquiv U.1).inverse.mapIso ((overFunctorEquiv U.1).app N)
    exact (Q.ofIsIso e.inv).isQuasicoherent
  exact SheafOfModules.IsQuasicoherent.of_coversTop N (fun U : Y.affineOpens ↦ U.1)
    (by rw [Opens.coversTop_iff]; exact iSup_affineOpens_eq_top Y)

end

end TauCeti.AlgebraicGeometry
