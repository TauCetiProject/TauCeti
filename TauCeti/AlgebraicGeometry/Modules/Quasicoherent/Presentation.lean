/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Global presentations of quasicoherent sheaves on affine schemes

A quasicoherent module on an affine scheme admits a global presentation by free sheaves,
with arbitrary sets of generators and relations. This permits colimit arguments with
quasicoherent modules on an affine scheme, even when no finite generation is assumed.

The restriction to an open subscheme and the module on its slice site have compatible
presentations. Quasicoherence can therefore be checked on restrictions to affine opens.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

/-- A presentation on the canonical spectrum of an affine scheme transports back to a
presentation on the affine scheme. -/
def _root_.AlgebraicGeometry.Scheme.Modules.presentationOfIsoSpec
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    (P : ((Scheme.Modules.pullback X.isoSpec.inv).obj M).Presentation) : M.Presentation := by
  let F : SheafOfModules (Spec Γ(X, ⊤)).ringCatSheaf ⥤
      SheafOfModules X.ringCatSheaf := Scheme.Modules.pullback X.isoSpec.hom
  have : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction X.isoSpec.hom).leftAdjoint_preservesColimits
  let h : F.obj ((Scheme.Modules.pullback X.isoSpec.inv).obj M) ≅ M :=
    (Scheme.Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv).app M ≪≫
      (Scheme.Modules.pullbackCongr X.isoSpec.hom_inv_id).app M ≪≫
      (Scheme.Modules.pullbackId X).app M
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ h.hom (Iso.isIso_hom h)
    (P.map F (Scheme.Modules.pullbackObjUnitIso X.isoSpec.hom).symm)

/-- Transporting a presentation from the canonical spectrum preserves finite generators and
finite relations. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isFinite_presentationOfIsoSpec
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    (P : ((Scheme.Modules.pullback X.isoSpec.inv).obj M).Presentation) [P.IsFinite] :
    (M.presentationOfIsoSpec P).IsFinite := by
  let F : SheafOfModules (Spec Γ(X, ⊤)).ringCatSheaf ⥤
      SheafOfModules X.ringCatSheaf := Scheme.Modules.pullback X.isoSpec.hom
  have : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction X.isoSpec.hom).leftAdjoint_preservesColimits
  unfold Scheme.Modules.presentationOfIsoSpec
  exact @SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _ _ (Iso.isIso_hom _) _
    (SheafOfModules.Presentation.isFinite_map _ _ _)

/-- A quasicoherent module on an affine scheme admits a global presentation by free sheaves.
The generating and relation families need not be finite. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_presentation_of_isAffine
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    Nonempty M.Presentation := by
  let e := X.isoSpec
  let N := (Scheme.Modules.pullback e.inv).obj M
  have : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pullback e.inv M
  let A := moduleSpecΓFunctor.obj N
  let P := presentationTilde A Set.univ (by simp) _ (Submodule.span_eq _)
  -- Supply the isomorphism instance explicitly: the presentation API uses sheaves of modules,
  -- while `fromTildeΓ` is stated with the category instance on scheme modules.
  let Q := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    (Scheme.Modules.fromTildeΓ N)
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N) P
  exact ⟨M.presentationOfIsoSpec Q⟩

namespace AlgebraicGeometry

/-- A presentation on the open subscheme gives a presentation on the slice site over the open. -/
def presentationOver {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  -- The equivalence changes the base ring sheaf, so its comparison is not an iso of
  -- modules over `X.ringCatSheaf.over U`; transport the presentation through the equivalence.
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤
      SheafOfModules (X.ringCatSheaf.over U) := (Scheme.Modules.overEquiv U).inverse
  have : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.overEquiv U).symm.toAdjunction.leftAdjoint_preservesColimits
  let Q := P.map F (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let e := (Scheme.Modules.overEquiv U).unitIso.app (M.over U) ≪≫
    (Scheme.Modules.overEquiv U).inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)
  exact Q.ofIsIso e.inv

/-- Transport from an open subscheme to its slice site preserves finite presentations. -/
instance isFinite_presentationOver {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) [P.IsFinite] : (presentationOver M U P).IsFinite := by
  unfold presentationOver
  apply +allowSynthFailures SheafOfModules.instIsFiniteOfIsIso
  apply +allowSynthFailures SheafOfModules.Presentation.isFinite_map

/-- Quasicoherence on an affine open subscheme implies quasicoherence on its slice site. -/
theorem isQuasicoherent_over_of_isQuasicoherent_restrict {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) [IsAffine U.toScheme] [(M.restrict U.ι).IsQuasicoherent] :
    (M.over U).IsQuasicoherent := by
  obtain ⟨P⟩ := (M.restrict U.ι).nonempty_presentation_of_isAffine
  exact (presentationOver M U P).isQuasicoherent

/-- Quasicoherence can be checked on restrictions to all affine open subschemes. -/
theorem isQuasicoherent_of_isQuasicoherent_restrict_affineOpens {X : Scheme.{u}}
    (M : X.Modules) (h : ∀ U : X.affineOpens, (M.restrict U.1.ι).IsQuasicoherent) :
    M.IsQuasicoherent := by
  have (U : X.affineOpens) : (M.over U.1).IsQuasicoherent := by
    have : IsAffine U.1.toScheme := U.2
    have := h U
    exact isQuasicoherent_over_of_isQuasicoherent_restrict M U.1
  exact SheafOfModules.IsQuasicoherent.of_coversTop M (fun U : X.affineOpens ↦ U.1)
    (by rw [Opens.coversTop_iff]; exact iSup_affineOpens_eq_top X)

end AlgebraicGeometry

end

end TauCeti
