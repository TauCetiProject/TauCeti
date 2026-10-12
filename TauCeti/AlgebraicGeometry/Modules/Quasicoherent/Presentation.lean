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

end

end TauCeti
