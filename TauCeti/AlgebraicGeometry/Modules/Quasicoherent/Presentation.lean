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
  let F : SheafOfModules (Spec Γ(X, ⊤)).ringCatSheaf ⥤
      SheafOfModules X.ringCatSheaf := Scheme.Modules.pullback e.hom
  have : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction e.hom).leftAdjoint_preservesColimits
  let h : F.obj N ≅ M :=
    (Scheme.Modules.pullbackComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pullbackCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.pullbackId X).app M
  exact ⟨@SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ h.hom (Iso.isIso_hom h)
    (Q.map F (Scheme.Modules.pullbackObjUnitIso e.hom).symm)⟩

end

end TauCeti
