/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Restriction criteria for quasicoherent modules on schemes

The equivalence between modules on an open subscheme and modules on its slice site preserves
quasicoherence in both directions. Consequently, quasicoherence can be checked on restrictions
to any open cover, or to all affine opens.

The criteria live in `TauCeti.AlgebraicGeometry` and use ordinary function application.
They transport quasicoherence with Mathlib's open-subscheme equivalence and descend it
with `SheafOfModules.IsQuasicoherent.of_coversTop`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- Quasicoherence can be checked after restriction along a scheme isomorphism. -/
theorem isQuasicoherent_of_isQuasicoherent_restrict_iso {X Y : Scheme.{u}}
    (e : X ≅ Y) (M : X.Modules) [hM : (M.restrict e.inv).IsQuasicoherent] :
    M.IsQuasicoherent := by
  let F := Scheme.Modules.restrictFunctor e.inv
  let G := Scheme.Modules.restrictFunctor e.hom
  have : (G.obj (F.obj M)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor e.hom _
  let i : G.obj (F.obj M) ≅ M :=
    (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm.app _ ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app _ ≪≫
      Scheme.Modules.restrictFunctorId.app _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso i inferInstance

/-- The open-subscheme equivalence sends a quasicoherent module on the slice site to a
quasicoherent module on the open subscheme. -/
instance isQuasicoherent_overEquiv_functor {X : Scheme.{u}} (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) [hM : M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv U).functor.obj M).IsQuasicoherent := by
  let G := U.overEquivalence.inverse
  have hcont (V : TopologicalSpace.Opens {x : X // x ∈ U}) : (Over.post (X := V) G).IsContinuous
      ((Opens.grothendieckTopology {x : X // x ∈ U}).over V)
      (((Opens.grothendieckTopology X).over U).over (G.obj V)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous G _ _).overPost V)
  let ψ := (U.overPullbackSheafEquivOver.app X.ringCatSheaf).inv
  have hψ : IsIso ψ := by dsimp [ψ]; infer_instance
  -- Pass the instances explicitly: the scheme and sheaf categories have different
  -- instance heads, although their carriers agree.
  exact @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ ψ
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) _ hψ hcont _ _ M hM

/-- The inverse open-subscheme equivalence sends quasicoherent modules to quasicoherent
modules on the slice site. -/
instance isQuasicoherent_overEquiv_inverse {X : Scheme.{u}} (U : X.Opens)
    (M : U.toScheme.Modules) [hM : M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsQuasicoherent := by
  let G := U.overEquivalence.functor
  have hcont (V : Over U) : (Over.post (X := V) G).IsContinuous
      (((Opens.grothendieckTopology X).over U).over V)
      ((Opens.grothendieckTopology {x : X // x ∈ U}).over (G.obj V)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous G _ _).overPost V)
  let ψ := (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
  have hψ : IsIso ψ := by dsimp [ψ]; infer_instance
  -- Pass the instances explicitly: the scheme and sheaf categories have different
  -- instance heads, although their carriers agree.
  exact @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ ψ
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) _ hψ hcont _ _ M hM

/-- Quasicoherence on an open subscheme implies quasicoherence on its slice site. -/
theorem isQuasicoherent_over_of_isQuasicoherent_restrict {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) [hM : (M.restrict U.ι).IsQuasicoherent] :
    (M.over U).IsQuasicoherent := by
  have h := isQuasicoherent_overEquiv_inverse U (M.restrict U.ι)
  let e := (Scheme.Modules.overEquiv U).unitIso.app (M.over U) ≪≫
    (Scheme.Modules.overEquiv U).inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso e.symm h

/-- Quasicoherence can be checked on restrictions to an open cover. -/
theorem isQuasicoherent_of_isQuasicoherent_restrict {X : Scheme.{u}} {ι : Type u}
    (M : X.Modules) (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, (M.restrict (U i).ι).IsQuasicoherent) : M.IsQuasicoherent := by
  have (i : ι) : (M.over (U i)).IsQuasicoherent := by
    have := h i
    exact isQuasicoherent_over_of_isQuasicoherent_restrict M (U i)
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U
    (by rwa [Opens.coversTop_iff])

/-- Quasicoherence can be checked on restrictions to all affine open subschemes. -/
theorem isQuasicoherent_of_isQuasicoherent_restrict_affineOpens {X : Scheme.{u}}
    (M : X.Modules) (h : ∀ U : X.affineOpens, (M.restrict U.1.ι).IsQuasicoherent) :
    M.IsQuasicoherent :=
  isQuasicoherent_of_isQuasicoherent_restrict M (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) h

end

end TauCeti.AlgebraicGeometry
