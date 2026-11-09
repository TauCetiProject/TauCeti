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

The equivalence `Scheme.Modules.overEquiv` between modules on the slice site of an open `U`
and modules on the open subscheme `U` preserves quasicoherence in both directions. Consequently,
a module on a scheme is quasicoherent if and only if its restrictions to the members of an open
cover are (`Scheme.Modules.isQuasicoherent_iff_of_iSup_eq_top`), if and only if its restrictions
to all affine opens are (`Scheme.Modules.isQuasicoherent_iff_forall_affineOpens`). Restriction
along an isomorphism of schemes also preserves and reflects quasicoherence
(`Scheme.Modules.isQuasicoherent_restrict_iff_of_isIso`).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- Restriction along an isomorphism of schemes preserves and reflects quasicoherence. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrict_iff_of_isIso
    {X Y : Scheme.{u}} (M : X.Modules) (f : Y ⟶ X) [IsIso f] :
    (M.restrict f).IsQuasicoherent ↔ M.IsQuasicoherent := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorComp (inv f) f).symm.app M ≪≫
      (Scheme.Modules.restrictFunctorCongr (IsIso.inv_hom_id f)).app M ≪≫
      Scheme.Modules.restrictFunctorId.app M)
    (Scheme.Modules.isQuasicoherent_restrictFunctor (inv f) (M.restrict f))

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

/-- A module is quasicoherent on the slice site of an open `U` if and only if its restriction
to the open subscheme `U` is quasicoherent. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_over_iff {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) :
    (M.over U).IsQuasicoherent ↔ (M.restrict U.ι).IsQuasicoherent := by
  let e := (Scheme.Modules.overFunctorEquiv U).app M
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso e
      (isQuasicoherent_overEquiv_functor U (M.over U))
  · exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
      ((Scheme.Modules.overEquiv U).unitIso.app (M.over U) ≪≫
        (Scheme.Modules.overEquiv U).inverse.mapIso e).symm
      (isQuasicoherent_overEquiv_inverse U (M.restrict U.ι))

/-- A module is quasicoherent if and only if its restrictions to the members of an open cover
are quasicoherent. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_of_iSup_eq_top
    {X : Scheme.{u}} {ι : Sort*} (M : X.Modules) (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    M.IsQuasicoherent ↔ ∀ i, (M.restrict (U i).ι).IsQuasicoherent := by
  refine ⟨fun _ _ ↦ inferInstance, fun h ↦ ?_⟩
  -- Reindex the cover by `Set.range U`, which lives in the universe required by `of_coversTop`.
  have (V : Set.range U) : (M.over V.1).IsQuasicoherent := by
    obtain ⟨_, i, rfl⟩ := V
    exact (M.isQuasicoherent_over_iff (U i)).2 (h i)
  exact SheafOfModules.IsQuasicoherent.of_coversTop M (Subtype.val : Set.range U → X.Opens)
    (by rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover, ← hU]; exact iSup_range' id U)

/-- A module is quasicoherent if and only if its restrictions to all affine open subschemes
are quasicoherent. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_forall_affineOpens
    {X : Scheme.{u}} (M : X.Modules) :
    M.IsQuasicoherent ↔ ∀ U : X.affineOpens, (M.restrict U.1.ι).IsQuasicoherent :=
  M.isQuasicoherent_iff_of_iSup_eq_top (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X)

end

end TauCeti.AlgebraicGeometry
