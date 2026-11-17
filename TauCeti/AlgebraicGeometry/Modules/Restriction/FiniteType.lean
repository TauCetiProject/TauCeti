/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FiniteType
public import TauCeti.AlgebraicGeometry.Modules.FiniteType
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Restriction criteria for modules of finite type on schemes

The restriction of a module of finite type along an open immersion is of finite type, and the
inverse of the equivalence between modules on an open subscheme and modules on its slice site
preserves finite type. Consequently, finite type can be checked on restrictions to any open
cover, or to all affine opens. This is the finite-type analogue of
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_of_iSup_eq_top`.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- The restriction of a module of finite type along an open immersion is of finite type: it is
isomorphic to the pullback, which is of finite type. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isFiniteType_restrict {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (M : X.Modules) [M.IsFiniteType] :
    (M.restrict j).IsFiniteType :=
  Scheme.Modules.isFiniteType_of_epi ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M)

/-- The inverse open-subscheme equivalence sends modules of finite type to modules of finite
type on the slice site. -/
instance isFiniteType_overEquiv_inverse {X : Scheme.{u}} (U : X.Opens)
    (M : U.toScheme.Modules) [hM : M.IsFiniteType] :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsFiniteType := by
  let G := U.overEquivalence.functor
  have hcont (V : Over U) : (Over.post (X := V) G).IsContinuous
      (((Opens.grothendieckTopology X).over U).over V)
      ((Opens.grothendieckTopology {x : X // x ∈ U}).over (G.obj V)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous G _ _).overPost V)
  let ψ := (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
  have hψ : IsIso ψ := by dsimp [ψ]; infer_instance
  exact SheafOfModules.isFiniteType_pushforward_of_isLeftAdjoint (G := G) (φ := ψ)
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) (hφ := hψ) (hG := hcont) (M := M)
    (hM := hM)

/-- Finite type on an open subscheme implies finite type on its slice site. -/
theorem isFiniteType_over_of_isFiniteType_restrict {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) [(M.restrict U.ι).IsFiniteType] :
    (M.over U).IsFiniteType := by
  have := isFiniteType_overEquiv_inverse U (M.restrict U.ι)
  let e := (Scheme.Modules.overEquiv U).unitIso.app (M.over U) ≪≫
    (Scheme.Modules.overEquiv U).inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)
  exact SheafOfModules.IsFiniteType.of_iso (R := X.ringCatSheaf.over U) e.symm

/-- Finite type can be checked on restrictions to an open cover. -/
theorem isFiniteType_of_isFiniteType_restrict {X : Scheme.{u}} {ι : Type*}
    (M : X.Modules) (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, (M.restrict (U i).ι).IsFiniteType) : M.IsFiniteType := by
  have (i : ι) : (M.over (U i)).IsFiniteType := by
    have := h i
    exact isFiniteType_over_of_isFiniteType_restrict M (U i)
  exact SheafOfModules.IsFiniteType.of_coversTop (M := M) U (by rwa [Opens.coversTop_iff])

/-- Finite type can be checked on restrictions to all affine open subschemes. -/
theorem isFiniteType_of_isFiniteType_restrict_affineOpens {X : Scheme.{u}}
    (M : X.Modules) (h : ∀ U : X.affineOpens, (M.restrict U.1.ι).IsFiniteType) :
    M.IsFiniteType :=
  isFiniteType_of_isFiniteType_restrict M (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) h

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- A module is of finite type on a union of opens if it is of finite type on each member. -/
theorem isFiniteType_restrict_iSup {X : Scheme.{u}} (M : X.Modules) {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ i, (M.restrict (U i).ι).IsFiniteType) :
    (M.restrict (⨆ i, U i).ι).IsFiniteType := by
  let V := ⨆ i, U i
  let W (i : ι) := V.ι ⁻¹ᵁ U i
  apply TauCeti.AlgebraicGeometry.isFiniteType_of_isFiniteType_restrict
    (M.restrict V.ι) W
  · apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.property
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    let f := V.ι.resLE (U i) (W i) le_rfl
    have : IsOpenImmersion f := by dsimp [f, Scheme.Hom.resLE]; infer_instance
    have := hU i
    have : ((M.restrict (U i).ι).restrict f).IsFiniteType := inferInstance
    exact SheafOfModules.IsFiniteType.of_iso (R := (W i).toScheme.ringCatSheaf)
      (M := (M.restrict (U i).ι).restrict f)
      (((restrictFunctorComp f (U i).ι).app M).symm ≪≫
        (restrictFunctorCongr (V.ι.resLE_comp_ι le_rfl)).app M ≪≫
        (restrictFunctorComp (W i).ι V.ι).app M)

end AlgebraicGeometry.Scheme.Modules
