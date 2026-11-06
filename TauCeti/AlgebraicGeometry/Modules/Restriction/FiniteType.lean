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
cover, or to all affine opens, and a module is of finite type over a union of opens if it is so
over each of them. This is the finite-type analogue of
`TauCeti.AlgebraicGeometry.isQuasicoherent_of_isQuasicoherent_restrict`.
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

/-- A module of finite type over the image of an open immersion `f` is of finite type over the
image of every open immersion `g` with `g.opensRange ≤ f.opensRange`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isFiniteType_restrict_of_opensRange_le
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (g : Z ⟶ X) [IsOpenImmersion g]
    (h : g.opensRange ≤ f.opensRange) (M : X.Modules) [(M.restrict f).IsFiniteType] :
    (M.restrict g).IsFiniteType := by
  have H : Set.range g ⊆ Set.range f := by
    simpa only [Scheme.Hom.coe_opensRange] using SetLike.coe_subset_coe.mpr h
  have : ((Scheme.Modules.restrictFunctor f ⋙
      Scheme.Modules.restrictFunctor (IsOpenImmersion.lift f g H)).obj M).IsFiniteType :=
    inferInstanceAs ((M.restrict f).restrict (IsOpenImmersion.lift f g H)).IsFiniteType
  exact SheafOfModules.IsFiniteType.of_iso (R := Z.ringCatSheaf)
    ((Scheme.Modules.restrictFunctorIsoOfOpensRangeLE f g h).app M).symm

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

/-- A module is of finite type over a union of opens if it is of finite type over each of
them. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isFiniteType_restrict_iSup {X : Scheme.{u}}
    {ι : Type*} (M : X.Modules) (U : ι → X.Opens) (h : ∀ i, (M.restrict (U i).ι).IsFiniteType) :
    (M.restrict (⨆ i, U i).ι).IsFiniteType := by
  let V := ⨆ i, U i
  refine isFiniteType_of_isFiniteType_restrict _ (fun i ↦ V.ι ⁻¹ᵁ U i)
    (by rw [← Scheme.Hom.preimage_iSup, Scheme.Opens.ι_preimage_self]) fun i ↦ ?_
  have : (M.restrict ((V.ι ⁻¹ᵁ U i).ι ≫ V.ι)).IsFiniteType := by
    have := h i
    refine Scheme.Modules.isFiniteType_restrict_of_opensRange_le (U i).ι _ ?_ M
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      Scheme.Opens.opensRange_ι]
    exact inf_le_right
  exact SheafOfModules.IsFiniteType.of_iso (R := (V.ι ⁻¹ᵁ U i).toScheme.ringCatSheaf)
    ((Scheme.Modules.restrictFunctorComp _ _).app M)

/-- Finite type can be checked on restrictions to all affine open subschemes. -/
theorem isFiniteType_of_isFiniteType_restrict_affineOpens {X : Scheme.{u}}
    (M : X.Modules) (h : ∀ U : X.affineOpens, (M.restrict U.1.ι).IsFiniteType) :
    M.IsFiniteType :=
  isFiniteType_of_isFiniteType_restrict M (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) h

end TauCeti.AlgebraicGeometry
