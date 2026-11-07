/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Presentation
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.FinitePresentationDescent

/-!
# Restriction criteria for finitely presented modules on schemes

The restriction of a finitely presented module along an open immersion is finitely presented.
Conversely, finite presentation can be checked on restrictions to any open cover: every affine
open contained in a member of the cover carries a finite global presentation, and these
presentations descend. This is the finite-presentation analogue of
`TauCeti.AlgebraicGeometry.isFiniteType_of_isFiniteType_restrict`.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- The restriction of a finitely presented module along an open immersion is finitely
presented: it is isomorphic to the pullback, which is finitely presented. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isFinitePresentation_restrict
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (M : X.Modules)
    [M.IsFinitePresentation] : (M.restrict j).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation U.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback j).app M).symm
    (Scheme.Modules.isFinitePresentation_pullback j M)

/-- Finite presentation can be checked on restrictions to an open cover. -/
theorem isFinitePresentation_of_isFinitePresentation_restrict {X : Scheme.{u}} {ι : Type*}
    (M : X.Modules) (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, (M.restrict (U i).ι).IsFinitePresentation) : M.IsFinitePresentation := by
  -- Descend along the affine opens contained in some member of the cover.
  let W := {W : X.affineOpens // ∃ i, W.1 ≤ U i}
  have (W : W) : (M.over W.1.1).IsFinitePresentation := by
    obtain ⟨i, hi⟩ := W.2
    have := h i
    have : IsAffine W.1.1.toScheme := W.1.2
    have : ((M.restrict (U i).ι).restrict (X.homOfLE hi)).IsFinitePresentation :=
      inferInstance
    have : (M.restrict W.1.1.ι).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation W.1.1.toScheme.ringCatSheaf).prop_of_iso
        (((Scheme.Modules.restrictFunctorComp (X.homOfLE hi) (U i).ι).app M).symm ≪≫
          (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hi)).app M) this
    obtain ⟨P, _⟩ := (M.restrict W.1.1.ι).exists_isFinite_presentation_of_isAffine
    obtain ⟨Q, _⟩ := M.exists_isFinite_presentation_over_of_restrict W.1.1 P
    exact Q.isFinitePresentation
  refine SheafOfModules.IsFinitePresentation.of_coversTop M (fun W : W ↦ W.1.1) ?_
  rw [Opens.coversTop_iff]
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.symm ▸ trivial : x ∈ ⨆ i, U i)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U i) hi
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, i, hVU⟩, hxV⟩

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- A module is finitely presented on a union of opens if it is finitely presented on each
member. -/
theorem isFinitePresentation_restrict_iSup {X : Scheme.{u}} (M : X.Modules) {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ i, (M.restrict (U i).ι).IsFinitePresentation) :
    (M.restrict (⨆ i, U i).ι).IsFinitePresentation := by
  let V := ⨆ i, U i
  let W (i : ι) := V.ι ⁻¹ᵁ U i
  apply TauCeti.AlgebraicGeometry.isFinitePresentation_of_isFinitePresentation_restrict
    (M.restrict V.ι) W
  · apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.property
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    let f := V.ι.resLE (U i) (W i) le_rfl
    have : IsOpenImmersion f := by dsimp [f, Scheme.Hom.resLE]; infer_instance
    have := hU i
    have : ((M.restrict (U i).ι).restrict f).IsFinitePresentation := inferInstance
    exact (SheafOfModules.isFinitePresentation (W i).toScheme.ringCatSheaf).prop_of_iso
      (((restrictFunctorComp f (U i).ι).app M).symm ≪≫
        (restrictFunctorCongr (V.ι.resLE_comp_ι le_rfl)).app M ≪≫
        (restrictFunctorComp (W i).ι V.ι).app M) this

end AlgebraicGeometry.Scheme.Modules
