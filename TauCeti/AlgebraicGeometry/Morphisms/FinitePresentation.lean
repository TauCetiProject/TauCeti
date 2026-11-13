/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Morphisms locally of finite presentation

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes. If `f ≫ g` is locally of finite
presentation and `g` is locally of finite type, then `f` is locally of finite presentation
(`AlgebraicGeometry.locallyOfFinitePresentation_of_comp`). In particular, every morphism over `Z`
between two schemes locally of finite presentation over `Z` is locally of finite presentation.

This is the scheme version of `RingHom.FinitePresentation.of_comp_finiteType`, to which the proof
reduces on affine opens. It parallels Mathlib's `AlgebraicGeometry.locallyOfFiniteType_of_comp`,
which needs no hypothesis on `g`; for finite presentation the hypothesis on `g` cannot be dropped.

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation_of_comp`: if `f ≫ g` is locally of finite
  presentation and `g` is locally of finite type, then `f` is locally of finite presentation.

* `CommRingCat.locallyOfFinitePresentation_terminal_from_Spec_iff`: finite presentation over
  the terminal scheme for an affine scheme is equivalent to finite presentation over `ℤ`.

## References

* The Stacks Project, [Tag 02FV](https://stacks.math.columbia.edu/tag/02FV).
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Cancellation for morphisms locally of finite presentation** (Stacks, Tag 02FV). If
`f ≫ g` is locally of finite presentation and `g` is locally of finite type, then `f` is locally
of finite presentation. -/
theorem locallyOfFinitePresentation_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hfg : LocallyOfFinitePresentation (f ≫ g)] [hg : LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := by
  -- check on an affine open `V ∋ x` of `X` mapping into affine opens `U` of `Y` and `W` of `Z`
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_stableUnderComposition
      RingHom.finitePresentation_holdsForLocalizationAway).left]
  intro x
  obtain ⟨W, hW, hxW, -⟩ :=
    Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens (Opens.mem_top (g (f x)))
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (U := g ⁻¹ᵁ W) hxW
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := f ⁻¹ᵁ U) hxU
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, ?_⟩
  -- there this is `RingHom.FinitePresentation.of_comp_finiteType`
  have H : (g.appLE W U hUW ≫ f.appLE U V hVU).hom.FinitePresentation := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact HasRingHomProperty.appLE _ _ hfg ⟨W, hW⟩ ⟨V, hV⟩ _
  exact H.of_comp_finiteType _ (HasRingHomProperty.appLE _ g hg ⟨W, hW⟩ ⟨U, hU⟩ hUW)

end AlgebraicGeometry

open AlgebraicGeometry CategoryTheory.Limits

namespace CommRingCat

/-- The spectrum of a ring `R` is locally of finite presentation over the terminal scheme
`Spec ℤ` if and only if `R` is of finite presentation over `ℤ`. -/
@[simp]
lemma locallyOfFinitePresentation_terminal_from_Spec_iff (R : CommRingCat.{u}) :
    LocallyOfFinitePresentation (terminal.from (Spec R)) ↔ Algebra.FinitePresentation ℤ R := by
  let g : CommRingCat.of (ULift.{u} ℤ) ⟶ R :=
    CommRingCat.ofHom ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom)
  have : MorphismProperty.RespectsIso @LocallyOfFinitePresentation :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map g),
    MorphismProperty.cancel_right_of_respectsIso (P := @LocallyOfFinitePresentation),
    LocallyOfFinitePresentation.SpecMap_iff, ← RingHom.finitePresentation_algebraMap]
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp (.of_bijective ULift.ringEquiv.bijective)⟩
  have : algebraMap ℤ R = g.hom.comp ULift.ringEquiv.symm.toRingHom := by
    ext; simp [g]
  rw [this]
  exact h.comp (.of_bijective ULift.ringEquiv.symm.bijective)

instance (R : CommRingCat.{u}) [Algebra.FiniteType ℤ R] :
    LocallyOfFinitePresentation (terminal.from (Spec R)) :=
  (locallyOfFinitePresentation_terminal_from_Spec_iff R).mpr
    (Algebra.FinitePresentation.of_finiteType.mp inferInstance)

end CommRingCat
