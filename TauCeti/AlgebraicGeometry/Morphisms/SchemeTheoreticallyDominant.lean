/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.RingHom.Injective

/-!
# Schematic density and separated targets

Morphisms over a base into a separated scheme are determined by their restriction along a
scheme-theoretically dominant morphism. Unlike the corresponding statement for topologically
dominant morphisms, this requires no reducedness hypothesis on the source. In particular, it
applies to flat models with a possibly nonreduced generic fibre.

The equalizer argument extends Mathlib's
`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`, by Christian Merten and Andrew Yang:
schematic density makes the closed equalizer the entire source as a scheme, not just as a space.

The file also gives criteria for scheme-theoretic dominance. A morphism to an affine scheme is
scheme-theoretically dominant exactly when it is injective on global sections
(`AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_appTop_injective`); in particular, `Spec` of
a ring homomorphism is scheme-theoretically dominant exactly when the homomorphism is injective
(`AlgebraicGeometry.isSchemeTheoreticallyDominant_SpecMap_iff`). A morphism is scheme-theoretically
dominant if its base change to each member of an open cover of the target is
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_openCover`).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

variable {W X Y S : Scheme.{u}}

/-- Two morphisms into a separated scheme over a base agree if they agree after precomposition
with a scheme-theoretically dominant morphism. The source need not be reduced. -/
theorem ext_of_isSchemeTheoreticallyDominant
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] {f g : X ⟶ Y}
    (s : Y ⟶ S) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (hι : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over S := Over.mk (f ≫ s)
  let Y' : Over S := Over.mk s
  let W' : Over S := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let ι' : W' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := inferInstanceAs (IsSeparated s)
  have hι' : ι' ≫ f' = ι' ≫ g' := by
    apply Over.OverMorphism.ext
    simpa only [Over.comp_left, ι', f', g', Over.homMk_left] using hι
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_antisymm _ bot_le
    calc
      (equalizer.ι f' g').left.ker ≤
          ((equalizer.lift ι' hι').left ≫ (equalizer.ι f' g').left).ker :=
        Scheme.Hom.le_ker_comp _ _
      _ = ι.ker := by
        rw [← Over.comp_left, equalizer.lift_ι]
        simp only [ι', Over.homMk_left]
      _ = ⊥ := ι.ker_eq_bot
  have : IsIso (equalizer.ι f' g').left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  rw [← cancel_epi (equalizer.ι f' g').left]
  simpa only [Over.comp_left, f', g', Over.homMk_left] using
    congrArg Over.Hom.left (equalizer.condition f' g')

end TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A morphism `f : X ⟶ Y` to an affine scheme is scheme-theoretically dominant exactly when it
is injective on global sections. -/
theorem isSchemeTheoreticallyDominant_iff_appTop_injective (f : X ⟶ Y) [IsAffine Y] :
    IsSchemeTheoreticallyDominant f ↔ Function.Injective f.appTop := by
  -- an ideal sheaf on an affine scheme is trivial exactly when its ideal of global sections is
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_eq_bot_iff,
    RingHom.injective_iff_ker_eq_bot]

/-- `Spec` of a ring homomorphism `φ` is scheme-theoretically dominant exactly when `φ` is
injective. -/
@[simp]
theorem isSchemeTheoreticallyDominant_SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    IsSchemeTheoreticallyDominant (Spec.map φ) ↔ Function.Injective φ.hom := by
  -- on global sections, `Spec.map φ` is `φ`, up to the isomorphisms `Scheme.ΓSpecIso`
  rw [isSchemeTheoreticallyDominant_iff_appTop_injective,
    RingHom.injective_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine φ)]

/-- A morphism `f : X ⟶ Y` is scheme-theoretically dominant if its base change to each member of
an open cover of `Y` is scheme-theoretically dominant. -/
theorem IsSchemeTheoreticallyDominant.of_openCover {f : X ⟶ Y} (𝒰 : Y.OpenCover)
    (h : ∀ i, IsSchemeTheoreticallyDominant (𝒰.pullbackHom f i)) :
    IsSchemeTheoreticallyDominant f := by
  -- the kernels of the members of an open cover of `Y` have trivial intersection, so it suffices
  -- that each of them contains the kernel of `f`
  rw [isSchemeTheoreticallyDominant_iff, eq_bot_iff, ← Scheme.Hom.ker_eq_bot_of_isIso (𝟙 Y),
    ← Scheme.Hom.iInf_ker_openCover_map_comp (𝟙 Y) 𝒰]
  refine le_iInf fun i ↦ ?_
  -- the base change of `f` to a member of the cover has trivial kernel, so following it by the
  -- member gives a morphism with the kernel of the member, and this morphism factors through `f`
  rw [Category.comp_id, ← Scheme.IdealSheafData.map_bot (𝒰.f i), ← (h i).ker_eq_bot,
    Scheme.IdealSheafData.map_ker, 𝒰.pullbackHom_map]
  exact Scheme.Hom.le_ker_comp _ _

end AlgebraicGeometry
