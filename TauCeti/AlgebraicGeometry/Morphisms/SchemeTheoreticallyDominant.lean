/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Schematic density and separated targets

Morphisms over a base into a separated scheme are determined by their restriction along a
scheme-theoretically dominant morphism. Unlike the corresponding statement for topologically
dominant morphisms, this requires no reducedness hypothesis on the source. In particular, it
applies to flat models with a possibly nonreduced generic fibre.

The equalizer argument extends Mathlib's
`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`, by Christian Merten and Andrew Yang:
schematic density makes the closed equalizer the entire source as a scheme, not just as a space.
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
