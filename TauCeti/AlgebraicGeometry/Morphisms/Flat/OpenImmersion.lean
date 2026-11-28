/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Diagonal

/-!
# Flat morphisms that are monomorphisms over a schematically dense base change

`Scheme.Hom.mono_of_mono_pullback_of_isSchemeTheoreticallyDominant` detects monomorphisms
among separated flat morphisms by a quasi-compact, scheme-theoretically dominant base change.
It combines `pullback.fst_eq_comp_diagonal_of_mono_snd` with the preservation of schematic
dominance by flat base change.

`Scheme.Hom.isOpenImmersion_of_mono_morphismRestrict` applies the criterion to restriction
over a retrocompact, schematically dense open, using `IsOpenImmersion.of_flat_of_mono`.
In particular, a separated flat morphism locally of finite presentation that is an isomorphism
over such an open is an open immersion. This is the open-immersion step for a strict transform
after flattening, as in [Stacks, Lemma 38.31.3](https://stacks.math.columbia.edu/tag/081S).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A separated flat morphism is a monomorphism if its base change along a quasi-compact,
scheme-theoretically dominant morphism is a monomorphism. -/
theorem mono_of_mono_pullback_of_isSchemeTheoreticallyDominant
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) [IsSeparated f] [Flat f]
    [QuasiCompact g] [IsSchemeTheoreticallyDominant g] [Mono (pullback.snd f g)] : Mono f := by
  have hdiag : IsSchemeTheoreticallyDominant (pullback.diagonal f) := by
    have hfactor := pullback.fst_eq_comp_diagonal_of_mono_snd f g
    have hcomp : IsSchemeTheoreticallyDominant
        ((pullback.fst (pullback.fst f f ≫ f) g ≫ pullback.fst f f) ≫ pullback.diagonal f) :=
      hfactor ▸ inferInstance
    exact IsSchemeTheoreticallyDominant.of_comp
      (pullback.fst (pullback.fst f f ≫ f) g ≫ pullback.fst f f) _
  have hiso : IsIso (pullback.diagonal f) := by
    exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hdiag.ker_eq_bot
  exact (pullback.isIso_diagonal_iff f).mp hiso

/-- A separated flat morphism locally of finite presentation is an open immersion if its
restriction over a retrocompact, schematically dense open is a monomorphism. In particular
the restriction may be an isomorphism. See [Stacks, Lemma 38.11.5]
(https://stacks.math.columbia.edu/tag/081M). -/
theorem isOpenImmersion_of_mono_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact U.ι]
    [IsSchemeTheoreticallyDominant U.ι] [Mono (f ∣_ U)] : IsOpenImmersion f := by
  have hp : Mono (pullback.snd f U.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  have hm : Mono f := f.mono_of_mono_pullback_of_isSchemeTheoreticallyDominant U.ι
  exact IsOpenImmersion.of_flat_of_mono f

end AlgebraicGeometry.Scheme.Hom
