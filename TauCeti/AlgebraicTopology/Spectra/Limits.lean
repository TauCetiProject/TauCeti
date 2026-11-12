/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Spectra.SymmetricSpectrum
public import TauCeti.CategoryTheory.Monoidal.Mod.Limits

/-!
# Limits of symmetric spectra

Symmetric sequences have limits computed in pointed simplicial sets at each level. The
forgetful functor from sphere modules creates limits, so the native category of symmetric
spectra has all small limits, with its sphere action induced by the universal property.
`SymmetricSpectrum.isLimitOfLevelwise` recognizes limiting cones by their levels.

For a level `n`, compose `Mod.forget SymmetricSequence.sphere`, the functor of
`DayFunctor.equiv FiniteBijection PointedSSet`, and
`(evaluation FiniteBijection PointedSSet).obj (FiniteBijection.mk n)`.
This composite preserves limits. Mathlib's `preservesLimitIso` identifies the level of a
spectral limit with the limit of its levels; `preservesLimitIso_hom_π` and
`preservesLimitIso_inv_π` identify its projections. These are strict categorical limits.

The construction uses Mathlib's `DayFunctor.equiv`, functor-category limits, and the generic
limit creation theorem for module objects.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.2.
-/

public section

universe v w

open CategoryTheory MonoidalCategory Limits

namespace TauCeti

/-- A cone of symmetric spectra is limiting if its cone of pointed simplicial sets is
limiting at every level. In particular, the limiting maps respect the sphere action. -/
noncomputable def SymmetricSpectrum.isLimitOfLevelwise {J : Type w} [Category.{v} J]
    {F : J ⥤ SymmetricSpectrum} (c : Cone F)
    (h : ∀ n : ℕ, IsLimit
      (((evaluation FiniteBijection PointedSSet).obj (FiniteBijection.mk n)).mapCone
        ((DayFunctor.equiv FiniteBijection PointedSSet).functor.mapCone
          ((Mod.forget SymmetricSequence.sphere).mapCone c)))) : IsLimit c := by
  apply isLimitOfReflects (Mod.forget SymmetricSequence.sphere)
  apply isLimitOfReflects (DayFunctor.equiv FiniteBijection PointedSSet).functor
  apply evaluationJointlyReflectsLimits
  intro n
  simpa only [FiniteBijection.mk_len] using h n.len

end TauCeti
