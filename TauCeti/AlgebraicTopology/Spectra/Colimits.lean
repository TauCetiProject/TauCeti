/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Spectra.Free
public import TauCeti.AlgebraicTopology.Spectra.SphereMonoid
public import TauCeti.CategoryTheory.Monoidal.Action.Colimits
public import TauCeti.CategoryTheory.Monoidal.Mod.Colimits

/-!
# Colimits of symmetric spectra

Colimits of symmetric sequences are computed levelwise. Day convolution preserves these
colimits separately in each variable, so the forgetful functor from sphere modules creates
colimits. This gives all small colimits of symmetric spectra, and of modules over every higher
sphere monoid, with the sphere action induced on the levelwise colimit.

`SymmetricSpectrum.isColimitOfLevelwise` recognizes colimit cocones by their levels.
Level evaluation preserves colimits, so Mathlib's `preservesColimitIso` gives the canonical
isomorphism between a level of a spectral colimit and the colimit of that level. Its injection
formulas are `ι_preservesColimitIso_hom` and `ι_preservesColimitIso_inv`.
These are strict categorical colimits, not homotopy colimits.

The construction reuses Mathlib's left-Kan-extension adjunction and functor-category colimits,
and the colimit-creation theorem for native module objects.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.2.
-/

public section

universe v w u

open CategoryTheory MonoidalCategory Limits

namespace TauCeti

open scoped DayFunctor

/- The generic module-object instances create colimits for all the sphere monoids. -/
noncomputable example : HasColimits SymmetricSpectrum := inferInstance
noncomputable example (k : ℕ) : HasColimits (SphereModule k) := inferInstance
noncomputable example : CreatesColimits
    (Mod.forget (D := SymmetricSequence.{0}) SymmetricSequence.sphere) := inferInstance

/-- Level evaluation preserves colimits of symmetric spectra. -/
instance SymmetricSpectrum.evaluation_preservesColimitsOfShape
    (J : Type w) [Category.{v} J] [HasColimitsOfShape J PointedSSet.{0}] (n : ℕ) :
    PreservesColimitsOfShape J (evaluation n) :=
  inferInstanceAs (PreservesColimitsOfShape J
    (Mod.forget SymmetricSequence.sphere ⋙
      (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor ⋙
        (CategoryTheory.evaluation FiniteBijection PointedSSet.{0}).obj (FiniteBijection.mk n)))

/-- Level evaluation preserves all small colimits. -/
instance SymmetricSpectrum.evaluation_preservesColimits (n : ℕ) :
    PreservesColimits (evaluation n) where
  preservesColimitsOfShape := inferInstance

/-- A cocone of symmetric spectra is a colimit if it is a colimit in each level.
Its universal maps automatically respect the sphere action. -/
noncomputable def SymmetricSpectrum.isColimitOfLevelwise {J : Type w} [Category.{v} J]
    [HasColimitsOfShape J PointedSSet.{0}] {F : J ⥤ SymmetricSpectrum} (c : Cocone F)
    (h : ∀ n : ℕ, IsColimit ((evaluation n).mapCocone c)) : IsColimit c := by
  apply isColimitOfReflects (Mod.forget SymmetricSequence.sphere)
  apply isColimitOfReflects (DayFunctor.equiv FiniteBijection PointedSSet).functor
  apply evaluationJointlyReflectsColimits
  rintro ⟨n⟩
  -- Reassociate the mapped cocones through the three forgetful/evaluation functors.
  exact IsColimit.equivOfNatIsoOfIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)) _ _
    (Cocone.ext (Iso.refl _) (fun _ ↦ by simp)) (h n)

end TauCeti
