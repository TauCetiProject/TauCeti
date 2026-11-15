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
public import Mathlib.CategoryTheory.Presentable.Finite

import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Presentable.Adjunction

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
Since the underlying simplicial set of a level preserves filtered colimits, the free spectrum
`F_n (K₊)` on a finitely presentable simplicial set `K` is finitely presentable
(`SymmetricSpectrum.isFinitelyPresentable_free_obj_addBasepoint`).
These are strict categorical colimits, not homotopy colimits.

The construction reuses Mathlib's left-Kan-extension adjunction and functor-category colimits,
the colimit-creation theorem for native module objects, and Mathlib's transfer of
presentability along adjunctions.

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

section Presentable

attribute [local instance] Cardinal.fact_isRegular_aleph0

open PointedSSet in
/-- The free spectrum `F_n (K₊)` on a finitely presentable simplicial set is finitely
presentable. -/
instance SymmetricSpectrum.isFinitelyPresentable_free_obj_addBasepoint (n : ℕ) (K : SSet.{0})
    [IsFinitelyPresentable.{0} K] :
    IsFinitelyPresentable.{0} ((SymmetricSpectrum.free n).obj (addBasepoint.obj K)) :=
  have : (evaluation n ⋙ forgetBasepoint).IsCardinalAccessible Cardinal.aleph0.{0} :=
    { preservesColimitOfShape J _ _ := by
        have := isFiltered_of_isCardinalFiltered J Cardinal.aleph0.{0}
        have := IsFiltered.isConnected J
        infer_instance }
  (SymmetricSpectrum.freeAddBasepointAdjunction n).isCardinalPresentable_leftAdjoint_obj _ K

end Presentable

end TauCeti
