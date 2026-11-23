/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar.Basic

import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Continuity of the polar unitary factor

When `A` is a complete normed real algebra with a continuous star, compatible star order, and an
isometric real continuous functional calculus (for instance any unital C⋆-algebra), the unitary
factor `Units.polarUnitary : Aˣ → unitary A` of the polar decomposition depends continuously on the
unit (`Units.continuous_polarUnitary`).

## Main declarations

* `Units.continuous_polarUnitary`: continuity of `a ↦ a.polarUnitary` under an isometric real
  continuous functional calculus.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
* Kenneth R. Davidson, *C⋆-Algebras by Example*, Fields Institute Monographs 6, American
  Mathematical Society, 1996, Section I.5.
-/

public section

noncomputable section

open Ring

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [PartialOrder A] [StarOrderedRing A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [ContinuousStar A]

namespace Units

/-- The polar unitary factor `a.polarUnitary` of a unit depends continuously on the unit. -/
theorem continuous_polarUnitary : Continuous fun a : Aˣ ↦ a.polarUnitary := by
  refine Continuous.subtype_mk ?_ _
  have hsqrt : Continuous fun a : Aˣ ↦ CFC.sqrt ((a : A) * star (a : A)) :=
    CFC.continuousOn_sqrt.comp_continuous (continuous_val.mul continuous_val.star)
      fun a ↦ mul_star_self_nonneg (a : A)
  have hinv : Continuous fun a : Aˣ ↦ (CFC.sqrt ((a : A) * star (a : A)))⁻¹ʳ :=
    continuous_iff_continuousAt.2 fun a ↦ by
      have h : ContinuousAt Ring.inverse (CFC.sqrt ((a : A) * star (a : A))) := by
        simpa only [IsUnit.unit_spec] using
          NormedRing.inverse_continuousAt a.isStrictlyPositive_sqrt_mul_star.isUnit.unit
      exact h.comp (x := a) hsqrt.continuousAt
  exact (hinv.mul continuous_val).congr fun a ↦ (coe_polarUnitary a).symm

end Units
