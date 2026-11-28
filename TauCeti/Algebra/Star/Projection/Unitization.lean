/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary

import Mathlib.Algebra.Star.UnitaryStarAlgAut
import TauCeti.Algebra.Algebra.Unitization

/-!
# Projections in the unitization

Algebraic behavior of star projections under unitary conjugation in the unitization
`Unitization R A`.

## Main declarations

* `IsStarProjection.isStarProjection_unitization_conj_snd`: conjugating a star projection `p : A`
  by a unitary of `Unitization R A` has `A`-component that is a star projection in `A`.
-/

public section

/-- Conjugating a star projection `p : A` by a unitary of `Unitization R A` yields an element
whose `A`-component is a star projection in `A`. -/
theorem IsStarProjection.isStarProjection_unitization_conj_snd {R A : Type*} [CommSemiring R]
    [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarModule R A] {p : A} (hp : IsStarProjection p)
    (u : unitary (Unitization R A)) :
    IsStarProjection (((u : Unitization R A) * (p : Unitization R A) *
      star (u : Unitization R A)).snd) := by
  have hproj : IsStarProjection
      ((u : Unitization R A) * (p : Unitization R A) * star (u : Unitization R A)) := by
    simpa only [Unitary.conjStarAlgAut_apply] using
      hp.inr.map (Unitary.conjStarAlgAut R (Unitization R A) u)
  exact IsStarProjection.of_inr (R := R)
    ((Unitization.inr_snd_mul_inr_mul (u : Unitization R A) p
      (star (u : Unitization R A))).symm ▸ hproj)
