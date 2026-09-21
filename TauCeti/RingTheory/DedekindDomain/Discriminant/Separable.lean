/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.RingTheory.DedekindDomain.Discriminant.Basic

/-!
# Relative discriminants of separable extensions

This file develops the first arithmetic properties of the relative discriminant ideal. For a
separable extension of fraction fields, the relative discriminant is nonzero, and in a tower of
Dedekind domains it satisfies the usual transitivity formula.

## Main results

* `TauCeti.relDiscr_ne_bot`: the relative discriminant of a separable extension is nonzero.
* `TauCeti.relDiscr_tower`: the relative discriminant formula for a tower of Dedekind domains.

The tower formula is the ideal version of Neukirch, *Algebraic Number Theory*, Chapter III,
§2, Proposition 10.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra

variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

/-- The relative discriminant is nonzero when the extension of fraction fields is separable. -/
theorem relDiscr_ne_bot [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    relDiscr A B ≠ ⊥ := by
  exact relDiscr_eq_bot_iff.not.mpr differentIdeal_ne_bot

variable {C : Type*} [CommRing C] [IsDedekindDomain C] [Algebra B C] [Algebra A C]
  [IsScalarTower A B C] [Module.Finite B C] [Module.Finite A C]
  [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]

/-- The relative discriminant satisfies the transitivity formula in a tower of Dedekind domains
when the top extension of fraction fields is separable. -/
theorem relDiscr_tower [Algebra.IsSeparable (FractionRing A) (FractionRing C)] :
    relDiscr A C = relDiscr A B ^ Module.finrank B C * Ideal.relNorm A (relDiscr B C) := by
  have hmap : Ideal.relNorm A
      ((differentIdeal A B).map (algebraMap B C)) =
        Ideal.relNorm A (differentIdeal A B) ^ Module.finrank B C := by
    calc
      _ = Ideal.relNorm A
          (Ideal.relNorm B ((differentIdeal A B).map (algebraMap B C))) :=
        (Ideal.relNorm_relNorm A B _).symm
      _ = Ideal.relNorm A (differentIdeal A B ^ Module.finrank B C) := by
        rw [Ideal.relNorm_algebraMap]
      _ = _ := by rw [map_pow]
  rw [relDiscr_def, differentIdeal_eq_differentIdeal_mul_differentIdeal A B C, map_mul, hmap,
    ← Ideal.relNorm_relNorm A B, mul_comm]
  simp only [relDiscr_def]

end TauCeti

end
