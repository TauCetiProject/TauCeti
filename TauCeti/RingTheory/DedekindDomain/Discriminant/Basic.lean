/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import TauCeti.RingTheory.DedekindDomain.Different.Basic

/-!
# Relative discriminant ideals

For a finite torsion-free extension `A → B` of Dedekind domains, the relative discriminant is the
ideal of `A` obtained by taking the relative norm of Mathlib's different ideal of `B`. This file
introduces that carrier, together with the two defining identities that are valid without a
separability assumption. The later arithmetic theory uses `relDiscr` rather than expanding this
relative norm of the different at each use site.

-/

public section

namespace TauCeti

open scoped nonZeroDivisors

variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

/-- The relative discriminant ideal of the finite torsion-free extension `A → B`. -/
noncomputable def relDiscr (A B : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] : Ideal A :=
  Ideal.relNorm A (differentIdeal A B)

/-- The relative discriminant is the relative norm of the different ideal. -/
theorem relDiscr_def : relDiscr A B = Ideal.relNorm A (differentIdeal A B) := by
  rw [relDiscr]

/-- The relative discriminant is zero exactly when the different is zero. -/
@[simp]
theorem relDiscr_eq_bot_iff : relDiscr A B = ⊥ ↔ differentIdeal A B = ⊥ := by
  rw [relDiscr_def, Ideal.relNorm_eq_bot_iff]

/-- The relative discriminant of the identity extension is the unit ideal. -/
@[simp]
theorem relDiscr_self : relDiscr A A = ⊤ := by
  let _ : Algebra (FractionRing A) (FractionRing A) :=
    FractionRing.liftAlgebra A (FractionRing A)
  rw [relDiscr_def, differentIdeal_self, Ideal.relNorm_top]

end TauCeti

end
