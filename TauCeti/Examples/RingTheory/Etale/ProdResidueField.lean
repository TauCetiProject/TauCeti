/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.KrullDimension.Field
import TauCeti.RingTheory.Etale.ProdResidueField
import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Tests for the closed-point factor `A × κ(A)`

Over a regular local ring `A` of dimension at least two, the algebra `A × κ(A)` is finite and
étale over the punctured spectrum, but it is not torsion free and not flat, hence not étale.
Over a normal local domain it is moreover normal. So finite normal algebras which are étale over
the punctured spectrum need not be étale unless they are also torsion free.
-/

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti

variable (A : Type*) [CommRing A] [IsRegularLocalRing A]

/-- *test_closed_point_factor*: `A × κ(A)` is a finite `A`-module. -/
example : Module.Finite A (A × ResidueField A) := inferInstance

/-- *test_closed_point_factor*: `A × κ(A)` is étale at every prime not lying over `𝔪`. -/
example (q : Ideal (A × ResidueField A)) [q.IsPrime] (hq : q.under A ≠ maximalIdeal A) :
    Algebra.IsEtaleAt A q :=
  isEtaleAt_prod_residueField A q hq

/-- *test_closed_point_factor*: over a normal local domain, `A × κ(A)` is normal. -/
example (B : Type*) [CommRing B] [IsLocalRing B] [IsDomain B] [IsIntegrallyClosed B]
    (q : Ideal (B × ResidueField B)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  ⟨isDomain_localization_prod_residueField B q,
    isIntegrallyClosed_localization_prod_residueField B q⟩

/-- *test_closed_point_factor* and *test_closed_point_factor_not_etale*: over a regular local
ring of dimension at least two, `A` is torsion free over itself, but `A × κ(A)` is not, and it is
neither flat nor étale over `A`. -/
example (hd : 2 ≤ ringKrullDim A) :
    Module.IsTorsionFree A A ∧ ¬ Module.IsTorsionFree A (A × ResidueField A) ∧
      ¬ Module.Flat A (A × ResidueField A) ∧ ¬ Algebra.Etale A (A × ResidueField A) := by
  have hA : ¬ IsField A := fun h ↦ by
    rw [ringKrullDim_eq_zero_of_isField h] at hd
    exact absurd hd (by decide)
  exact ⟨inferInstance, not_isTorsionFree_prod_residueField A hA, not_flat_prod_residueField A hA,
    not_etale_prod_residueField A hA⟩

end TauCeti
