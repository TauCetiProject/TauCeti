/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm

/-!
# Northcott absolute norm on nonzero ideals

In a Dedekind domain with finite quotients, only finitely many nonzero ideals have
absolute norm at most any bound. The resulting Northcott instance supplies finite cutoff carriers
for counting nonzero ideals over any such domain.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors

/-- The absolute norm on nonzero ideals of a Dedekind domain with finite quotients is Northcott.
For nonzero ideals it equals quotient cardinality, whose sublevel sets are finite by
`Ring.HasFiniteQuotients.finite_cardQuot_le`. -/
instance instNorthcottAbsNormNonZeroDivisors {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Ring.HasFiniteQuotients R] :
    Northcott (fun I : (Ideal R)⁰ ↦ Ideal.absNorm (I : Ideal R)) := by
  constructor
  intro B
  have hfinite : {I : (Ideal R)⁰ | (I : Ideal R).cardQuot ≤ B}.Finite :=
    (Ring.HasFiniteQuotients.finite_cardQuot_le (S := R) B).preimage
      Subtype.val_injective.injOn
  refine hfinite.subset fun I hI ↦ ?_
  simpa only [Set.mem_ofPred_eq,
    Ideal.absNorm_of_ne_bot (mem_nonZeroDivisors_iff_ne_zero.mp I.2)] using hI

end TauCeti
