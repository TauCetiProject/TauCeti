/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# Orthogonal simple roots

Distinct simple roots with zero Cartan pairing do not sum to a root. This is the
root-system input to centralization of orthogonal rank-one Chevalley subgroups.
The proof uses Mathlib's simple-root string length and linear independence lemmas.
-/

public section

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [Finite ι]

/-- Distinct simple roots with zero Cartan pairing do not sum to a root. -/
theorem root_add_root_notMem_range_of_pairingIn_eq_zero (b : P.Base)
    {i j : b.support} (hij : i ≠ j) (hpair : P.pairingIn ℤ i j = 0) :
    P.root i + P.root j ∉ Set.range P.root := by
  have htop : P.chainTopCoeff j i = 0 := by
    apply Int.natCast_inj.mp
    simpa only [hpair, neg_zero, Nat.cast_zero] using b.chainTopCoeff_eq_of_ne hij.symm
  exact (P.chainTopCoeff_eq_zero_iff.mp htop).resolve_left
    (not_not.mpr (b.linearIndependent_pair_of_ne hij.symm))

end RootPairing.Base
