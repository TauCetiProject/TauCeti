/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.RingTheory.Frobenius
import TauCeti.GroupTheory.GroupAction.Period

/-!
# Prime parity for the product of Frobenius and conjugation

`IsArithFrobAt.mul_zpow_smul_eq_ite` distinguishes the even and odd translates of a prime under
the product of a Frobenius element and a commuting conjugation. This classifies the two primes
underlying a marked Frobenius cycle, including when the primes are read by an inverse action.
The inputs are
`IsArithFrobAt.mem_stabilizer` and `MulAction.zpow_smul_eq_ite_of_sq_smul_eq`.

The signed Frobenius convention is that of `New.Data.IsMarked.exists_frobeniusCycle` in
`grh/src/New/UpperBound/Divisibility/MarkOperator.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean)
(revision `72fead1`, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open scoped Pointwise

namespace IsArithFrobAt

/-- Let `σ` be an arithmetic Frobenius at `Q` and let `c ^ 2` fix `Q`. If `c` and `σ` commute
at `Q`, the even powers of `c * σ` fix `Q`, and the odd powers send it to `c • Q`. -/
theorem mul_zpow_smul_eq_ite {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S] {Q : Ideal S} [Q.IsPrime]
    {σ c : G} (hσ : IsArithFrobAt R σ Q) (hcσ : (σ * c) • Q = (c * σ) • Q)
    (hc : c ^ 2 • Q = Q) (n : ℤ) :
    (c * σ) ^ n • Q = if Even n then Q else c • Q := by
  have hfix : σ • Q = Q := MulAction.mem_stabilizer_iff.mp hσ.mem_stabilizer
  have hfirst : (c * σ) • Q = c • Q := by rw [mul_smul, hfix]
  have hconj : σ • (c • Q) = c • Q := by rwa [← mul_smul, hcσ]
  have hsecond : (c * σ) • (c • Q) = Q := by rw [mul_smul, hconj, ← mul_smul, ← pow_two, hc]
  have hsq : (c * σ) ^ 2 • Q = Q := by rw [pow_two, mul_smul, hfirst, hsecond]
  rw [MulAction.zpow_smul_eq_ite_of_sq_smul_eq _ hsq, hfirst]

end IsArithFrobAt
