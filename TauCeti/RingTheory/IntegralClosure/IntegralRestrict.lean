/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import TauCeti.RingTheory.Ideal.Operations

/-!
# The integral trace on extended ideals

Mathlib's `Algebra.intTrace A B` is the trace of a finite extension of integrally closed domains
`B / A`, restricted from the fraction fields to the rings themselves. This file records that it
is compatible with the ideals of the base: the trace carries the extended ideal `p · B` of an
ideal `p` of `A` back into `p`. This is the case of the trace of the general fact
`LinearMap.apply_mem_of_mem_smul_top`, that an `A`-linear functional carries `p • B` into `p`,
since `p • B` is the extended ideal `p · B`.

This is the elementary half of the computation of the trace of an ideal of `B`. The other half,
which reads the exact image off the different ideal, is in
`TauCeti.RingTheory.DedekindDomain.Different.Trace`.

## Main results

* `Algebra.intTrace_mem_of_mem_map`: `Tr(p · B) ⊆ p`.
-/

public section

namespace Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
variable [Module.Finite A B] [Module.IsTorsionFree A B]

/-- The integral trace carries the extended ideal `p · B` of an ideal `p` of the base ring back
into `p`: it is an `A`-linear functional on `B`, and `p · B = p • B`. -/
theorem intTrace_mem_of_mem_map {p : Ideal A} {x : B} (hx : x ∈ p.map (algebraMap A B)) :
    intTrace A B x ∈ p :=
  (intTrace A B).apply_mem_of_mem_smul_top (by rwa [Ideal.smul_top_eq_map])

end Algebra
