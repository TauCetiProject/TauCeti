/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.Algebra

import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Topological algebra kernels and subalgebra closures

The kernel of a continuous algebra homomorphism into a `T₁` space is the preimage of the closed
point `0`, so it is closed. This is the algebra counterpart of Mathlib's
`ContinuousLinearMap.isClosed_ker`. It is stated as an instance so that, for instance, the
quotient of a normed algebra by the kernel of a continuous homomorphism is found to be a normed
algebra.

The set closure of a subalgebra in a semitopological semiring is stable under scalar
multiplication (`Subalgebra.smul_mem_closure`).

## Main results

* `ContinuousAlgHom.isClosed_ker`: the kernel of a continuous algebra homomorphism into a `T₁`
  space is closed.
* `Subalgebra.smul_mem_closure`: scalar multiplication preserves the closure of a subalgebra.
-/

public section

namespace ContinuousAlgHom

/-- The kernel of a continuous algebra homomorphism into a `T₁` space is closed. -/
instance isClosed_ker {R A B : Type*} [CommSemiring R] [Semiring A] [TopologicalSpace A]
    [Semiring B] [TopologicalSpace B] [T1Space B] [Algebra R A] [Algebra R B] (f : A →A[R] B) :
    IsClosed (RingHom.ker f : Set A) :=
  RingHom.isClosed_ker f.continuous

end ContinuousAlgHom

namespace Subalgebra

/-- Scalar multiplication preserves the closure of a subalgebra in a semitopological semiring. -/
theorem smul_mem_closure {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [TopologicalSpace A] [IsSemitopologicalSemiring A] (S : Subalgebra R A)
    {a : A} (ha : a ∈ closure (S : Set A)) (r : R) : r • a ∈ closure (S : Set A) := by
  rw [← topologicalClosure_coe] at ha ⊢
  exact S.topologicalClosure.smul_mem ha r

end Subalgebra
