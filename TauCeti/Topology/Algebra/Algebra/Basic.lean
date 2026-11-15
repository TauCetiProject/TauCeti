/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.Algebra

/-!
# Kernels of continuous algebra homomorphisms

The kernel of a continuous algebra homomorphism into a `T₁` space is the preimage of the closed
point `0`, so it is closed. This is the algebra counterpart of Mathlib's
`ContinuousLinearMap.isClosed_ker`. It is stated as an instance so that, for instance, the
quotient of a normed algebra by the kernel of a continuous homomorphism is found to be a normed
algebra.

## Main results

* `ContinuousAlgHom.isClosed_ker`: the kernel of a continuous algebra homomorphism into a `T₁`
  space is closed.
-/

public section

namespace ContinuousAlgHom

/-- The kernel of a continuous algebra homomorphism into a `T₁` space is closed. -/
instance isClosed_ker {R A B : Type*} [CommSemiring R] [Semiring A] [TopologicalSpace A]
    [Semiring B] [TopologicalSpace B] [T1Space B] [Algebra R A] [Algebra R B] (f : A →A[R] B) :
    IsClosed (RingHom.ker f : Set A) :=
  isClosed_singleton.preimage f.continuous

end ContinuousAlgHom
