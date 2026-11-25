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
# Topological algebra basics

This file collects basic topological algebra facts:

* `ContinuousAlgHom.isClosed_ker`: the kernel of a continuous algebra homomorphism into a `T₁`
  space is closed (the algebra counterpart of `ContinuousLinearMap.isClosed_ker`, stated as an
  instance so that quotients of normed algebras by kernels of continuous homomorphisms inherit
  normed algebra structures).
* `Algebra.mem_elemental_iff`: membership in `Algebra.elemental R w` is equivalent to membership
  in the topological closure of `Algebra.adjoin R {w}`.
-/

public section

namespace ContinuousAlgHom

/-- The kernel of a continuous algebra homomorphism into a `T₁` space is closed. -/
instance isClosed_ker {R A B : Type*} [CommSemiring R] [Semiring A] [TopologicalSpace A]
    [Semiring B] [TopologicalSpace B] [T1Space B] [Algebra R A] [Algebra R B] (f : A →A[R] B) :
    IsClosed (RingHom.ker f : Set A) :=
  RingHom.isClosed_ker f.continuous

end ContinuousAlgHom

namespace Algebra

/-- Membership in `Algebra.elemental R w` is equivalent to membership in the topological closure
of `Algebra.adjoin R {w}`. -/
theorem mem_elemental_iff {R A : Type*} [CommSemiring R] [Semiring A] [TopologicalSpace A]
    [Algebra R A] [IsSemitopologicalSemiring A] {w x : A} :
    x ∈ elemental R w ↔ x ∈ closure (adjoin R {w} : Set A) := by
  rw [← SetLike.mem_coe, elemental, Subalgebra.topologicalClosure_coe]

end Algebra
