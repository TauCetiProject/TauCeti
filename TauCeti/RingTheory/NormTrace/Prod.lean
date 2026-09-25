/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs

/-!
# Norms of binary products

This file records the norm of an element of a product of two algebras, together with the
description of multiplication on such a product as a `LinearMap.prodMap`.  The dependent
finite-product analogues are in `TauCeti.RingTheory.NormTrace.Pi`, and the trace of a binary
product is Mathlib's `Algebra.trace_prod_apply`.
-/

public section

namespace TauCeti

section Lmul

variable {K : Type*} [CommSemiring K]
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra K A] [Algebra K B]

/-- Multiplication by an element of a product of two algebras acts on the two factors
independently, so as a `K`-linear map it is the product of the multiplications by its
components. -/
theorem Algebra.lmul_prod (x : A × B) :
    Algebra.lmul K (A × B) x =
      LinearMap.prodMap (Algebra.lmul K A x.1) (Algebra.lmul K B x.2) :=
  LinearMap.ext fun _ ↦ rfl

end Lmul

section Norm

variable {K : Type*} [CommRing K]
variable {A B : Type*} [Ring A] [Ring B] [Algebra K A] [Algebra K B]

/-- The norm of an element of a product of two algebras is the product of its component norms. -/
@[simp]
theorem Algebra.norm_prod [Module.Free K A] [Module.Finite K A] [Module.Free K B]
    [Module.Finite K B] (x : A × B) :
    Algebra.norm K x = Algebra.norm K x.1 * Algebra.norm K x.2 := by
  rw [Algebra.norm_apply, Algebra.lmul_prod, LinearMap.det_prodMap, Algebra.norm_apply,
    Algebra.norm_apply]

end Norm

end TauCeti
