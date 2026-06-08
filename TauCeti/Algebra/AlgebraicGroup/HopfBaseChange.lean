/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Base change of Hopf algebras

This file records a small API for scalar extension of Hopf algebras.  Mathlib already supplies
the Hopf algebra structure on a tensor product of Hopf algebras; specializing one factor to the
base ring gives the scalar extension `S ⊗[R] A` of an `R`-Hopf algebra `A` along `R → S`.

The reductive-groups roadmap needs this form of base change in Layer 0, both for changing the
base field of an affine group scheme and for comparing functors of points before and after base
change.  This file gives the construction the roadmap-facing name `BaseChange`; the Hopf,
bialgebra, and coalgebra API is Mathlib's tensor-product API, including
`TensorProduct.antipode_def`, `TensorProduct.counit_tmul`, `TensorProduct.comul_tmul`,
`Algebra.TensorProduct.includeRight`, and `AlgHom.liftEquiv`.

## Main declarations

* `HopfAlgebra.BaseChange`: the scalar extension `S ⊗[R] A` of an `R`-algebra, carrying the
  tensor-product Hopf algebra structure when `A` is a Hopf algebra over `R`.

## References

This supports the "Base change. `K ⊗[k] A` as a Hopf algebra over `K`" item in Layer 0 of the
Tau Ceti reductive-groups roadmap.  The underlying tensor-product Hopf algebra instance is due to
Amelia Livingston and Andrew Yang in Mathlib.
-/

open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The scalar extension of an `R`-algebra `A` along `R → S`.  When `A` is a Hopf algebra over
`R`, Mathlib's tensor-product Hopf algebra instance equips this algebra with a Hopf algebra
structure over `S`. -/
abbrev BaseChange [Semiring A] [Algebra R A] :=
  S ⊗[R] A

end HopfAlgebra

end TauCeti
