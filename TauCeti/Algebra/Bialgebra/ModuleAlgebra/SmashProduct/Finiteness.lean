/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.SmashProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finiteness of the smash product

This file provides module-finiteness of the smash product `A # H`
(`TauCeti.LeftModuleAlgebra.SmashProduct`), separated from the core construction so that users
of `SmashProduct.Basic` do not transitively import tensor-product finiteness.

## Main definitions

* `TauCeti.LeftModuleAlgebra.SmashProduct.instModuleFinite`: `μ.SmashProduct` is a finite
  `R`-module whenever `A` and `H` are finite `R`-modules.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §4.1.
* Y. Qi, *Hopfological algebra*, Example 2.8.
-/

public section

namespace TauCeti

namespace LeftModuleAlgebra

universe u v w

section Finite

variable {R : Type u} {H : Type v} {A : Type w}
  [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]

/-- The smash product `A # H` is a finite `R`-module whenever `A` and `H` are finite
`R`-modules. -/
instance SmashProduct.instModuleFinite (μ : LeftModuleAlgebra R H A)
    [Module.Finite R A] [Module.Finite R H] :
    Module.Finite R μ.SmashProduct :=
  Module.Finite.of_surjective μ.tensorEquiv.symm.toLinearMap μ.tensorEquiv.symm.surjective

end Finite

end LeftModuleAlgebra

end TauCeti
