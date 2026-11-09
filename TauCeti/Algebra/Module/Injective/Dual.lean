/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.Algebra.Module.Injective.Coinduced

/-!
# The dual regular module is injective

For an algebra `A` over a field `k`, the dual of the right regular module is an injective
left `A`-module. Together with its cogenerator property, this provides injective modules
containing finite-dimensional modules, without a self-injectivity assumption on the algebra.

The action on the dual is specified through an equivariant linear equivalence, rather than
installed as a global instance on all duals. This follows the convention of
`TauCeti.LinearAlgebra.Dual.RightAction`.

It is the case `V = k` of the injectivity of the coinduced module `Hom_k(A, V)`, see
`TauCeti.Algebra.Module.Injective.Coinduced`.

## Main results

* `LinearEquiv.moduleInjective_of_dual_regular`: the dual of the right regular module is
  injective.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, Section I.5.
-/

public section

namespace LinearEquiv

variable {k A Q : Type*}

variable [Field k] [Ring A] [Algebra k A] [AddCommGroup Q] [Module A Q] [Module k Q]

/-- The dual of the right regular module, with action `(a • φ) x = φ (x * a)`, is an
injective left module over any algebra over a field. -/
theorem moduleInjective_of_dual_regular (e : Q ≃ₗ[k] Module.Dual k A)
    (he : ∀ (a : A) (q : Q) (x : A), e (a • q) x = e q (x * a)) :
    Module.Injective A Q :=
  e.moduleInjective_of_coinduced he

end LinearEquiv
