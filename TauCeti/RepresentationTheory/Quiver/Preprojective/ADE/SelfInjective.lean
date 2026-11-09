/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.Preprojective.SelfInjective

/-!
# Self-injectivity of the preprojective algebras of finite ADE diagrams

The preprojective algebra of every orientation of a graph isomorphic to a standard Dynkin diagram
(as a simple graph, a finite simply-laced Dynkin diagram) is left and right self-injective, over
every field, characteristic two included. This is the general theorem that finite-dimensional
preprojective algebras are self-injective
(`TauCeti.moduleInjective_preprojectiveAlgebra_of_finiteDimensional`), applied to the
finite-dimensionality of these algebras (`TauCeti.finiteDimensional_preprojectiveAlgebra_of_iso`).

## Main results

* `TauCeti.moduleInjective_preprojectiveAlgebra_of_iso`: left self-injectivity.
* `TauCeti.moduleInjective_op_preprojectiveAlgebra_of_iso`: right self-injectivity.

## References

* S. Brenner, M. C. R. Butler and A. D. King, *Periodic algebras which are almost Koszul*,
  Algebr. Represent. Theory 5 (2002), Section 4.
* C. M. Ringel, *The preprojective algebra of a quiver*, for the finite-Dynkin Frobenius property.
-/

public section

namespace TauCeti

open DoubledQuiver

variable (k : Type*) [Field k]

/-- **The preprojective algebra of every orientation of a graph isomorphic to a standard Dynkin
diagram is left self-injective**, over every field. -/
theorem moduleInjective_preprojectiveAlgebra_of_iso {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G) :
    Module.Injective (preprojectiveAlgebra k (OrientedQuiver G o))
      (preprojectiveAlgebra k (OrientedQuiver G o)) :=
  have := Fintype.ofFinite V
  have := finiteDimensional_preprojectiveAlgebra_of_iso k e o
  moduleInjective_preprojectiveAlgebra_of_finiteDimensional k

/-- **The preprojective algebra of every orientation of a graph isomorphic to a standard Dynkin
diagram is right self-injective**, over every field. -/
theorem moduleInjective_op_preprojectiveAlgebra_of_iso {V : Type*} [Finite V] {G : SimpleGraph V}
    {t : DynkinType} (e : G ≃g diagramGraph t.cartanMatrix) (o : Orientation G) :
    Module.Injective (preprojectiveAlgebra k (OrientedQuiver G o))ᵐᵒᵖ
      (preprojectiveAlgebra k (OrientedQuiver G o)) :=
  have := Fintype.ofFinite V
  have := finiteDimensional_preprojectiveAlgebra_of_iso k e o
  moduleInjective_op_preprojectiveAlgebra_of_finiteDimensional k

end TauCeti
