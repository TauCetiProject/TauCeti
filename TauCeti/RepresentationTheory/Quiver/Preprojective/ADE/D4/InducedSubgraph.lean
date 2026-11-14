/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.InducedSubgraph

/-!
# Characteristic-two cyclic classes from induced `D₄` subdiagrams

An induced copy of `D₄` in a finite graph gives a quotient of signless preprojective algebras.
In characteristic two, lift the degree-four cyclic class of `D₄` along this quotient. Its lift
cannot be a sum of commutators, since algebra homomorphisms preserve sums of commutators.
This applies in particular to the branching vertices of the finite `D` and `E` diagrams.
The copy must be induced: an arbitrary graph homomorphism does not give this quotient.

Products use later-factor-first order. The lifted class traverses two distinct backtracks at
the branch vertex. No field hypothesis is required, only a nontrivial commutative ring with
`2 = 0`. Quotient carriers use the neighborhood enumerations `Fintype.ofFinite`.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, for the bad-characteristic cyclic classes.
-/

public section

namespace TauCeti

open DoubledQuiver

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [CommRing k] {V : Type*} [Finite V] {G : SimpleGraph V}

/-- An induced `D₄` subdiagram detects a nonzero degree-four cyclic class in characteristic
two. This holds over every nontrivial commutative coefficient ring. -/
theorem exists_mem_signlessPreprojectiveGrade_four_notMem_commutatorSubmodule_of_d4_embedding
    [Nontrivial k] (f : zigzagD4Graph ↪g G) (h2 : (2 : k) = 0) :
    ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 4 ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_embedding k f
    ⟨signlessWord k zigzagD4Graph [1, 2, 1, 0, 1],
      signlessWord_D4_cyclicWord_mem_grade_four k,
      signlessWord_D4_cyclicWord_not_mem_commutatorSubmodule k h2⟩

end TauCeti
