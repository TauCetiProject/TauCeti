/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Lattice
import TauCeti.Algebra.Lie.Presentation.Serre.SingleBond

/-!
# The single-bond braid relation in Chevalley data

Pinned simple Weyl representatives at a single bond satisfy the length-three braid
relation over every commutative ring. The equality holds in the actual point group,
including in bad characteristic and over nonreduced rings, not just in a Weyl quotient.

The rational Serre-operator braid relation is first restricted to the datum's integral
Kostant-stable lattice and then extended to the value ring. This avoids imposing any
restriction on weight multiplicities or choosing a signed permutation weight basis.
`TauCeti.DynkinType.ChevalleyDatum.isSerreSystem_representation` identifies the datum's
rational operators as a Serre system in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum`. The shared word-identity theorem
`TauCeti.DynkinType.ChevalleyDatum.prod_map_weylElement_eq_of_prod_map_weylUnit_eq` in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Lattice` transports Serre-operator word
identities to pinned simple Weyl representatives.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra
open scoped TensorProduct

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Pinned simple Weyl representatives at a single bond satisfy the length-three braid
relation over every commutative value ring. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_one (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1)
    (A : Type*) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 := by
  have h' := D.prod_map_weylElement_eq_of_prod_map_weylUnit_eq [i, j, i] [j, i, j] (by
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using D.isSerreSystem_representation.weylUnit_braid_of_cartan_eq_neg_one
        (i := i) (j := j) (by simp) (by simp) hji hij
        (D.isNilpotent_representation_rootGenerator (.inl i))
        (D.isNilpotent_representation_rootGenerator (.inr i))
        (D.isNilpotent_representation_rootGenerator (.inl j))
        (D.isNilpotent_representation_rootGenerator (.inr j))) A
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, mul_assoc] using h'

end TauCeti.DynkinType.ChevalleyDatum
