/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Lattice
import TauCeti.Algebra.Lie.Presentation.Serre.TripleBond

/-!
# The triple-bond braid relation in Chevalley data

Pinned simple Weyl representatives at a triple bond satisfy the length-six braid
relation in the actual points of every Chevalley datum over every commutative ring.
In particular the equality holds in characteristics two and three and over nonreduced
rings, without division by the root-string factorials in those rings.

The rational identity `TauCeti.IsSerreSystem.weylUnit_braid_of_cartan_eq_neg_three`
applies to the represented Serre system
`TauCeti.DynkinType.ChevalleyDatum.isSerreSystem_representation` in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum`. It is restricted to the admissible
lattice and then base changed using
`TauCeti.DynkinType.ChevalleyDatum.prod_map_weylElement_eq_of_prod_map_weylUnit_eq` in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Lattice`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Pinned Weyl representatives at a triple bond satisfy the length-six braid relation
in the actual point group over every commutative value ring. The Cartan convention has
roots as rows, so `i` is the long node. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_three (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -3)
    (A : Type*) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 := by
  have hji := t.cartanMatrix_eq_neg_one_of_cartanMatrix_le_neg_two j i (by omega)
  have h' := D.prod_map_weylElement_eq_of_prod_map_weylUnit_eq
    [i, j, i, j, i, j] [j, i, j, i, j, i] (by
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, mul_assoc] using
        (D.isSerreSystem_representation.weylUnit_braid_of_cartan_eq_neg_three
          (i := j) (j := i) (by simp) (by simp) hij hji
          (D.isNilpotent_representation_rootGenerator (.inl j))
          (D.isNilpotent_representation_rootGenerator (.inr j))
          (D.isNilpotent_representation_rootGenerator (.inl i))
          (D.isNilpotent_representation_rootGenerator (.inr i))).symm) A
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, mul_assoc] using h'

end TauCeti.DynkinType.ChevalleyDatum
