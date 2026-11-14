/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic
import TauCeti.Algebra.Lie.Presentation.Serre.DoubleBond

/-!
# The double-bond braid relation in Chevalley data

Pinned simple Weyl representatives at a double bond satisfy the length-four braid
relation over every commutative ring. This is an equality in the actual point group,
not just in a Weyl quotient. It supplies the double-bond relation needed to identify
the quotient of the Weyl subgroup by the torus.

The rational operator identity is
`IsSerreSystem.weylUnit_braid_of_cartan_eq_neg_two`, transferred to `D.points A` by
`ChevalleyDatum.prod_map_weylElement_eq_of_prod_map_weylUnit_eq`. In particular, no
division takes place in the value ring, and no restriction on weight multiplicities,
characteristic or reducedness is needed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Pinned simple Weyl representatives at a double bond satisfy the length-four braid
relation over every commutative value ring. The Cartan matrix is indexed by root, then coroot,
so `j` is the long node and `i` the short node. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_two (i j : Fin t.rank)
    (hji : t.cartanMatrix j i = -2)
    (A : Type*) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 := by
  -- The Lie basis uses the transpose of the displayed Cartan matrix: exchange the two nodes
  -- in the rational operator theorem and take the symmetry of the resulting equality.
  have hij := t.cartanMatrix_eq_neg_one_of_cartanMatrix_le_neg_two i j (by omega)
  simpa [mul_assoc] using D.prod_map_weylElement_eq_of_prod_map_weylUnit_eq
    (l₁ := [i, j, i, j]) (l₂ := [j, i, j, i]) (by
      simpa [mul_assoc] using
        (D.isSerreSystem_representation.weylUnit_braid_of_cartan_eq_neg_two
          (i := j) (j := i) (by simp) (by simp) hij hji
          (D.isNilpotent_representation_rootGenerator (.inl j))
          (D.isNilpotent_representation_rootGenerator (.inr j))
          (D.isNilpotent_representation_rootGenerator (.inl i))
          (D.isNilpotent_representation_rootGenerator (.inr i))).symm) A

end TauCeti.DynkinType.ChevalleyDatum
