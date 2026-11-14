/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.DynkinType
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.DoubleBond
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Orthogonal
import TauCeti.Algebra.Lie.Presentation.Serre.TripleBond
import TauCeti.GroupTheory.Coxeter.Basic

/-!
# The triple-bond and general Artin--Tits braid relations in Chevalley data

Pinned simple Weyl representatives at a triple bond satisfy the length-six braid relation
over every commutative ring. Together with orthogonality at unjoined nodes and the single-
and double-bond braid relations, this proves the Artin--Tits braid relation
`prod_map_weylElement_braidWord` for every pair of Bourbaki nodes in the actual point group
`D.points A` of any Chevalley datum.

The triple-bond identity transfers the rational Serre-operator equality
`IsSerreSystem.weylUnit_braid_of_cartan_eq_neg_three` to `D.points A` via
`ChevalleyDatum.prod_map_weylElement_eq_of_prod_map_weylUnit_eq`, avoiding any division in
`A` or restriction on the characteristic, reducedness, or weight multiplicities. The unified
braid-word theorem combines the four off-diagonal Cartan products `{0, 1, 2, 3}` of
`t.coxeterMatrix`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.weylElement_braid_of_cartanMatrix_eq_neg_three`:
  the length-six braid relation in `D.points A` at a triple bond.
* `TauCeti.DynkinType.ChevalleyDatum.prod_map_weylElement_braidWord`: the Artin--Tits
  braid relation in `D.points A` for every pair of nodes of `t.coxeterMatrix`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 9.3.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Pinned simple Weyl representatives at a triple bond satisfy the length-six braid
relation over every commutative value ring. The Cartan matrix is indexed by root, then coroot,
so `j` is the long node and `i` the short node. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_three (i j : Fin t.rank)
    (hji : t.cartanMatrix j i = -3)
    (A : Type*) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 := by
  -- The Lie basis uses the transpose of the displayed Cartan matrix: exchange the two nodes
  -- in the rational operator theorem and take the symmetry of the resulting equality.
  have hij := t.cartanMatrix_eq_neg_one_of_cartanMatrix_le_neg_two i j (by omega)
  simpa [mul_assoc] using D.prod_map_weylElement_eq_of_prod_map_weylUnit_eq
    (l₁ := [i, j, i, j, i, j]) (l₂ := [j, i, j, i, j, i]) (by
      simpa [mul_assoc] using
        (D.isSerreSystem_representation.weylUnit_braid_of_cartan_eq_neg_three
          (i := j) (j := i) (by simp) (by simp) hij hji
          (D.isNilpotent_representation_rootGenerator (.inl j))
          (D.isNilpotent_representation_rootGenerator (.inr j))
          (D.isNilpotent_representation_rootGenerator (.inl i))
          (D.isNilpotent_representation_rootGenerator (.inr i))).symm) A

/-- **The Artin--Tits braid relation for pinned simple Weyl elements.** For any pair of
Bourbaki nodes `i` and `j`, the alternating words of length `t.coxeterMatrix i j` in
`n_i(1)` and `n_j(1)` are equal in the actual point group `D.points A` over every
commutative ring `A`. -/
theorem prod_map_weylElement_braidWord (i j : Fin t.rank) (A : Type*) [CommRing A] :
    ((CoxeterSystem.braidWord t.coxeterMatrix i j).map
        fun k => D.weylElement (t.simpleIndex ht k) A 1).prod =
      ((CoxeterSystem.braidWord t.coxeterMatrix j i).map
        fun k => D.weylElement (t.simpleIndex ht k) A 1).prod := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, t.coxeterMatrix.symmetric j i,
    TauCeti.prod_map_alternatingWord, TauCeti.prod_map_alternatingWord, coxeterMatrix_apply]
  rcases t.cartanMatrix_mul_cartanMatrix_mem_of_ne hij with hp | hp | hp | hp
  · have hzero : t.cartanMatrix i j = 0 :=
      (mul_eq_zero.mp hp).elim id (t.cartanMatrix_apply_eq_zero_iff_symm i j).mpr
    simpa [hp] using (D.commute_weylElement_simpleIndex A i j hzero 1 1).eq
  · rw [hp, coxeterOrder_one]
    rcases t.cartanMatrix_offDiag_of_mul_eq hij zero_lt_one hp with ⟨h1, h2⟩ | ⟨h2, h1⟩ <;>
      simpa [Nat.even_iff, mul_assoc] using
        (D.weylElement_braid_of_cartanMatrix_eq_neg_one i j h1 h2 A).symm
  · rw [hp, coxeterOrder_two]
    rcases t.cartanMatrix_offDiag_of_mul_eq hij zero_lt_two hp with ⟨_, hji⟩ | ⟨_, hij2⟩
    · simpa [Nat.even_iff, pow_two, mul_assoc] using
        D.weylElement_braid_of_cartanMatrix_eq_neg_two i j hji A
    · simpa [Nat.even_iff, pow_two, mul_assoc] using
        (D.weylElement_braid_of_cartanMatrix_eq_neg_two j i hij2 A).symm
  · rw [Set.mem_singleton_iff] at hp
    rw [hp, coxeterOrder_three]
    rcases t.cartanMatrix_offDiag_of_mul_eq hij zero_lt_three hp with ⟨_, hji⟩ | ⟨_, hij3⟩
    · simpa [Nat.even_iff, pow_three, mul_assoc] using
        D.weylElement_braid_of_cartanMatrix_eq_neg_three i j hji A
    · simpa [Nat.even_iff, pow_three, mul_assoc] using
        (D.weylElement_braid_of_cartanMatrix_eq_neg_three j i hij3 A).symm

end TauCeti.DynkinType.ChevalleyDatum
