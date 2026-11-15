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
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.TripleBond
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Orthogonal
import TauCeti.GroupTheory.Coxeter.Basic

/-!
# The Artin--Tits braid relation for pinned simple Weyl elements of a Chevalley datum

For any Chevalley datum `D` of a valid Dynkin type `t`, the pinned simple Weyl representatives
`D.weylElement (t.simpleIndex ht i) A 1` satisfy the Artin--Tits braid-word relation of
`t.coxeterMatrix` in the actual point group `D.points A` over every commutative ring `A`
(`prod_map_weylElement_braidWord`), without any restriction on characteristic, reducedness, or
weight multiplicities.

The proof combines commutation at orthogonal nodes (`commute_weylElement_simpleIndex`) with the
single-, double-, and triple-bond braid theorems across the four off-diagonal Cartan products
`{0, 1, 2, 3}` of `t.coxeterMatrix`. Together with `weylElement_mul_self`, this supplies the
relations needed to lift `DynkinType.simplyConnectedWeylCoxeterSystem` to the Weyl-subgroup
quotient.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.prod_map_weylElement_braidWord`: the Artin--Tits braid
  relation in `D.points A` for every pair of Bourbaki nodes of `t.coxeterMatrix`.

## References

* J. Tits, *Normalisateurs de tores. I. Groupes de Coxeter étendus*, J. Algebra 4 (1966), 96--116.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 6, Lemma 56.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
* T. A. Springer, *Linear Algebraic Groups*, 2nd ed., §9.3, Proposition 9.3.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

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
