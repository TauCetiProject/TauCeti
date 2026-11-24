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

/-!
# The Coxeter braid relations of Chevalley Weyl representatives

For a Chevalley datum of type `t` and any two nodes `i, j`, the pinned simple Weyl
representatives `nᵢ = nᵢ(1)` and `nⱼ = nⱼ(1)` satisfy the braid relation whose length is the
entry of the Coxeter matrix `TauCeti.DynkinType.coxeterMatrix t` at `(i, j)`: the alternating
products of that length starting with `nᵢ` and with `nⱼ` agree. Written with Mathlib's
`CoxeterSystem.braidWord`, this is the form of the braid relations in the Coxeter
presentation of the Weyl group. It holds in the actual point group over every commutative
ring, not just in a Weyl quotient.

The braid relations are the lengths `2, 3, 4, 6` at the Cartan products `0, 1, 2, 3`, proved
in `TauCeti.Algebra.AlgebraicGroup.Chevalley.Orthogonal` and the files
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic`, `Braid.DoubleBond` and
`Braid.TripleBond`, and `TauCeti.DynkinType.coxeterMatrix_apply` matches each Coxeter entry to
its bond. The squares `nᵢ(1)² = hᵢ(-1)` are in general nontrivial torus points, so these are the
braid relations of the Coxeter presentation, not its relations `sᵢ² = 1`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
* J. Tits, *Normalisateurs de tores I. Groupes de Coxeter étendus*, J. Algebra **4** (1966),
  96--116.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- **The braid relations of the pinned Weyl representatives.** For any two nodes `i, j`, the
Weyl words of the two braid words of the Coxeter matrix at `(i, j)`, that is the alternating
products of `nᵢ(1)` and `nⱼ(1)` of length the Coxeter matrix entry, one ending with `nⱼ(1)` and
the other with `nᵢ(1)`, are equal in the points of the datum over every commutative ring. This
is the analogue of `CoxeterSystem.wordProd_braidWord_eq` for the Weyl representatives. -/
theorem weylWord_braidWord_eq (i j : Fin t.rank) (A : Type*) [CommRing A] :
    ((CoxeterSystem.braidWord t.coxeterMatrix i j).map
        fun k => D.weylElement (t.simpleIndex ht k) A 1).prod =
      ((CoxeterSystem.braidWord t.coxeterMatrix j i).map
        fun k => D.weylElement (t.simpleIndex ht k) A 1).prod := by
  rcases eq_or_ne i j with rfl | hne
  · rfl
  -- Swapping `i` and `j` swaps the two braid words, so the case `t.cartanMatrix i j ≤ -2` is
  -- the mirror image of the case `t.cartanMatrix j i ≤ -2` handled below.
  wlog hij : -1 ≤ t.cartanMatrix i j generalizing i j
  · have hji := t.cartanMatrix_eq_neg_one_of_cartanMatrix_le_neg_two j i (by omega)
    exact (this j i hne.symm (by omega)).symm
  have hmem := t.cartanMatrix_mul_cartanMatrix_mem_of_ne hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hi := t.cartanMatrix_apply_le_zero_of_ne hne
  have hj := t.cartanMatrix_apply_le_zero_of_ne hne.symm
  -- Once the Coxeter entry is a numeral `m`, both braid words can be written out.
  have hword (m : ℕ) (hm : coxeterOrder (t.cartanMatrix i j * t.cartanMatrix j i) = m)
      (h : ((CoxeterSystem.alternatingWord i j m).map
          fun k => D.weylElement (t.simpleIndex ht k) A 1).prod =
        ((CoxeterSystem.alternatingWord j i m).map
          fun k => D.weylElement (t.simpleIndex ht k) A 1).prod) :
      ((CoxeterSystem.braidWord t.coxeterMatrix i j).map
          fun k => D.weylElement (t.simpleIndex ht k) A 1).prod =
        ((CoxeterSystem.braidWord t.coxeterMatrix j i).map
          fun k => D.weylElement (t.simpleIndex ht k) A 1).prod := by
    simpa only [CoxeterSystem.braidWord, t.coxeterMatrix_apply, mul_comm (t.cartanMatrix j i),
      hm] using h
  -- A double or triple bond has a long node, at which the opposite entry is `-1`.
  by_cases hji : t.cartanMatrix j i ≤ -2
  · have hij := t.cartanMatrix_eq_neg_one_of_cartanMatrix_le_neg_two i j hji
    rcases (by rw [hij] at hmem; omega : t.cartanMatrix j i = -2 ∨ t.cartanMatrix j i = -3)
      with h | h
    · refine hword 4 (by simp [hij, h]) ?_
      simpa only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.nil_append,
        List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_assoc] using
        D.weylElement_braid_of_cartanMatrix_eq_neg_two i j h A
    · refine hword 6 (by simp [hij, h]) ?_
      simpa only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.nil_append,
        List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_assoc] using
        D.weylElement_braid_of_cartanMatrix_eq_neg_three i j h A
  -- Otherwise both entries are `0`, at orthogonal nodes, or both are `-1`, at a single bond.
  rcases (by omega : t.cartanMatrix i j = 0 ∨ t.cartanMatrix i j = -1) with h | h
  · refine hword 2 (by simp [h]) ?_
    simpa only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.nil_append,
      List.map_append, List.prod_append, List.map_singleton, List.prod_singleton] using
      (D.commute_weylElement_simpleIndex A i j h 1 1).eq
  · have h' : t.cartanMatrix j i = -1 := by
      have := (t.cartanMatrix_apply_eq_zero_iff_symm i j).not.mp (by omega)
      omega
    refine hword 3 (by simp [h, h']) ?_
    simpa only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.nil_append,
      List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_assoc] using
      (D.weylElement_braid_of_cartanMatrix_eq_neg_one i j h h' A).symm

end TauCeti.DynkinType.ChevalleyDatum
