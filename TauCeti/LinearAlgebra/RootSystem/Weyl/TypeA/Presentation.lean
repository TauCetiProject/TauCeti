/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Restriction
public import TauCeti.GroupTheory.Perm.Coxeter
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Length
public import TauCeti.LinearAlgebra.RootSystem.LongestElement

/-!
# The Weyl group of type `Aₙ` is the symmetric group

Let `P` be a finite reduced crystallographic root pairing over a commutative domain of
characteristic zero, and let `b` be a base of `P` of Cartan type `Aₙ`. This file identifies the
Weyl group of `P` with `Equiv.Perm (Fin (n + 1))`, marking the simple reflections: once the simple
roots are labelled by the nodes `0, …, n - 1` of the chain `Aₙ`, compatibly with the Cartan
matrices, the reflection in the `k`-th simple root goes to the adjacent transposition `(k k+1)`.

The identification compares two presentations of the same Coxeter group. The Weyl group is a
Coxeter system on its simple reflections, with the Coxeter matrix read off the Cartan matrix of
`b` (`TauCeti.weylCoxeterSystem`), and a labelling matching the Cartan matrix of `b` with that of
`Aₙ` matches this Coxeter matrix with `CoxeterMatrix.A n`
(`TauCeti.coxeterMatrixOfBase_eq_coxeterMatrix_reindex`). The symmetric group is a Coxeter system
on the adjacent transpositions with that same matrix (`TauCeti.permCoxeterSystem`). So the
relations of the adjacent transpositions are inherited from the presentation of the Weyl group,
rather than deduced from a count of group orders, and no spanning hypothesis on `P` is needed.
The rank-zero case `A₀` is included: the base is empty and both groups are trivial.

The marking turns combinatorics of the Weyl group into combinatorics of permutations. The length
of a Weyl group element, which is its number of inversions among the positive roots, is the
number of inversions of the corresponding permutation, and a simple root is sent to a positive
root exactly when the permutation keeps the two letters of the corresponding adjacent
transposition in order. Counting the inversions of the order-reversing permutation then gives
`n (n + 1) / 2` positive roots and `n (n + 1)` roots in all.

## Main definitions

* `RootPairing.typeAWeylGroupEquiv`: the marked isomorphism from the Weyl group of a root pairing
  with a base labelled as `Aₙ` to `Equiv.Perm (Fin (n + 1))`.

## Main results

* `RootPairing.typeAWeylGroupEquiv_ofIdx`: it sends the reflection in the simple root labelled `k`
  to the adjacent transposition `(k k+1)`.
* `RootPairing.ncard_inversions_eq_card_typeAWeylGroupEquiv`: the number of inversions of a Weyl
  group element is the number of inversions of its permutation.
* `RootPairing.isPos_weylGroupToPerm_iff_typeAWeylGroupEquiv`: the image of a simple root is
  positive exactly when the permutation preserves the order of the two corresponding letters.
* `RootPairing.nonempty_weylGroup_mulEquiv_perm_of_typeA`: **the Weyl group of a root pairing with
  a base of Cartan type `Aₙ` is isomorphic to the symmetric group on `n + 1` letters.**
* `RootPairing.card_weylGroup_of_hasCartanType_A`: its order is `(n + 1)!`.
* `RootPairing.ncard_posRoots_of_hasCartanType_A` and `RootPairing.natCard_eq_of_hasCartanType_A`:
  there are `n (n + 1) / 2` positive roots and `n (n + 1)` roots.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29 (1990), Section 1.7, Corollary, and Section 2.10, type `A`.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, §1, no. 5, and Plate I.
-/

public section

open Finset TauCeti

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base) {n : ℕ} (e : b.support ≃ Fin n)
  (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))

omit [Finite ι] [CharZero R] [IsDomain R] [P.IsReduced] in
variable {P b} in
/-- A base of Cartan type `Aₙ` has a labelling of its simple roots by `Fin n` matching its Cartan
matrix with `CartanMatrix.A n`. This is `TauCeti.hasCartanType_iff`, with the rank and the standard
Cartan matrix of `DynkinType.A n` rewritten to `n` and `CartanMatrix.A n`. -/
private theorem exists_cartanMatrix_eq_A (h : HasCartanType P b (.A n)) :
    ∃ e : b.support ≃ Fin n, ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j) := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b _).mp h
  rw [DynkinType.cartanMatrix_A] at he
  exact ⟨e, he⟩

omit [P.IsReduced] in
include he in
/-- A labelling of the simple roots matching the Cartan matrix of the base with that of `Aₙ`
matches the Coxeter matrix of the base with `CoxeterMatrix.A n`. -/
private theorem coxeterMatrixOfBase_eq_coxeterMatrixA (i j : b.support) :
    coxeterMatrixOfBase P b i j = CoxeterMatrix.A n (e i) (e j) := by
  have hA : ∀ i j, b.cartanMatrix i j = (DynkinType.A n).cartanMatrix (e i) (e j) := by
    rw [DynkinType.cartanMatrix_A]
    exact he
  rw [coxeterMatrixOfBase_eq_coxeterMatrix_reindex (t := .A n) e hA, DynkinType.coxeterMatrix_A]
  simpa using CoxeterMatrix.reindex_apply (e := e.symm) (M := CoxeterMatrix.A n) i j

/-- **The marked isomorphism from a Weyl group of type `Aₙ` to the symmetric group.** Given a
labelling `e` of the simple roots of `b` by the nodes of the chain `Aₙ` under which the Cartan
matrix of `b` is the standard Cartan matrix of type `Aₙ`, this is the isomorphism from the Weyl
group to `Equiv.Perm (Fin (n + 1))` sending the reflection in the simple root `i` to the adjacent
transposition `(e i, e i + 1)` (`RootPairing.typeAWeylGroupEquiv_ofIdx`). It depends on the
labelling `e`, which a base of Cartan type `Aₙ` determines only up to the symmetry of the chain.

Both directions are the homomorphisms `CoxeterSystem.parabolicHom` between the Weyl Coxeter
system `TauCeti.weylCoxeterSystem` and `TauCeti.permCoxeterSystem`, along `e` and `e.symm`. -/
noncomputable def typeAWeylGroupEquiv : P.weylGroup ≃* Equiv.Perm (Fin (n + 1)) :=
  MonoidHom.toMulEquiv
    ((weylCoxeterSystem P b).parabolicHom (permCoxeterSystem (n + 1)) (f := e)
      (coxeterMatrixOfBase_eq_coxeterMatrixA P b e he))
    ((permCoxeterSystem (n + 1)).parabolicHom (weylCoxeterSystem P b) (f := e.symm)
      fun i j ↦ by
        -- The matrix `CoxeterMatrix.A (n + 1 - 1)` of `permCoxeterSystem (n + 1)` reduces to
        -- `CoxeterMatrix.A n`.
        have h := (coxeterMatrixOfBase_eq_coxeterMatrixA P b e he (e.symm i) (e.symm j)).symm
        rw [e.apply_symm_apply, e.apply_symm_apply] at h
        exact h)
    ((weylCoxeterSystem P b).ext_simple fun i ↦ by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, CoxeterSystem.parabolicHom_simple,
        e.symm_apply_apply])
    ((permCoxeterSystem (n + 1)).ext_simple fun i ↦ by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, CoxeterSystem.parabolicHom_simple,
        e.apply_symm_apply])

/-- The marked isomorphism is the homomorphism `CoxeterSystem.parabolicHom` along `e`. -/
private theorem coe_typeAWeylGroupEquiv :
    ⇑(P.typeAWeylGroupEquiv b e he) = (weylCoxeterSystem P b).parabolicHom
      (permCoxeterSystem (n + 1)) (f := e) (coxeterMatrixOfBase_eq_coxeterMatrixA P b e he) := by
  rw [typeAWeylGroupEquiv, MonoidHom.toMulEquiv_apply]

/-- The marked isomorphism sends the reflection in the simple root `i` to the adjacent
transposition of the letters `e i` and `e i + 1`. -/
@[simp]
theorem typeAWeylGroupEquiv_ofIdx (i : b.support) :
    P.typeAWeylGroupEquiv b e he (weylGroup.ofIdx P (i : ι)) =
      Equiv.swap (e i).castSucc (e i).succ := by
  rw [coe_typeAWeylGroupEquiv, ← weylCoxeterSystem_simple, CoxeterSystem.parabolicHom_simple,
    permCoxeterSystem_simple, BraidGroup.transposition_eq_swap]
  congr 1 <;> ext <;> simp

/-- The inverse of the marked isomorphism sends the adjacent transposition of the letters `k` and
`k + 1` to the reflection in the simple root labelled `k`. -/
@[simp]
theorem typeAWeylGroupEquiv_symm_swap (k : Fin n) :
    (P.typeAWeylGroupEquiv b e he).symm (Equiv.swap k.castSucc k.succ) =
      weylGroup.ofIdx P ((e.symm k : b.support) : ι) := by
  rw [MulEquiv.symm_apply_eq, typeAWeylGroupEquiv_ofIdx, Equiv.apply_symm_apply]

/-- **The marked isomorphism matches lengths with permutation inversions**: the number of positive
roots made negative by a Weyl group element is the number of pairs of letters whose order its
permutation reverses. -/
theorem ncard_inversions_eq_card_typeAWeylGroupEquiv (w : P.weylGroup) :
    (inversions P b w).ncard = #{p : Fin (n + 1) × Fin (n + 1) |
      p.1 < p.2 ∧ P.typeAWeylGroupEquiv b e he w p.2 < P.typeAWeylGroupEquiv b e he w p.1} := by
  rw [← permCoxeterSystem_length_eq_card_inversion, coe_typeAWeylGroupEquiv,
    CoxeterSystem.length_parabolicHom, length_weylCoxeterSystem_eq]

/-- **The sign of the image of a simple root is read off the permutation**: a Weyl group element
sends the simple root `i` to a positive root exactly when its permutation keeps the letters `e i`
and `e i + 1` in order. -/
theorem isPos_weylGroupToPerm_iff_typeAWeylGroupEquiv (w : P.weylGroup) (i : b.support) :
    b.IsPos (P.weylGroupToPerm w (i : ι)) ↔
      P.typeAWeylGroupEquiv b e he w (e i).castSucc <
        P.typeAWeylGroupEquiv b e he w (e i).succ := by
  set σ := P.typeAWeylGroupEquiv b e he w with hσ
  have hdesc : (permCoxeterSystem (n + 1)).IsRightDescent σ (e i) ↔
      (weylCoxeterSystem P b).IsRightDescent w i := by
    rw [CoxeterSystem.IsRightDescent, CoxeterSystem.IsRightDescent, hσ, coe_typeAWeylGroupEquiv,
      ← CoxeterSystem.parabolicHom_simple (weylCoxeterSystem P b) (cs' := permCoxeterSystem (n + 1))
        (coxeterMatrixOfBase_eq_coxeterMatrixA P b e he),
      ← map_mul, CoxeterSystem.length_parabolicHom, CoxeterSystem.length_parabolicHom]
  rw [isRightDescent_permCoxeterSystem_iff, isRightDescent_weylCoxeterSystem_iff] at hdesc
  have hne : σ (e i).castSucc ≠ σ (e i).succ := σ.injective.ne Fin.castSucc_lt_succ.ne
  rw [← not_iff_not, ← hdesc, not_lt]
  -- The two letters of the transposition are the strands it crosses.
  have hs : BraidGroup.strand (n := n + 1) (e i) = (e i).castSucc := Fin.ext (by simp)
  have hs' : BraidGroup.strandSucc (n := n + 1) (e i) = (e i).succ := Fin.ext (by simp)
  rw [hs, hs', le_iff_lt_or_eq, or_iff_left hne.symm]

/-- **The Weyl group of type `Aₙ` is the symmetric group on `n + 1` letters**, for a finite
reduced crystallographic root pairing over a commutative domain of characteristic zero with a base
of Cartan type `Aₙ`. The pairing need not span. An explicit isomorphism, marked by any labelling
of the simple roots compatible with the Cartan matrices, is `RootPairing.typeAWeylGroupEquiv`. -/
theorem nonempty_weylGroup_mulEquiv_perm_of_typeA (h : HasCartanType P b (.A n)) :
    Nonempty (P.weylGroup ≃* Equiv.Perm (Fin (n + 1))) :=
  let ⟨e, he⟩ := exists_cartanMatrix_eq_A h
  ⟨P.typeAWeylGroupEquiv b e he⟩

/-- The Weyl group of a root pairing with a base of Cartan type `Aₙ` has order `(n + 1)!`. -/
theorem card_weylGroup_of_hasCartanType_A (h : HasCartanType P b (.A n)) :
    Nat.card P.weylGroup = (n + 1).factorial := by
  obtain ⟨e⟩ := P.nonempty_weylGroup_mulEquiv_perm_of_typeA b h
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]

include he in
/-- The number of positive roots of a base labelled as `Aₙ` is the number of pairs of letters
in `Fin (n + 1)`. -/
private theorem ncard_posRoots_eq_choose_two : (posRoots P b).ncard = (n + 1).choose 2 := by
  set φ := P.typeAWeylGroupEquiv b e he
  have : Finite P.weylGroup := Finite.of_equiv _ φ.symm.toEquiv
  have hpairs : #{p : Fin (n + 1) × Fin (n + 1) | p.1 < p.2} = (n + 1).choose 2 := by
    rw [Fintype.card_product_filter_lt, Fintype.card_fin]
  rw [← hpairs]
  refine le_antisymm ?_ ?_
  · obtain ⟨w₀, hw₀⟩ := exists_inversions_eq_posRoots_of_finite_weylGroup P b
    rw [← hw₀, P.ncard_inversions_eq_card_typeAWeylGroupEquiv b e he]
    exact card_le_card fun p ↦ by simp +contextual
  · obtain ⟨w, hw⟩ := φ.surjective Fin.revPerm
    calc #{p : Fin (n + 1) × Fin (n + 1) | p.1 < p.2}
        = #{p : Fin (n + 1) × Fin (n + 1) | p.1 < p.2 ∧ φ w p.2 < φ w p.1} := by
          simp_rw [hw, Fin.revPerm_apply, Fin.rev_lt_rev, and_self]
      _ = (inversions P b w).ncard := (P.ncard_inversions_eq_card_typeAWeylGroupEquiv b e he w).symm
      _ ≤ (posRoots P b).ncard := ncard_inversions_le P b w

/-- A base of Cartan type `Aₙ` has `n (n + 1) / 2` positive roots. -/
theorem ncard_posRoots_of_hasCartanType_A (h : HasCartanType P b (.A n)) :
    (posRoots P b).ncard = n * (n + 1) / 2 := by
  obtain ⟨e, he⟩ := exists_cartanMatrix_eq_A h
  rw [P.ncard_posRoots_eq_choose_two b e he, Nat.choose_two_right, Nat.add_sub_cancel,
    Nat.mul_comm]

/-- A root pairing with a base of Cartan type `Aₙ` has `n (n + 1)` roots. -/
theorem natCard_eq_of_hasCartanType_A (h : HasCartanType P b (.A n)) :
    Nat.card ι = n * (n + 1) := by
  obtain ⟨e, he⟩ := exists_cartanMatrix_eq_A h
  rw [← two_mul_ncard_posRoots P b, P.ncard_posRoots_eq_choose_two b e he, Nat.choose_two_right,
    Nat.add_sub_cancel, Nat.mul_comm (n + 1),
    Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]

end RootPairing
