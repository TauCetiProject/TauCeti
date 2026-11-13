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
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# The triple-bond and general Artin--Tits braid relations in Chevalley data

Pinned simple Weyl representatives at a triple bond satisfy the length-six braid relation
over every commutative ring. Together with orthogonality at unjoined nodes and the single-
and double-bond braid relations, this proves the Artin--Tits braid relation
`prod_map_weylElement_braidWord` for every pair of Bourbaki nodes in the actual point group
`D.points A` of any Chevalley datum.

The triple-bond identity restricts the rational Serre-operator equality
`IsSerreSystem.weylUnit_braid_of_cartan_eq_neg_three` to the datum's Kostant-stable
lattice and extends scalars to `A`, avoiding any division in `A` or restriction on the
characteristic, reducedness, or weight multiplicities. The unified braid-word theorem
combines the four off-diagonal Cartan products `{0, 1, 2, 3}` of `t.coxeterMatrix`.

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

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private theorem weylRestrict_braid_tripleBond (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -3) :
    let n := fun i => kostantWeylRestrict (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice
      (D.isNilpotent_representation_rootGenerator (.inl i))
      (D.isNilpotent_representation_rootGenerator (.inr i))
    (n i * n j * n i * n j * n i * n j : D.lattice ≃ₗ[ℤ] D.lattice) =
      n j * n i * n j * n i * n j * n i := by
  dsimp only
  let φ := D.representation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  have hs := (t.isSerreSystem_lieBasis ht).map φ
  have hE (k : Fin t.rank) : IsNilpotent (φ ((t.lieBasis ht).e k)) := by
    simpa only [φ, LieHom.comp_apply, AlgHom.toLieHom_apply,
      LieAlgebra.Basis.rootGenerator_inl] using
      D.isNilpotent_representation_rootGenerator (.inl k)
  have hF (k : Fin t.rank) : IsNilpotent (φ ((t.lieBasis ht).f k)) := by
    simpa only [φ, LieHom.comp_apply, AlgHom.toLieHom_apply,
      LieAlgebra.Basis.rootGenerator_inr] using
      D.isNilpotent_representation_rootGenerator (.inr k)
  -- The Lie basis uses the transpose of the displayed Cartan matrix: exchange the two nodes
  -- in the rational operator theorem and take the symmetry of the resulting equality.
  have h := (hs.weylUnit_braid_of_cartan_eq_neg_three
    (i := j) (j := i) (by simp) (by simp) hij hji (hE j) (hF j) (hE i) (hF i)).symm
  ext v
  have hv := congrArg (fun u : (Module.End ℚ D.carrier)ˣ => (u : Module.End ℚ D.carrier) v) h
  simpa only [mul_apply_eq_comp, coe_kostantWeylRestrict_apply, Units.val_mul,
    Module.End.smul_def, φ, Function.comp_apply, LieHom.comp_apply, AlgHom.toLieHom_apply,
    LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using hv

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
  let n := fun i => kostantWeylGL (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
    D.representation D.lattice D.representation_mem_lattice
    (D.isNilpotent_representation_rootGenerator (.inl i))
    (D.isNilpotent_representation_rootGenerator (.inr i)) A
  have hn : n i * n j * n i * n j * n i * n j = n j * n i * n j * n i * n j * n i := by
    apply Units.ext
    have h := congrArg (fun e : D.lattice ≃ₗ[ℤ] D.lattice =>
      (e : Module.End ℤ D.lattice).baseChange A) (D.weylRestrict_braid_tripleBond i j
        (t.cartanMatrix_eq_neg_one_of_cartanMatrix_le_neg_two i j (by omega)) hji)
    simpa only [LinearEquiv.coe_toLinearMap_mul, LinearMap.baseChange_mul,
      Units.val_mul, n, kostantWeylGL_val, kostantWeylPoints_toLinearMap] using h
  let f := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
  have hf (k : Fin t.rank) :
      (D.weylElement (t.simpleIndex ht k) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A) =
        f (n k) := D.coe_weylElement_simpleIndex_one k A
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, hf, map_mul] using congrArg f hn

private theorem cartanMatrix_offDiag_of_mul_eq {i j : Fin t.rank} (hij : i ≠ j)
    {c : ℤ} (hc : 0 < c) (hp : t.cartanMatrix i j * t.cartanMatrix j i = c) :
    t.cartanMatrix i j = -1 ∧ t.cartanMatrix j i = -c ∨
      t.cartanMatrix j i = -1 ∧ t.cartanMatrix i j = -c := by
  have ha : t.cartanMatrix i j ≤ 0 := t.cartanMatrix_apply_le_zero_of_ne hij
  rcases (by omega : t.cartanMatrix i j = 0 ∨ t.cartanMatrix i j = -1 ∨
      t.cartanMatrix i j ≤ -2) with h | h | h
  · simp [h] at hp; omega
  · exact Or.inl ⟨h, by rw [h] at hp; omega⟩
  · have h' := t.cartanMatrix_eq_neg_one_of_cartanMatrix_le_neg_two j i h
    exact Or.inr ⟨h', by rw [h'] at hp; omega⟩

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
    coxeterMatrix_apply]
  rcases t.cartanMatrix_mul_cartanMatrix_mem_of_ne hij with hp | hp | hp | hp
  · have hzero : t.cartanMatrix i j = 0 :=
      (mul_eq_zero.mp hp).elim id (t.cartanMatrix_apply_eq_zero_iff_symm i j).mpr
    rw [hp, coxeterOrder_zero]
    simpa only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.map_append,
      List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
      one_mul, mul_one] using (D.commute_weylElement_simpleIndex A i j hzero 1 1).eq
  · rw [hp, coxeterOrder_one]
    rcases cartanMatrix_offDiag_of_mul_eq hij zero_lt_one hp with ⟨h1, h2⟩ | ⟨h2, h1⟩ <;>
      simpa only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
        one_mul, mul_one, mul_assoc] using
        (D.weylElement_braid_of_cartanMatrix_eq_neg_one i j h1 h2 A).symm
  · rw [hp, coxeterOrder_two]
    rcases cartanMatrix_offDiag_of_mul_eq hij zero_lt_two hp with ⟨_, hji⟩ | ⟨_, hij2⟩
    · simpa only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
        one_mul, mul_one, mul_assoc] using D.weylElement_braid_of_cartanMatrix_eq_neg_two i j hji A
    · simpa only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
        one_mul, mul_one, mul_assoc] using
        (D.weylElement_braid_of_cartanMatrix_eq_neg_two j i hij2 A).symm
  · rw [Set.mem_singleton_iff] at hp
    rw [hp, coxeterOrder_three]
    rcases cartanMatrix_offDiag_of_mul_eq hij zero_lt_three hp with ⟨_, hji⟩ | ⟨_, hij3⟩
    · simpa only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
        one_mul, mul_one, mul_assoc] using
        D.weylElement_braid_of_cartanMatrix_eq_neg_three i j hji A
    · simpa only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
        one_mul, mul_one, mul_assoc] using
        (D.weylElement_braid_of_cartanMatrix_eq_neg_three j i hij3 A).symm

end TauCeti.DynkinType.ChevalleyDatum
