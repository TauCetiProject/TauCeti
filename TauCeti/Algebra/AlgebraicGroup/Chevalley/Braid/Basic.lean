/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.Algebra.Lie.Presentation.Serre
import TauCeti.Algebra.Lie.Presentation.Serre.SingleBond
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# Weyl word identities and the single-bond braid relation in Chevalley data

Pinned simple Weyl representatives at a single bond satisfy the length-three braid
relation over every commutative ring. The equality holds in the actual point group,
including in bad characteristic and over nonreduced rings, not just in a Weyl quotient.

The rational Serre-operator braid relation is first restricted to the datum's integral
Kostant-stable lattice and then extended to the value ring. This avoids imposing any
restriction on weight multiplicities or choosing a signed permutation weight basis.
`weylElement_word_eq_of_weylUnit_word_eq` supplies this transport for arbitrary words
in the simple Weyl units, so the same construction applies to other bond types.

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

/-- An identity between words in the rational simple Weyl units descends to the
integral admissible lattice, then holds in the datum's points over any commutative ring. -/
theorem weylElement_word_eq_of_weylUnit_word_eq (l r : List (Fin t.rank))
    (h :
      let n := fun k => weylUnit
        (D.isNilpotent_representation_rootGenerator (.inl k))
        (D.isNilpotent_representation_rootGenerator (.inr k))
      (l.map n).prod = (r.map n).prod)
    (A : Type*) [CommRing A] :
    (l.map (fun k => D.weylElement (t.simpleIndex ht k) A 1)).prod =
      (r.map (fun k => D.weylElement (t.simpleIndex ht k) A 1)).prod := by
  let q := fun k => weylUnit
    (D.isNilpotent_representation_rootGenerator (.inl k))
    (D.isNilpotent_representation_rootGenerator (.inr k))
  let z := fun k => kostantWeylRestrict (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
    D.representation D.lattice D.representation_mem_lattice
    (D.isNilpotent_representation_rootGenerator (.inl k))
    (D.isNilpotent_representation_rootGenerator (.inr k))
  -- Restriction respects each letter, and hence the action of every word.
  have hz (w : List (Fin t.rank)) (v : D.lattice) :
      ((w.map z).prod v : D.carrier) = ((w.map q).prod : Module.End ℚ D.carrier) v := by
    induction w with
    | nil => rfl
    | cons k w ih =>
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, Units.val_mul,
        z, coe_kostantWeylRestrict_apply, Module.End.smul_def]
      rw [ih]
  have hZ : (l.map z).prod = (r.map z).prod := by
    ext v
    rw [hz, hz]
    exact congrArg (fun u : (Module.End ℚ D.carrier)ˣ => (u : Module.End ℚ D.carrier) v) h
  -- Multiplicativity of base change transports the integral word identity.
  let n := fun k => kostantWeylGL (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
    D.representation D.lattice D.representation_mem_lattice
    (D.isNilpotent_representation_rootGenerator (.inl k))
    (D.isNilpotent_representation_rootGenerator (.inr k)) A
  have hn (w : List (Fin t.rank)) :
      ((w.map z).prod).toLinearMap.baseChange A =
        ((w.map n).prod : Module.End A (A ⊗[ℤ] D.lattice)) := by
    induction w with
    | nil =>
      simp only [List.map_nil, List.prod_nil, LinearEquiv.coe_toLinearMap_one,
        LinearMap.baseChange_id, Units.val_one, Module.End.one_eq_id]
    | cons k w ih =>
      simp only [List.map_cons, List.prod_cons, LinearEquiv.coe_toLinearMap_mul,
        LinearMap.baseChange_mul, Units.val_mul, ih, n, z, kostantWeylGL_val,
        kostantWeylPoints_toLinearMap]
  have hN : (l.map n).prod = (r.map n).prod := by
    apply Units.ext
    simpa only [hn] using congrArg
      (fun e : D.lattice ≃ₗ[ℤ] D.lattice => e.toLinearMap.baseChange A) hZ
  -- The chosen lattice basis identifies these operators with the datum's points.
  let f := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
  have hf (k : Fin t.rank) :
      (D.weylElement (t.simpleIndex ht k) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A) =
        f (n k) := D.coe_weylElement_simpleIndex_one k A
  apply Subtype.ext
  simpa only [SubmonoidClass.coe_list_prod, List.map_map, Function.comp_def, hf,
    map_list_prod] using congrArg f hN

/-- A word identity valid for all nilpotent Serre systems on the datum's rational carrier,
in the transposed Cartan convention, holds for its pinned simple Weyl representatives
over every commutative ring. -/
theorem weylElement_word_eq_of_serre_word_eq (l r : List (Fin t.rank))
    (h : ∀ {H E F : Fin t.rank → Module.End ℚ D.carrier},
      IsSerreSystem ℚ t.cartanMatrix.transpose H E F →
      ∀ (hE : ∀ k, IsNilpotent (E k)) (hF : ∀ k, IsNilpotent (F k)),
        (l.map (fun k => weylUnit (hE k) (hF k))).prod =
          (r.map (fun k => weylUnit (hE k) (hF k))).prod)
    (A : Type*) [CommRing A] :
    (l.map (fun k => D.weylElement (t.simpleIndex ht k) A 1)).prod =
      (r.map (fun k => D.weylElement (t.simpleIndex ht k) A 1)).prod := by
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
  apply D.weylElement_word_eq_of_weylUnit_word_eq l r ?_ A
  simpa only [φ, Function.comp_apply, LieHom.comp_apply, AlgHom.toLieHom_apply,
    LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using h hs hE hF

/-- Pinned simple Weyl representatives at a single bond satisfy the length-three braid
relation over every commutative value ring. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_one (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1)
    (A : Type*) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 := by
  have h' := D.weylElement_word_eq_of_serre_word_eq [i, j, i] [j, i, j] (by
    intro H E F hs hE hF
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using hs.weylUnit_braid_of_cartan_eq_neg_one
        (i := i) (j := j) (by simp) (by simp) hji hij (hE i) (hF i) (hE j) (hF j)) A
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, mul_assoc] using h'

end TauCeti.DynkinType.ChevalleyDatum
