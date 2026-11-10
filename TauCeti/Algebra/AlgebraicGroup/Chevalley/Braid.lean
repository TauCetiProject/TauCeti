/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.RootSubgroup
import TauCeti.Algebra.Lie.Presentation.Serre.SingleBond
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# The single-bond braid relation in Chevalley data

Pinned simple Weyl representatives at a single bond satisfy the length-three braid
relation over every commutative ring. The equality holds in the actual point group,
including in bad characteristic and over nonreduced rings, not just in a Weyl quotient.

The rational Serre-operator braid relation is first restricted to the datum's integral
Kostant-stable lattice and then extended to the value ring. This avoids imposing any
restriction on weight multiplicities or choosing a signed permutation weight basis.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private theorem weylRestrict_braid (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1) :
    let n := fun i => kostantWeylRestrict (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice
      (D.isNilpotent_representation_rootGenerator (.inl i))
      (D.isNilpotent_representation_rootGenerator (.inr i))
    (n i * n j * n i : D.lattice ≃ₗ[ℤ] D.lattice) = n j * n i * n j := by
  dsimp only
  let φ := D.representation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  have hs := (t.isSerreSystem_lieBasis ht).map φ
  have hnil := (t.lieBasis ht).isNilpotent_e_and_f D.representation
    D.isNilpotent_representation_rootGenerator
  have h := hs.weylUnit_braid_of_cartan_eq_neg_one
    (i := i) (j := j) (by simp) (by simp) hji hij
    (hnil i).1 (hnil i).2 (hnil j).1 (hnil j).2
  ext v
  have hv := congrArg (fun u : (Module.End ℚ D.carrier)ˣ => (u : Module.End ℚ D.carrier) v) h
  simpa only [mul_apply_eq_comp, coe_kostantWeylRestrict_apply, Units.val_mul,
    Module.End.smul_def, φ, Function.comp_apply, LieHom.comp_apply, AlgHom.toLieHom_apply,
    LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using hv

/-- Pinned simple Weyl representatives at a single bond satisfy the length-three braid
relation over every commutative value ring. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_one (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1)
    (A : Type*) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 := by
  let n := fun i => kostantWeylGL (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
    D.representation D.lattice D.representation_mem_lattice
    (D.isNilpotent_representation_rootGenerator (.inl i))
    (D.isNilpotent_representation_rootGenerator (.inr i)) (CommAlgCat.of ℤ A)
  have hn : n i * n j * n i = n j * n i * n j := by
    apply Units.ext
    simpa only [n, Units.val_mul, kostantWeylGL_val, kostantWeylPoints_toLinearMap,
      LinearEquiv.coe_toLinearMap_mul, LinearMap.baseChange_mul] using
      congrArg (fun e : D.lattice ≃ₗ[ℤ] D.lattice =>
        (e : D.lattice →ₗ[ℤ] D.lattice).baseChange A) (D.weylRestrict_braid i j hij hji)
  -- Use the same matrix MulEquiv and value-ring carrier as the simple-index formula.
  let f := Units.map
    (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom
  have hf (k : Fin t.rank) :
      (D.weylElement (t.simpleIndex ht k) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A) =
        f (n k) := D.coe_weylElement_simpleIndex_one k A
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, hf, map_mul] using congrArg f hn

end TauCeti.DynkinType.ChevalleyDatum
