/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.Lie.Presentation.Serre.Braid.TripleBond
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# The triple-bond braid relation in Chevalley data

Pinned simple Weyl representatives at a triple bond satisfy the length-six braid
relation in the actual points of every Chevalley datum over every commutative ring.
In particular the equality holds in characteristics two and three and over nonreduced
rings, without division by the root-string factorials in those rings.

The rational Serre-operator identity is restricted to the admissible lattice and then
base changed. This transport follows the single-bond construction in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic`, using multiplicativity of
base change instead of induction on tensors.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private theorem weylRestrict_triple_braid (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -3) (hji : t.cartanMatrix j i = -1) :
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
  have h := hs.weylUnit_braid_of_cartan_eq_neg_three
    (i := j) (j := i) (by simp) (by simp) hij hji (hE j) (hF j) (hE i) (hF i)
  ext v
  have hv := congrArg (fun u : (Module.End ℚ D.carrier)ˣ => (u : Module.End ℚ D.carrier) v) h.symm
  simpa only [mul_apply_eq_comp, coe_kostantWeylRestrict_apply, Units.val_mul,
    Module.End.smul_def, φ, Function.comp_apply, LieHom.comp_apply, AlgHom.toLieHom_apply,
    LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using hv

/-- Pinned Weyl representatives at a triple bond satisfy the length-six braid relation
in the actual point group over every commutative value ring. The Cartan convention has
roots as rows, so `i` is the long node. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_three (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -3) (hji : t.cartanMatrix j i = -1)
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
    have h := congrArg (fun e : D.lattice ≃ₗ[ℤ] D.lattice => e.toLinearMap.baseChange A)
      (D.weylRestrict_triple_braid i j hij hji)
    apply Units.ext
    simpa only [n, Units.val_mul, kostantWeylGL_val, kostantWeylPoints_toLinearMap,
      LinearEquiv.coe_toLinearMap_mul, LinearMap.baseChange_mul] using h
  let f := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
  have hf (k : Fin t.rank) :
      (D.weylElement (t.simpleIndex ht k) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A) =
        f (n k) := D.coe_weylElement_simpleIndex_one k A
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, hf, map_mul] using congrArg f hn

end TauCeti.DynkinType.ChevalleyDatum
