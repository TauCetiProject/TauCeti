/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.RootSubgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Action
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.LeadingMinors
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Torus

/-!
# Weyl words in the matrix big cell

A Weyl word in a faithful Chevalley representation carries the weight space at `μ` to the
weight space at `w μ`. Its leading weight-block minors can therefore all be invertible only
when `w = 1`. Conversely, a word spelling the identity preserves every weight space, so all
these minors are units. This is the Weyl-representative test used to single out the open
Bruhat cell. It holds over every nontrivial commutative value ring, even when rational torus
points do not distinguish the weights.

The ordering can be any ordering of the distinct weights; basis vectors within a weight
space need not be permuted. The matrix argument uses
`TauCeti.UniversalEnvelopingAlgebra.isUnit_leading_weight_minors_iff`; the integral
weight-space transport uses `IsCartanWeightVector.kostantWeylRestrict` before scalar extension.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, Part II, Chapter 1.
-/

public section

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private noncomputable def simpleWeylLatticeEquiv (i : Fin t.rank) :
    D.lattice ≃ₗ[ℤ] D.lattice :=
  kostantWeylRestrict (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
    D.representation_mem_lattice (D.isNilpotent_representation_rootGenerator (.inl i))
    (D.isNilpotent_representation_rootGenerator (.inr i))

private theorem simpleWeylLatticeEquiv_weight (i : Fin t.rank) {μ : Fin t.rank → ℤ}
    {m : D.lattice}
    (hm : IsCartanWeightVector (t.lieBasis ht).h D.representation μ (m : D.carrier)) :
    IsCartanWeightVector (t.lieBasis ht).h D.representation
      (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) • μ)
      (D.simpleWeylLatticeEquiv i m : D.carrier) := by
  rw [RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul,
    RootPairing.reflection_apply, t.coroot'_simpleIndex_apply ht, t.root_simpleIndex ht]
  dsimp only [simpleWeylLatticeEquiv]
  exact IsCartanWeightVector.kostantWeylRestrict
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
    D.representation_mem_lattice (D.isNilpotent_representation_rootGenerator (.inl i))
    (D.isNilpotent_representation_rootGenerator (.inr i))
    (D.isSl2Triple_representation_rootGenerator i) (c := i) (α := fun j => t.cartanMatrix i j)
    (fun j => by simpa only [LieAlgebra.Basis.rootGenerator_inl, Int.cast_smul_eq_zsmul] using
      t.lie_lieBasis_h_e ht i j)
    (fun j => by simpa only [LieAlgebra.Basis.rootGenerator_inr, Int.cast_smul_eq_zsmul,
      neg_smul] using t.lie_lieBasis_h_f ht i j) hm

private noncomputable def weylWordLatticeEquiv (l : List (Fin t.rank)) :
    D.lattice ≃ₗ[ℤ] D.lattice :=
  (l.map D.simpleWeylLatticeEquiv).prod

private theorem weylWordLatticeEquiv_weight (l : List (Fin t.rank)) {μ : Fin t.rank → ℤ}
    {m : D.lattice}
    (hm : IsCartanWeightVector (t.lieBasis ht).h D.representation μ (m : D.carrier)) :
    IsCartanWeightVector (t.lieBasis ht).h D.representation
      (t.geckWeylWordProd ht l • μ) (D.weylWordLatticeEquiv l m : D.carrier) := by
  induction l generalizing μ m with
  | nil => simpa only [weylWordLatticeEquiv, List.map_nil, List.prod_nil,
      one_apply_eq_self, geckWeylWordProd_nil, one_smul] using hm
  | cons i l ih =>
      simpa only [weylWordLatticeEquiv, List.map_cons, List.prod_cons, mul_apply_eq_comp,
        geckWeylWordProd_cons, mul_smul] using D.simpleWeylLatticeEquiv_weight i (ih hm)

private theorem simpleWeylLatticeEquiv_matrix (i : Fin t.rank) (A : Type v) [CommRing A] :
    (LinearMap.toMatrix D.basis D.basis (D.simpleWeylLatticeEquiv i).toLinearMap).map
        (Int.castRingHom A) =
      ((D.weylElement (t.simpleIndex ht i) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A) := by
  rw [coe_weylElement_simpleIndex_one]
  -- Unwrap the matrix algebra equivalence and the map on units to apply the base-change
  -- matrix formula, which is stated for linear maps rather than units.
  change _ = LinearMap.toMatrix (D.basis.baseChange A) (D.basis.baseChange A)
    (kostantWeylGL (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
      D.representation_mem_lattice (D.isNilpotent_representation_rootGenerator (.inl i))
      (D.isNilpotent_representation_rootGenerator (.inr i)) (CommAlgCat.of ℤ A)).val
  rw [kostantWeylGL_val, kostantWeylPoints_toLinearMap,
    Module.Basis.toMatrix_baseChange_baseChange]
  rfl

private theorem weylWordLatticeEquiv_matrix (l : List (Fin t.rank)) (A : Type v) [CommRing A] :
    (LinearMap.toMatrix D.basis D.basis (D.weylWordLatticeEquiv l).toLinearMap).map
        (Int.castRingHom A) =
      (((l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod :
        Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A) := by
  induction l with
  | nil => simp [weylWordLatticeEquiv]
  | cons i l ih =>
      have heq : D.weylWordLatticeEquiv (i :: l) =
          D.simpleWeylLatticeEquiv i * D.weylWordLatticeEquiv l := by
        simp only [weylWordLatticeEquiv, List.map_cons, List.prod_cons]
      rw [heq, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, Matrix.map_mul,
        D.simpleWeylLatticeEquiv_matrix i A, ih]
      simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, Units.val_mul]

/-- A Weyl word has invertible leading weight-block minors exactly when the Weyl-group element
it spells is the identity. The equivalence `r` orders the distinct weights, keeping repeated
weights in a single block. The value ring may have arbitrary characteristic and nilpotents. -/
theorem isUnit_leading_weight_minors_weylWord_iff {β : Type*} [PartialOrder β] [DecidableLE β]
    (l : List (Fin t.rank)) (A : Type v) [CommRing A] [Nontrivial A]
    (r : Set.range D.weight ≃ β) :
    (∀ a, IsUnit ((Matrix.toSquareBlockProp
      ((((l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod :
        Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A))
      fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤ a).det)) ↔
      t.geckWeylWordProd ht l = 1 := by
  rw [← D.weylWordLatticeEquiv_matrix l A,
    isUnit_leading_weight_minors_iff (t.lieBasis ht).h D.representation D.lattice D.basis D.weight
      D.isCartanWeightVector_basis (D.weylWordLatticeEquiv l)
      (fun μ => t.geckWeylWordProd ht l • μ)
      (MulAction.injective _).injOn
      (fun j => D.weylWordLatticeEquiv_weight l (D.isCartanWeightVector_basis j)) r]
  exact ⟨D.eq_one_of_forall_smul_weight_eq _, fun h j => by rw [h, one_smul]⟩

end TauCeti.DynkinType.ChevalleyDatum
