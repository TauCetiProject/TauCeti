/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Action
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Torus
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Integral lattice Weyl representatives

Pinned simple Weyl representatives preserve the admissible integral lattice of a Chevalley
datum. Their ordered products transport Cartan weights by the corresponding Weyl word, and
inverse products transport weights by its inverse. After scalar extension, their integral
matrices are the products of the datum's Weyl points over any commutative ring.

## Main definitions

* `TauCeti.DynkinType.ChevalleyDatum.simpleWeylLatticeEquiv`: a simple Weyl representative
  restricted to the integral lattice.
* `TauCeti.DynkinType.ChevalleyDatum.weylWordLatticeEquiv`: the lattice action of a Weyl word.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.map_toMatrix_weylWordLatticeEquiv`: scalar extension of an
  integral Weyl word gives the corresponding product of Weyl points.

The transport argument is used by the big-cell weight-minor test.
It uses the Kostant lattice restriction rather than a signed permutation weight basis.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- The pinned simple Weyl representative acting on the admissible integral lattice. -/
noncomputable def simpleWeylLatticeEquiv (i : Fin t.rank) :
    D.lattice ≃ₗ[ℤ] D.lattice :=
  kostantWeylRestrict (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
    D.representation_mem_lattice (D.isNilpotent_representation_rootGenerator (.inl i))
    (D.isNilpotent_representation_rootGenerator (.inr i))

/-- The simple lattice representative is the restriction of the rational Weyl operator. -/
theorem simpleWeylLatticeEquiv_def (i : Fin t.rank) :
    D.simpleWeylLatticeEquiv i =
      kostantWeylRestrict (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation
        D.lattice D.representation_mem_lattice
        (D.isNilpotent_representation_rootGenerator (.inl i))
        (D.isNilpotent_representation_rootGenerator (.inr i)) := by
  rfl

/-- The simple lattice representative acts by the rational Weyl unit on the carrier. -/
@[simp]
theorem coe_simpleWeylLatticeEquiv_apply (i : Fin t.rank) (m : D.lattice) :
    (D.simpleWeylLatticeEquiv i m : D.carrier) =
      (weylUnit (D.isNilpotent_representation_rootGenerator (.inl i))
        (D.isNilpotent_representation_rootGenerator (.inr i)) : Module.End ℚ D.carrier) m := by
  rw [simpleWeylLatticeEquiv_def, coe_kostantWeylRestrict_apply, Module.End.smul_def]

/-- The inverse simple lattice representative acts by the inverse rational Weyl unit. -/
@[simp]
theorem coe_simpleWeylLatticeEquiv_symm_apply (i : Fin t.rank) (m : D.lattice) :
    ((D.simpleWeylLatticeEquiv i).symm m : D.carrier) =
      (((weylUnit (D.isNilpotent_representation_rootGenerator (.inl i))
        (D.isNilpotent_representation_rootGenerator (.inr i)) :
          (Module.End ℚ D.carrier)ˣ)⁻¹ : (Module.End ℚ D.carrier)ˣ) :
            Module.End ℚ D.carrier) m := by
  rw [simpleWeylLatticeEquiv_def, coe_kostantWeylRestrict_symm_apply, Module.End.smul_def]

/-- A product of pinned simple Weyl representatives on the integral lattice. -/
noncomputable def weylWordLatticeEquiv (l : List (Fin t.rank)) :
    D.lattice ≃ₗ[ℤ] D.lattice :=
  (l.map D.simpleWeylLatticeEquiv).prod

/-- The lattice action of a word is the ordered product of its simple lattice actions. -/
theorem weylWordLatticeEquiv_def (l : List (Fin t.rank)) :
    D.weylWordLatticeEquiv l = (l.map D.simpleWeylLatticeEquiv).prod := by
  rfl

/-- The empty Weyl word acts as the identity on the integral lattice. -/
@[simp]
theorem weylWordLatticeEquiv_nil : D.weylWordLatticeEquiv [] = 1 := by
  simp [weylWordLatticeEquiv_def]

/-- Prepending a simple root multiplies its lattice representative on the left. -/
@[simp]
theorem weylWordLatticeEquiv_cons (i : Fin t.rank) (l : List (Fin t.rank)) :
    D.weylWordLatticeEquiv (i :: l) =
      D.simpleWeylLatticeEquiv i * D.weylWordLatticeEquiv l := by
  simp [weylWordLatticeEquiv_def]

/-- Concatenation of Weyl words corresponds to multiplication of lattice representatives. -/
@[simp]
theorem weylWordLatticeEquiv_append (l r : List (Fin t.rank)) :
    D.weylWordLatticeEquiv (l ++ r) =
      D.weylWordLatticeEquiv l * D.weylWordLatticeEquiv r := by
  simp [weylWordLatticeEquiv_def, List.prod_append]

/-- A lattice Weyl word acts by the corresponding product of rational Weyl units. -/
@[simp]
theorem coe_weylWordLatticeEquiv_apply (l : List (Fin t.rank)) (m : D.lattice) :
    (D.weylWordLatticeEquiv l m : D.carrier) =
      ((l.map fun i => weylUnit
        (D.isNilpotent_representation_rootGenerator (.inl i))
        (D.isNilpotent_representation_rootGenerator (.inr i))).prod :
          Module.End ℚ D.carrier) m := by
  induction l generalizing m with
  | nil => simp
  | cons i l ih =>
      simp only [weylWordLatticeEquiv_cons, mul_apply_eq_comp,
        coe_simpleWeylLatticeEquiv_apply, ih, List.map_cons, List.prod_cons,
        Units.val_mul]

/-- An inverse lattice Weyl word acts by the inverse product of rational Weyl units. -/
@[simp]
theorem coe_weylWordLatticeEquiv_symm_apply (l : List (Fin t.rank)) (m : D.lattice) :
    ((D.weylWordLatticeEquiv l).symm m : D.carrier) =
      ((((l.map fun i => weylUnit
        (D.isNilpotent_representation_rootGenerator (.inl i))
        (D.isNilpotent_representation_rootGenerator (.inr i))).prod)⁻¹ :
          (Module.End ℚ D.carrier)ˣ) : Module.End ℚ D.carrier) m := by
  simp_rw [← LinearEquiv.coe_inv]
  induction l generalizing m with
  | nil => simp
  | cons i l ih =>
      rw [weylWordLatticeEquiv_cons, mul_inv_rev, mul_apply_eq_comp, ih,
        LinearEquiv.coe_inv, coe_simpleWeylLatticeEquiv_symm_apply]
      simp only [List.map_cons, List.prod_cons, mul_inv_rev, Units.val_mul,
        mul_apply_eq_comp]

/-- The integral matrix of a simple lattice representative base changes to the matrix
of the datum's pinned simple Weyl representative over any commutative ring. -/
theorem map_toMatrix_simpleWeylLatticeEquiv (i : Fin t.rank) (A : Type v) [CommRing A] :
    (LinearMap.toMatrix D.basis D.basis (D.simpleWeylLatticeEquiv i).toLinearMap).map
        (Int.castRingHom A) =
      ((D.weylElement (t.simpleIndex ht i) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A) := by
  simp [coe_weylElement_simpleIndex_one, LinearMap.toMatrixAlgEquiv,
    kostantWeylGL_val, kostantWeylPoints_toLinearMap,
    Module.Basis.toMatrix_baseChange_baseChange, D.simpleWeylLatticeEquiv_def, algebraMap_int_eq]

/-- The integral matrix of a Weyl word becomes the product of the datum's pinned
simple Weyl representatives after scalar extension to any commutative ring. -/
theorem map_toMatrix_weylWordLatticeEquiv (l : List (Fin t.rank)) (A : Type v) [CommRing A] :
    (LinearMap.toMatrix D.basis D.basis (D.weylWordLatticeEquiv l).toLinearMap).map
        (Int.castRingHom A) =
      (((l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod :
        Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A) := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [weylWordLatticeEquiv_cons, LinearEquiv.coe_toLinearMap_mul,
        LinearMap.toMatrix_mul, Matrix.map_mul, D.map_toMatrix_simpleWeylLatticeEquiv i A, ih]
      simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, Units.val_mul]

/-- The integral matrix of an inverse simple lattice representative base changes to the
inverse of the datum's pinned simple Weyl matrix over any commutative ring. -/
theorem map_toMatrix_simpleWeylLatticeEquiv_symm (i : Fin t.rank) (A : Type v) [CommRing A] :
    (LinearMap.toMatrix D.basis D.basis (D.simpleWeylLatticeEquiv i).symm.toLinearMap).map
        (Int.castRingHom A) =
      (((D.weylElement (t.simpleIndex ht i) A 1)⁻¹ :
        Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A) := by
  simp [coe_weylElement_simpleIndex_one, LinearMap.toMatrixAlgEquiv,
    kostantWeylGL_inv_val, kostantWeylPoints_symm_toLinearMap,
    Module.Basis.toMatrix_baseChange_baseChange, D.simpleWeylLatticeEquiv_def, algebraMap_int_eq]

/-- The integral matrix of an inverse Weyl word becomes the inverse product of the datum's
pinned simple Weyl matrices after scalar extension to any commutative ring. -/
theorem map_toMatrix_weylWordLatticeEquiv_symm (l : List (Fin t.rank)) (A : Type v)
    [CommRing A] :
    (LinearMap.toMatrix D.basis D.basis (D.weylWordLatticeEquiv l).symm.toLinearMap).map
        (Int.castRingHom A) =
      ((((l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod)⁻¹ :
        Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A) := by
  induction l with
  | nil => simp [LinearEquiv.one_eq_refl]
  | cons i l ih =>
      rw [weylWordLatticeEquiv_cons, LinearEquiv.mul_eq_trans, LinearEquiv.trans_symm,
        ← LinearEquiv.mul_eq_trans, LinearEquiv.coe_toLinearMap_mul,
        LinearMap.toMatrix_mul, Matrix.map_mul, ih,
        D.map_toMatrix_simpleWeylLatticeEquiv_symm i A]
      simp only [List.map_cons, List.prod_cons, mul_inv_rev, Subgroup.coe_mul, Units.val_mul]

/-- A pinned simple lattice representative transports a Cartan weight vector by the
corresponding simple reflection. -/
theorem isCartanWeightVector_simpleWeylLatticeEquiv (i : Fin t.rank) {μ : Fin t.rank → ℤ}
    {m : D.lattice}
    (hm : IsCartanWeightVector (t.lieBasis ht).h D.representation μ (m : D.carrier)) :
    IsCartanWeightVector (t.lieBasis ht).h D.representation
      (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) • μ)
      (D.simpleWeylLatticeEquiv i m : D.carrier) := by
  rw [RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul,
    RootPairing.reflection_apply, t.coroot'_simpleIndex_apply ht, t.root_simpleIndex ht]
  rw [D.simpleWeylLatticeEquiv_def]
  exact IsCartanWeightVector.kostantWeylRestrict
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
    D.representation_mem_lattice (D.isNilpotent_representation_rootGenerator (.inl i))
    (D.isNilpotent_representation_rootGenerator (.inr i))
    (D.isSl2Triple_representation_rootGenerator i) (c := i) (α := fun j => t.cartanMatrix i j)
    (fun j => by simpa only [LieAlgebra.Basis.rootGenerator_inl, Int.cast_smul_eq_zsmul] using
      t.lie_lieBasis_h_e ht i j)
    (fun j => by simpa only [LieAlgebra.Basis.rootGenerator_inr, Int.cast_smul_eq_zsmul,
      neg_smul] using t.lie_lieBasis_h_f ht i j) hm

/-- The inverse pinned simple lattice representative transports a Cartan weight vector by
that same simple reflection. -/
theorem isCartanWeightVector_simpleWeylLatticeEquiv_symm (i : Fin t.rank) {μ : Fin t.rank → ℤ}
    {m : D.lattice}
    (hm : IsCartanWeightVector (t.lieBasis ht).h D.representation μ (m : D.carrier)) :
    IsCartanWeightVector (t.lieBasis ht).h D.representation
      (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) • μ)
      ((D.simpleWeylLatticeEquiv i).symm m : D.carrier) := by
  rw [RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul,
    RootPairing.reflection_apply, t.coroot'_simpleIndex_apply ht, t.root_simpleIndex ht]
  rw [D.simpleWeylLatticeEquiv_def]
  exact IsCartanWeightVector.kostantWeylRestrict_symm
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
    D.representation_mem_lattice (D.isNilpotent_representation_rootGenerator (.inl i))
    (D.isNilpotent_representation_rootGenerator (.inr i))
    (D.isSl2Triple_representation_rootGenerator i) (c := i) (α := fun j => t.cartanMatrix i j)
    (fun j => by simpa only [LieAlgebra.Basis.rootGenerator_inl, Int.cast_smul_eq_zsmul] using
      t.lie_lieBasis_h_e ht i j)
    (fun j => by simpa only [LieAlgebra.Basis.rootGenerator_inr, Int.cast_smul_eq_zsmul,
      neg_smul] using t.lie_lieBasis_h_f ht i j) hm

/-- A lattice Weyl word transports a Cartan weight vector by the Weyl-group element it spells. -/
theorem isCartanWeightVector_weylWordLatticeEquiv (l : List (Fin t.rank)) {μ : Fin t.rank → ℤ}
    {m : D.lattice}
    (hm : IsCartanWeightVector (t.lieBasis ht).h D.representation μ (m : D.carrier)) :
    IsCartanWeightVector (t.lieBasis ht).h D.representation
      (t.simplyConnectedWeylWordProd ht l • μ) (D.weylWordLatticeEquiv l m : D.carrier) := by
  induction l generalizing μ m with
  | nil => simpa only [weylWordLatticeEquiv_nil, one_apply_eq_self,
      simplyConnectedWeylWordProd_nil, one_smul] using hm
  | cons i l ih =>
      simpa only [weylWordLatticeEquiv_cons, mul_apply_eq_comp,
        simplyConnectedWeylWordProd_cons, mul_smul] using
        D.isCartanWeightVector_simpleWeylLatticeEquiv i (ih hm)

/-- An inverse lattice Weyl word transports a Cartan weight vector by the inverse
of the Weyl-group element it spells. -/
theorem isCartanWeightVector_weylWordLatticeEquiv_symm (l : List (Fin t.rank))
    {μ : Fin t.rank → ℤ} {m : D.lattice}
    (hm : IsCartanWeightVector (t.lieBasis ht).h D.representation μ (m : D.carrier)) :
    IsCartanWeightVector (t.lieBasis ht).h D.representation
      ((t.simplyConnectedWeylWordProd ht l)⁻¹ • μ)
      ((D.weylWordLatticeEquiv l).symm m : D.carrier) := by
  simp_rw [← LinearEquiv.coe_inv]
  induction l generalizing μ m with
  | nil => simpa only [weylWordLatticeEquiv_nil, inv_one, one_apply_eq_self,
      simplyConnectedWeylWordProd_nil, one_smul] using hm
  | cons i l ih =>
      simpa only [weylWordLatticeEquiv_cons, mul_inv_rev, mul_apply_eq_comp,
        simplyConnectedWeylWordProd_cons, RootPairing.weylGroup.ofIdx_inv_eq, mul_smul,
        LinearEquiv.coe_inv] using
        ih (D.isCartanWeightVector_simpleWeylLatticeEquiv_symm i hm)

end TauCeti.DynkinType.ChevalleyDatum
