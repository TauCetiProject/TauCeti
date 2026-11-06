/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.WeightLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Torus
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# Weyl reflection on the actual torus of a Chevalley datum

A simple Weyl representative normalizes the split torus whose character lattice is the
integral span of the representation weights. This torus need not be the image of the
full-weight parametrization over the value ring. We restrict the root-datum reflection to
that span, express it in the chosen lattice basis, and dualize it on torus parameters.
Conjugation by the integral Weyl representative realizes this action over every commutative
ring, including rings with nilpotents.

The conjugation argument uses the weight-space action of
`UniversalEnvelopingAlgebra.IsCartanWeightVector.kostantWeylRestrict_symm` and the diagonal
torus construction, just as the full-weight formula
`UniversalEnvelopingAlgebra.kostantWeylPoints_conj_kostantTorusPoints` does. It does not require
a torus point to extend to the full weight lattice.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 20.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open TensorProduct

attribute [local instance] LieRing.ofAssociativeRing

namespace TauCeti.DynkinType.ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- The simple root-datum reflection restricted to the weight lattice of the datum. -/
noncomputable def weightLatticeSimpleReflection (i : Fin t.rank) :
    D.weightLattice ≃ₗ[ℤ] D.weightLattice :=
  LinearEquiv.ofInvolutive
    { toFun := fun μ => ⟨(t.simplyConnectedRootDatum ht).reflection (t.simpleIndex ht i) μ, by
        rw [RootPairing.reflection_apply]
        exact D.weightLattice.sub_mem μ.property
          (D.weightLattice.smul_mem _
            (rootSpan_le_span_weight ht D.representation D.lattice D.representation_mem_lattice
              D.basis D.weight D.injective_representation_ι D.span_lattice_eq_top
              D.isCartanWeightVector_basis
              (Submodule.subset_span ⟨t.simpleIndex ht i, rfl⟩)))⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
    (fun μ => Subtype.ext ((t.simplyConnectedRootDatum ht).reflection_same _ μ))

/-- On ambient weights, the restricted reflection subtracts the simple-root multiple
specified by the simple coroot. -/
@[simp]
theorem coe_weightLatticeSimpleReflection (i : Fin t.rank) (μ : D.weightLattice) :
    (D.weightLatticeSimpleReflection i μ : Fin t.rank → ℤ) =
      (μ : Fin t.rank → ℤ) - μ.val i • t.rootGeneratorWeight ht (.inl i) := by
  simp only [weightLatticeSimpleReflection, LinearEquiv.coe_ofInvolutive,
    LinearMap.coe_mk, AddHom.coe_mk, RootPairing.reflection_apply,
    coroot'_simpleIndex_apply, rootGeneratorWeight_inl_eq_root_simpleIndex]

/-- Restricting the root-datum reflection preserves its involution law. -/
@[simp]
theorem weightLatticeSimpleReflection_apply_twice (i : Fin t.rank) (μ : D.weightLattice) :
    D.weightLatticeSimpleReflection i (D.weightLatticeSimpleReflection i μ) = μ := by
  -- The restriction has exactly the ambient reflection as its underlying function.
  exact Subtype.ext ((t.simplyConnectedRootDatum ht).reflection_same _ μ)

/-- The simple reflection in coordinates of the datum's own character lattice. -/
noncomputable def coordinateSimpleReflection (i : Fin t.rank) :
    (Fin t.rank → ℤ) ≃ₗ[ℤ] (Fin t.rank → ℤ) :=
  D.weightLatticeBasis.equivFun.symm.trans
    ((D.weightLatticeSimpleReflection i).trans D.weightLatticeBasis.equivFun)

/-- Recombining arbitrary reflected coordinates in the chosen basis gives the
restricted root-datum reflection. -/
theorem sum_coordinateSimpleReflection_smul (i : Fin t.rank) (μ : Fin t.rank → ℤ) :
    ∑ j, D.coordinateSimpleReflection i μ j • D.weightLatticeBasis j =
      D.weightLatticeSimpleReflection i (∑ j, μ j • D.weightLatticeBasis j) := by
  rw [← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_symm_apply]
  simp only [coordinateSimpleReflection, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

/-- Recombining reflected coordinates gives the reflected weight. -/
@[simp]
theorem coordinateSimpleReflection_coordinateWeight (i : Fin t.rank) (j : Fin D.dim) :
    D.coordinateSimpleReflection i (D.coordinateWeight j) =
      D.weightLatticeBasis.equivFun
        (D.weightLatticeSimpleReflection i ⟨D.weight j, D.weight_mem_weightLattice j⟩) := by
  have h : D.weightLatticeBasis.equivFun.symm (D.coordinateWeight j) =
      ⟨D.weight j, D.weight_mem_weightLattice j⟩ := by
    apply Subtype.ext
    simp only [Module.Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul]
    exact D.sum_coordinateWeight_smul j
  simp only [coordinateSimpleReflection, LinearEquiv.trans_apply, h]

/-- The coordinate simple reflection is an involution. -/
@[simp]
theorem coordinateSimpleReflection_apply_twice (i : Fin t.rank) (μ : Fin t.rank → ℤ) :
    D.coordinateSimpleReflection i (D.coordinateSimpleReflection i μ) = μ := by
  simp only [coordinateSimpleReflection, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  rw [D.weightLatticeSimpleReflection_apply_twice, LinearEquiv.apply_symm_apply]

variable {A : Type*} [CommRing A]

/-- The simple reflection of actual-torus parameters, dual to the reflection on the
character lattice in its chosen basis. -/
noncomputable def simpleReflectionTorus (i : Fin t.rank) :
    (Fin t.rank → Aˣ) ≃* (Fin t.rank → Aˣ) :=
  { torusPointMap (D.coordinateSimpleReflection i).toLinearMap with
    invFun := torusPointMap (D.coordinateSimpleReflection i).toLinearMap
    left_inv := fun s => funext fun j => by
      simp [torusPointMap_apply]
    right_inv := fun s => funext fun j => by
      simp [torusPointMap_apply] }

/-- Each reflected torus coordinate evaluates the reflected basic character. -/
@[simp]
theorem simpleReflectionTorus_apply (i : Fin t.rank) (s : Fin t.rank → Aˣ)
    (j : Fin t.rank) :
    D.simpleReflectionTorus i s j =
      torusCharacter s (D.coordinateSimpleReflection i (Pi.single j 1)) :=
  torusPointMap_apply _ _ _

/-- Characters of the datum's actual torus pull back by the simple reflection. -/
@[simp]
theorem torusCharacter_simpleReflectionTorus (i : Fin t.rank) (s : Fin t.rank → Aˣ)
    (μ : Fin t.rank → ℤ) :
    torusCharacter (D.simpleReflectionTorus i s) μ =
      torusCharacter s (D.coordinateSimpleReflection i μ) :=
  torusCharacter_torusPointMap _ _ _

/-- Reflection of actual-torus parameters is involutive over every value ring. -/
@[simp]
theorem simpleReflectionTorus_apply_twice (i : Fin t.rank) (s : Fin t.rank → Aˣ) :
    D.simpleReflectionTorus i (D.simpleReflectionTorus i s) = s := by
  ext j
  simp [simpleReflectionTorus, torusPointMap_apply]

private theorem coordinateTorus_tmul (μ : D.weightLattice) (m : D.lattice)
    (hm : UniversalEnvelopingAlgebra.IsCartanWeightVector (t.lieBasis ht).h D.representation
      (μ : Fin t.rank → ℤ) (m : D.carrier)) (s : Fin t.rank → Aˣ) (a : A) :
    (UniversalEnvelopingAlgebra.kostantTorusPoints D.lattice D.basis D.coordinateWeight A s).val
        (a ⊗ₜ[ℤ] m) =
      ((torusCharacter s (D.weightLatticeBasis.equivFun μ) : A) * a) ⊗ₜ[ℤ] m := by
  rw [UniversalEnvelopingAlgebra.kostantTorusPoints_apply,
    basisWeightTorus_apply_of_repr_eq_zero (D.basis.baseChange A) D.coordinateWeight s
      (μ := D.weightLatticeBasis.equivFun μ) (m := a ⊗ₜ[ℤ] m) (fun j hj => ?_),
    smul_tmul', smul_eq_mul]
  have hne : D.weight j ≠ (μ : Fin t.rank → ℤ) := by
    intro h
    apply hj
    apply D.weightLatticeBasis.equivFun.symm.injective
    apply Subtype.ext
    simp only [Module.Basis.equivFun_symm_apply, LinearEquiv.symm_apply_apply,
      Submodule.coe_sum, Submodule.coe_smul]
    exact (D.sum_coordinateWeight_smul j).trans h
  rw [Module.Basis.baseChange_repr_tmul,
    UniversalEnvelopingAlgebra.repr_eq_zero_of_isCartanWeightVector
      (t.lieBasis ht).h D.representation D.lattice D.basis D.weight
      D.isCartanWeightVector_basis hm hne]
  simp

/-- The integral simple Weyl representative conjugates the actual coordinate torus by
its dual simple reflection. No extension of torus parameters to the full weight lattice
is required. The equality is in the general linear group of the scalar-extended lattice. -/
theorem kostantWeylGL_conj_coordinateTorus (i : Fin t.rank) (s : Fin t.rank → Aˣ) :
    let n := UniversalEnvelopingAlgebra.kostantWeylGL (t.lieBasis ht).rootGenerator
      (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice
      (D.isNilpotent_representation_rootGenerator (.inl i))
      (D.isNilpotent_representation_rootGenerator (.inr i)) A
    n * UniversalEnvelopingAlgebra.kostantTorusPoints D.lattice D.basis D.coordinateWeight A s *
        n⁻¹ =
      UniversalEnvelopingAlgebra.kostantTorusPoints D.lattice D.basis D.coordinateWeight A
        (D.simpleReflectionTorus i s) := by
  let e := (t.lieBasis ht).rootGenerator
  let h := (t.lieBasis ht).h
  let hi := D.isNilpotent_representation_rootGenerator (.inl i)
  let hj := D.isNilpotent_representation_rootGenerator (.inr i)
  have hT := ((t.lieBasis ht).isSl2Triple_rootGenerator i).map
    (D.representation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ))
    (fun hz => (t.lieBasis ht).sl2 i |>.h_ne_zero
      (D.injective_representation_ι (by simpa using hz)))
  apply Units.ext
  rw [Units.val_mul, Units.val_mul,
    UniversalEnvelopingAlgebra.kostantWeylGL_val,
    UniversalEnvelopingAlgebra.kostantWeylGL_inv_val]
  refine Module.Basis.ext (D.basis.baseChange A) fun j => ?_
  let μ := D.weightLatticeSimpleReflection i ⟨D.weight j, D.weight_mem_weightLattice j⟩
  let m := (UniversalEnvelopingAlgebra.kostantWeylRestrict e h D.representation D.lattice
    D.representation_mem_lattice hi hj).symm (D.basis j)
  have hm : UniversalEnvelopingAlgebra.IsCartanWeightVector h D.representation
      (μ : Fin t.rank → ℤ) (m : D.carrier) := by
    rw [D.coe_weightLatticeSimpleReflection]
    exact UniversalEnvelopingAlgebra.IsCartanWeightVector.kostantWeylRestrict_symm
      e h D.representation D.lattice D.representation_mem_lattice hi hj hT
      (t.lie_lieBasis_h_rootGenerator ht (.inl i))
      (fun k => by simpa only [rootGeneratorWeight_inr, rootGeneratorWeight_inl,
        Int.cast_neg, neg_smul] using t.lie_lieBasis_h_rootGenerator ht (.inr i) k)
      (D.isCartanWeightVector_basis j)
  simp only [Module.Basis.baseChange_apply, mul_apply_eq_comp, LinearEquiv.coe_coe,
    UniversalEnvelopingAlgebra.kostantWeylPoints_symm_apply_tmul]
  rw [D.coordinateTorus_tmul μ m hm,
    UniversalEnvelopingAlgebra.kostantWeylPoints_apply_tmul,
    LinearEquiv.apply_symm_apply,
    UniversalEnvelopingAlgebra.kostantTorusPoints_tmul_basis,
    D.torusCharacter_simpleReflectionTorus, D.coordinateSimpleReflection_coordinateWeight]

/-- In matrix coordinates of the datum, conjugation by the simple Weyl representative
reflects the actual torus parameters. -/
theorem basisMatrix_kostantWeylGL_conj_coordinateTorus (i : Fin t.rank)
    (s : Fin t.rank → Aˣ) :
    let n := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv
      (UniversalEnvelopingAlgebra.kostantWeylGL (t.lieBasis ht).rootGenerator
        (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice
        (D.isNilpotent_representation_rootGenerator (.inl i))
        (D.isNilpotent_representation_rootGenerator (.inr i)) A)
    n * UniversalEnvelopingAlgebra.kostantTorusMatrix D.lattice D.basis D.coordinateWeight s *
        n⁻¹ =
      UniversalEnvelopingAlgebra.kostantTorusMatrix D.lattice D.basis D.coordinateWeight
        (D.simpleReflectionTorus i s) := by
  let f : (Module.End A (A ⊗[ℤ] D.lattice))ˣ →*
      Matrix.GeneralLinearGroup (Fin D.dim) A :=
    Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
  have hf (u : Fin t.rank → Aˣ) :
      f (UniversalEnvelopingAlgebra.kostantTorusPoints
        D.lattice D.basis D.coordinateWeight A u) =
      UniversalEnvelopingAlgebra.kostantTorusMatrix
        D.lattice D.basis D.coordinateWeight u := by
    exact UniversalEnvelopingAlgebra.basisMatrix_kostantTorusPoints _ _ _ _
  have he := congrArg f (D.kostantWeylGL_conj_coordinateTorus i s)
  rw [map_mul, map_mul, map_inv, hf, hf] at he
  exact he

/-- A simple Weyl representative normalizes the full actual torus of a Chevalley datum,
not merely the image of its full-weight parametrization. -/
theorem map_coordinateTorus_range_conj_kostantWeylGL (i : Fin t.rank) :
    let n := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv
      (UniversalEnvelopingAlgebra.kostantWeylGL (t.lieBasis ht).rootGenerator
        (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice
        (D.isNilpotent_representation_rootGenerator (.inl i))
        (D.isNilpotent_representation_rootGenerator (.inr i)) A)
    Subgroup.map (MulAut.conj n).toMonoidHom
        (UniversalEnvelopingAlgebra.kostantTorusMatrix
          D.lattice D.basis D.coordinateWeight (A := A)).range =
      (UniversalEnvelopingAlgebra.kostantTorusMatrix
        D.lattice D.basis D.coordinateWeight (A := A)).range := by
  let n : Matrix.GeneralLinearGroup (Fin D.dim) A :=
    Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv
      (UniversalEnvelopingAlgebra.kostantWeylGL (t.lieBasis ht).rootGenerator
        (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice
        (D.isNilpotent_representation_rootGenerator (.inl i))
        (D.isNilpotent_representation_rootGenerator (.inr i)) A)
  dsimp only
  rw [← MonoidHom.range_comp]
  have hc : (MulAut.conj n).toMonoidHom.comp
      (UniversalEnvelopingAlgebra.kostantTorusMatrix
        D.lattice D.basis D.coordinateWeight (A := A)) =
      (UniversalEnvelopingAlgebra.kostantTorusMatrix
        D.lattice D.basis D.coordinateWeight).comp
          (D.simpleReflectionTorus i).toMonoidHom := by
    ext s : 1
    exact D.basisMatrix_kostantWeylGL_conj_coordinateTorus i s
  rw [hc, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr
      (show Function.Surjective (D.simpleReflectionTorus (A := A) i).toMonoidHom from
        (D.simpleReflectionTorus i).surjective), Subgroup.map_top]

end TauCeti.DynkinType.ChevalleyDatum

