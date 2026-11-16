/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Immersion
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Closed root subgroups of the simply connected Chevalley scheme

Every root morphism of the full-weight Chevalley datum is a closed immersion over `ℤ`.
Consequently its additive parameter remains faithful over arbitrary value rings, including
nonreduced rings and rings of bad characteristic.

The starting immersions are
`isClosedImmersion_rootSubgroup_simpleIndex_scChevalleyDatum`. They are extended using the
signed Weyl conjugation formula `ChevalleyDatum.weylElement_conj_rootSubgroupPoints`.
The argument takes place at the universal
additive-group point, so it proves surjectivity of coordinate maps, rather than only injectivity
on field-valued points. No point-generation or specialization theorem is required.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv Multiplicative
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType

noncomputable section

-- Match the scalar-action instance used by the integral exponential and its matrix API.
attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid}

namespace ChevalleyDatum

variable (D : ChevalleyDatum t ht)

local notation "C" γ => kostantRootSubgroupCoordinateMap (t.chevalleySystem ht)
  (LieAlgebra.Basis.h (t.lieBasis ht)) D.representation D.lattice
  (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator) γ
  (isNilpotent_apply_ι_chevalleySystem D.representation
    D.isNilpotent_representation_rootGenerator γ) D.basis

private theorem coordinateMap_conj_reflection (i : Fin t.rank) (γ : Fin t.numRoots)
    (A : Type) [CommRing A]
    (q0 : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) :
    toConv ((q0.ofConv.comp
      (C ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht i) γ)).hom.toAlgHom).comp
      (GeneralLinear.conjCoordinateIso
        (D.weylElement (t.simpleIndex ht i) ℤ 1 :
          Matrix.GeneralLinearGroup (Fin D.dim) ℤ)⁻¹).hom.hom.toAlgHom) =
      toConv (((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
        (ofAdd (((t.chevalleyWeylSign ht (t.simpleIndex ht i) γ : ℤ) : A) *
          toAdd (AdditiveGroup.gaPointsMulEquiv q0)))).ofConv.comp (C γ).hom.toAlgHom) := by
  let δ := (t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ
  let z := toAdd (AdditiveGroup.gaPointsMulEquiv q0)
  let ε := t.chevalleyWeylSign ht (t.simpleIndex ht i) γ
  let P : Matrix.GeneralLinearGroup (Fin D.dim) ℤ := D.weylElement (t.simpleIndex ht i) ℤ 1
  have hε : (ε : ℤ) * (ε : ℤ) = 1 := by simp [← Units.val_mul]
  have hεA : ((ε : ℤ) : A) * ((ε : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, hε, Int.cast_one]
  have hm := congrArg (fun x : D.points A => (x : Matrix.GeneralLinearGroup (Fin D.dim) A))
    (D.weylElement_conj_rootSubgroupPoints i γ A (((ε : ℤ) : A) * z))
  dsimp only [ε] at hεA hm
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← mul_assoc, hεA, one_mul] at hm
  have hp : Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P =
      (D.weylElement (t.simpleIndex ht i) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A) := by
    simp only [P, D.map_weylElement, map_one]
  apply (GeneralLinear.pointsMulEquiv D.dim).injective
  rw [GeneralLinear.pointsMulEquiv_toConv_comp_conjCoordinateIso]
  simp only [GeneralLinear.pointsMulEquiv_apply]
  rw [pointsMulEquiv_kostantRootSubgroupCoordinateMap,
    pointsMulEquiv_kostantRootSubgroupCoordinateMap,
    kostantRootSubgroupMatrix_eq_matrix_chevalleyRootSubgroup D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator,
    kostantRootSubgroupMatrix_eq_matrix_chevalleyRootSubgroup D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator]
  simp only [MulEquiv.apply_symm_apply]
  rw [← D.coe_rootSubgroupPoints, ← D.coe_rootSubgroupPoints, map_inv, hp]
  have h := congrArg (fun x : Matrix.GeneralLinearGroup (Fin D.dim) A =>
    (D.weylElement (t.simpleIndex ht i) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A)⁻¹ * x *
      (D.weylElement (t.simpleIndex ht i) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A)) hm
  simpa only [← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right, inv_inv, δ, ε, z,
    ofAdd_toAdd] using h.symm

private theorem coordinateMap_surjective_reflection (i : Fin t.rank) (γ : Fin t.numRoots)
    (hγ : Function.Surjective (C γ).hom) :
    Function.Surjective
      (C ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ)).hom := by
  let δ := (t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ
  let A : Type := AdditiveGroup.coordinateHopfAlgebra ℤ
  let : Algebra ℤ A := Ring.toIntAlgebra A
  let z : A := SymmetricAlgebra.ι ℤ ℤ 1
  let ε := t.chevalleyWeylSign ht (t.simpleIndex ht i) γ
  let P : Matrix.GeneralLinearGroup (Fin D.dim) ℤ := D.weylElement (t.simpleIndex ht i) ℤ 1
  let q0 := (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (ofAdd z)
  -- Read the universal point as a function, avoiding two different integer algebra instances.
  have hq0 : ∀ a : A, q0.ofConv a = a := by
    have hring : q0.ofConv.toRingHom = RingHom.id A := by
      apply SymmetricAlgebra.ringHom_ext (Subsingleton.elim _ _)
      intro m
      have hm : SymmetricAlgebra.ι ℤ ℤ m = m • z := by
        simpa only [smul_eq_mul, mul_one] using (SymmetricAlgebra.ι ℤ ℤ).map_smul m (1 : ℤ)
      rw [hm, map_zsmul]
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, q0, z,
        AdditiveGroup.gaPointsMulEquiv_symm_apply_ι, toAdd_ofAdd]
      rfl
    exact fun a => congrArg (fun g : A →+* A => g a) hring
  obtain ⟨x, hx⟩ := (hγ : Function.Surjective (C γ).hom.toAlgHom) z
  have heval := congrArg (fun p => p.ofConv x) (D.coordinateMap_conj_reflection i γ A q0)
  simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, hq0, hx, q0, z,
    MulEquiv.apply_symm_apply, toAdd_ofAdd, AdditiveGroup.gaPointsMulEquiv_symm_apply_ι] at heval
  have hεA : ((ε : ℤ) : A) * ((ε : ℤ) : A) = 1 := by
    simp [← Int.cast_mul, ← Units.val_mul]
  apply (C δ).hom.toAlgHom.surjective_of_ι_one_mem_range
  refine ⟨(ε : ℤ) • (GeneralLinear.conjCoordinateIso P⁻¹).hom.hom x, ?_⟩
  rw [map_zsmul]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom]
  rw [heval, zsmul_eq_mul, ← mul_assoc, hεA, one_mul]

/-- Surjectivity of the positive simple-root coordinate maps implies surjectivity of all
root coordinate maps. The assertion concerns integral polynomial maps, not just field points. -/
theorem rootCoordinateMap_surjective_of_simple
    (hsimple : ∀ i : Fin t.rank, Function.Surjective (C (t.simpleIndex ht i)).hom)
    (γ : Fin t.numRoots) : Function.Surjective (C γ).hom := by
  induction γ using (t.rationalBase ht).induction_simple_reflect with
  | h₁ γ hγ =>
    obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hγ
    exact hsimple i
  | h₂ γ α hγ hα =>
    obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hα
    simpa only [reflectionPerm_rationalRootSystem] using
      D.coordinateMap_surjective_reflection i γ hγ

/-- If the positive simple-root morphisms are closed immersions, every root morphism is a
closed immersion. This criterion does not assume generation of the group of field points. -/
theorem isClosedImmersion_rootSubgroup_of_simple
    (hsimple : ∀ i : Fin t.rank,
      IsClosedImmersion (D.rootSubgroup (t.simpleIndex ht i)).hom.hom.left)
    (γ : Fin t.numRoots) : IsClosedImmersion (D.rootSubgroup γ).hom.hom.left := by
  have hcoord (i : Fin t.rank) : Function.Surjective (C (t.simpleIndex ht i)).hom := by
    have := hsimple i
    have hc' := IsClosedImmersion.comp
      (D.rootSubgroup (t.simpleIndex ht i)).hom.hom.left D.groupSchemeι.hom.hom.left
    have hc : IsClosedImmersion
        (D.rootSubgroup (t.simpleIndex ht i) ≫ D.groupSchemeι).hom.hom.left := by
      simpa only [Grp.comp_hom_hom, Over.comp_left] using hc'
    rw [D.rootSubgroup_comp_groupSchemeι, kostantRootSubgroup_def] at hc
    exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
      (AdditiveGroup.groupScheme_def ℤ) (GeneralLinear.groupScheme_def ℤ D.dim) _).1 hc
  rw [D.rootSubgroup_def, chevalleyRootSubgroupToToral_def]
  apply (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_iff _ _).2
  have h := mkQuotient_comp_chevalleyRootSubgroupToralCoordinateMap D.representation
    D.lattice D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
    D.basis D.coordinateWeight γ
  rw [CommHopfAlgCat.liftQuotient_unique _ _
    (kostantToralDefiningIdeal_toIdeal_le_ker_kostantRootSubgroupCoordinateMap D.representation
      D.lattice D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
      D.basis D.coordinateWeight γ) _ h]
  exact CommHopfAlgCat.liftQuotient_surjective_of_surjective _ _ _
    (D.rootCoordinateMap_surjective_of_simple hcoord γ)

end ChevalleyDatum

variable (t : DynkinType) (ht : t.Valid)

/-- Every root morphism of the full-weight Chevalley datum is a closed immersion over `ℤ`.
In particular this is scheme-theoretic, including in bad characteristic and after nonreduced
base change, and does not require generation of all group points by root subgroups. -/
instance isClosedImmersion_rootSubgroup_scChevalleyDatum (γ : Fin t.numRoots) :
    IsClosedImmersion ((t.scChevalleyDatum ht).rootSubgroup γ).hom.hom.left := by
  exact (t.scChevalleyDatum ht).isClosedImmersion_rootSubgroup_of_simple
    (fun i => isClosedImmersion_rootSubgroup_simpleIndex_scChevalleyDatum t ht i) γ

end

end TauCeti.DynkinType
