/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.Splitting
public import TauCeti.Algebra.Homology.ModuleCat.ShiftSequence

/-!
# The action of a cycle of degree zero on the cohomology of a shifted module complex

A cycle `a` of degree zero of the algebra acts on a differential graded right module `ℳ` by
`x ↦ x · a`, which commutes with the differential.  Composed with the Koszul sign, it is a
morphism of complexes from `shiftedModuleComplex hM (q + 1)` to the shift by one of
`shiftedModuleComplex hM q` (`TauCeti.shiftedModuleComplexAct`), hence induces a map on cohomology
(`TauCeti.shiftedModuleComplexActHomology`), which sends the class of `α` to the class of
`op a • ε α`, with `ε` the Koszul sign.

## Main definitions

* `TauCeti.shiftedModuleComplexAct`: the action of a cycle of degree zero, as a morphism of
  complexes.
* `TauCeti.shiftedModuleComplexActHomology`: the induced map on cohomology.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

section Action

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (hM : IsDGRightModule h ℳ dM)

/-- The right action of an element `a` of degree zero of the algebra, twisted by the Koszul sign,
from the degree-`n` term of `shiftedModuleComplex hM (q + 1)` to the degree-`(n + 1)` term of
`shiftedModuleComplex hM q`: both are the piece of `ℳ` of degree `n + q + 1`. -/
noncomputable def shiftedModuleComplexActX {a : A} (ha : a ∈ 𝒜 0) (q n : ℤ) :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).X n →ₗ[R]
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).X (n + 1) :=
  (shiftedModuleComplexXEquiv hM q (n + 1)).symm.toLinearMap ∘ₗ
    ((DistribSMul.toLinearMap R M (op a) ∘ₗ (InternalGrading.ofDecomposition ℳ).koszulTwist 1 ∘ₗ
      (ℳ (n + (q + 1))).subtype).codRestrict _ fun x ↦ by
        have hdeg : n + 1 + q = n + (q + 1) := by ring
        rw [hdeg]
        have hx : (x : M) ∈ (InternalGrading.ofDecomposition ℳ).piece (n + (q + 1)) := by
          rw [InternalGrading.ofDecomposition_piece]
          exact x.2
        have hε := (InternalGrading.ofDecomposition ℳ).koszulTwist_mem_piece hx 1
        rw [InternalGrading.ofDecomposition_piece] at hε
        exact op_smul_mem_of_mem_zero ha hε) ∘ₗ
    (shiftedModuleComplexXEquiv hM (q + 1) n).toLinearMap

@[simp]
theorem shiftedModuleComplexXEquiv_shiftedModuleComplexActX {a : A} (ha : a ∈ 𝒜 0) (q n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).X n) :
    (shiftedModuleComplexXEquiv hM q (n + 1) (shiftedModuleComplexActX hM ha q n α) : M) =
      op a • (InternalGrading.ofDecomposition ℳ).koszulTwist 1
        (shiftedModuleComplexXEquiv hM (q + 1) n α : M) := by
  simp only [shiftedModuleComplexActX, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply]
  rfl

include hM in
/-- The right action of a cycle `a` of degree zero of the algebra commutes with `dM`. -/
theorem dM_op_smul_of_d_eq_zero {a : A} (hda : d a = 0) {k : ℤ} {x : M} (hx : x ∈ ℳ k) :
    dM (op a • x) = op a • dM x := by
  rw [hM.leibniz hx a, hda, MulOpposite.op_zero, zero_smul, smul_zero, add_zero]

include hM in
/-- The right action of a cycle `a` of degree zero, twisted by the Koszul sign, anticommutes with
`dM`. -/
theorem op_smul_koszulTwist_dM {a : A} (hda : d a = 0) {k : ℤ} {x : M}
    (hx : x ∈ ℳ k) :
    op a • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (dM x) =
      -dM (op a • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 x) := by
  have hx' : x ∈ (InternalGrading.ofDecomposition ℳ).piece k := by
    rwa [InternalGrading.ofDecomposition_piece]
  have hdx : dM x ∈ (InternalGrading.ofDecomposition ℳ).piece (k + 1) := by
    rw [InternalGrading.ofDecomposition_piece]
    exact hM.isHomogeneous.map_mem hx
  rw [InternalGrading.koszulTwist_one_apply_of_mem _ hdx,
    InternalGrading.koszulTwist_one_apply_of_mem _ hx',
    dM_op_smul_of_d_eq_zero hM hda (Submodule.smul_mem _ _ hx), map_smul, Int.negOnePow_succ,
    Units.val_neg, Int.cast_neg, neg_smul, smul_neg, smul_comm (op a)]

/-- **The right action of a cycle of degree zero, twisted by the Koszul sign**, as a morphism of
complexes from `shiftedModuleComplex hM (q + 1)` to the shift by one of
`shiftedModuleComplex hM q`: it anticommutes with `dM`, as the shift requires. -/
noncomputable def shiftedModuleComplexAct {a : A} (ha : a ∈ 𝒜 0) (hda : d a = 0) (q : ℤ) :
    shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1) ⟶
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q)⟦(1 : ℤ)⟧ where
  f n := ModuleCat.ofHom (shiftedModuleComplexActX hM ha q n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun α ↦
      (shiftedModuleComplexXEquiv hM q (i + 1 + 1)).injective (Subtype.ext ?_))
    rw [CochainComplex.shiftFunctor_obj_d', Int.negOnePow_one, Units.neg_smul, one_smul]
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, ModuleCat.hom_neg,
      LinearMap.neg_apply, map_neg, Submodule.coe_neg]
    rw [shiftedModuleComplexXEquiv_shiftedModuleComplexActX, shiftedModuleComplexXEquiv_d,
      shiftedModuleComplexXEquiv_d, shiftedModuleComplexXEquiv_shiftedModuleComplexActX]
    exact (op_smul_koszulTwist_dM hM hda (shiftedModuleComplexXEquiv hM (q + 1) i α).2).symm

/-- Transport along an equality of degrees does not change the underlying element of `ℳ`. -/
theorem shiftedModuleComplexXEquiv_XIsoOfEq_hom (p i j : ℤ) (hij : i = j)
    (z : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X i) :
    (shiftedModuleComplexXEquiv hM p j
        (((shiftedModuleComplex.{uR, uA, uM, uP} hM p).XIsoOfEq hij).hom.hom z) : M) =
      shiftedModuleComplexXEquiv hM p i z := by
  subst hij
  rfl

/-- **The action of a cycle of degree zero on cohomology**: the map
`H^n(shiftedModuleComplex hM (q + 1)) ⟶ H^{n + 1}(shiftedModuleComplex hM q)` induced by
`shiftedModuleComplexAct`, both being the cohomology of `ℳ` in degree `n + q + 1`. -/
noncomputable def shiftedModuleComplexActHomology {a : A} (ha : a ∈ 𝒜 0) (hda : d a = 0)
    (q n n' : ℤ) (hn : 1 + n = n') :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology n ⟶
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology n' :=
  (HomologicalComplex.homologyFunctor _ _ 0).shiftMap (shiftedModuleComplexAct hM ha hda q) n n' hn

/-- The action of a cycle of degree zero on cohomology, on classes: it sends the class of `α` to
the class of `op a • ε α`, with `ε` the Koszul sign. -/
theorem shiftedModuleComplexActHomology_homologyπ {a : A} (ha : a ∈ 𝒜 0) (hda : d a = 0)
    (q n n' : ℤ) (hn : 1 + n = n') (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).X n)
    (hα : ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).d n (n + 1)).hom α = 0)
    (β : (shiftedModuleComplex.{uR, uA, uM, uP} hM q).X n')
    (hβ : (shiftedModuleComplexXEquiv hM q n' β : M) =
      op a • (InternalGrading.ofDecomposition ℳ).koszulTwist 1
        (shiftedModuleComplexXEquiv hM (q + 1) n α : M))
    (hβ' : ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).d n' (n' + 1)).hom β = 0) :
    (shiftedModuleComplexActHomology hM ha hda q n n' hn).hom
        (((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homologyπ n).hom
          ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).moduleCatCyclesMk α (n + 1)
            (by simp) hα)) =
      ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).homologyπ n').hom
        ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).moduleCatCyclesMk β (n' + 1)
          (by simp) hβ') :=
  CochainComplex.shiftMap_homologyπ_moduleCatCyclesMk _ n n' hn α hα β
    ((shiftedModuleComplexXEquiv hM q n').injective (Subtype.ext (by
      rw [hβ, CochainComplex.shiftFunctorObjXIso, shiftedModuleComplexXEquiv_XIsoOfEq_hom]
      exact (shiftedModuleComplexXEquiv_shiftedModuleComplexActX hM ha q n α).symm))) hβ'

/-- The action of a cycle of degree zero on cohomology sends the class of `α` to the class of an
element whose value is `op a • ε α`, with `ε` the Koszul sign. -/
theorem exists_shiftedModuleComplexActHomology_homologyπ {a : A} (ha : a ∈ 𝒜 0)
    (hda : d a = 0) (q n n' : ℤ) (hn : 1 + n = n')
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).X n)
    (hα : ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).d n (n + 1)).hom α = 0) :
    ∃ (β : (shiftedModuleComplex.{uR, uA, uM, uP} hM q).X n')
      (hβ' : ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).d n' (n' + 1)).hom β = 0),
      (shiftedModuleComplexXEquiv hM q n' β : M) =
        op a • (InternalGrading.ofDecomposition ℳ).koszulTwist 1
          (shiftedModuleComplexXEquiv hM (q + 1) n α : M) ∧
      (shiftedModuleComplexActHomology hM ha hda q n n' hn).hom
          (((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homologyπ n).hom
            ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).moduleCatCyclesMk α (n + 1)
              (by simp) hα)) =
        ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).homologyπ n').hom
          ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).moduleCatCyclesMk β (n' + 1)
            (by simp) hβ') := by
  have hmem : op a • (InternalGrading.ofDecomposition ℳ).koszulTwist 1
      (shiftedModuleComplexXEquiv hM (q + 1) n α : M) ∈ ℳ (n' + q) := by
    have hx : (shiftedModuleComplexXEquiv hM (q + 1) n α : M) ∈
        (InternalGrading.ofDecomposition ℳ).piece (n + (q + 1)) := by
      rw [InternalGrading.ofDecomposition_piece]
      exact (shiftedModuleComplexXEquiv hM (q + 1) n α).2
    have hε : ∀ j, j = n + (q + 1) → (InternalGrading.ofDecomposition ℳ).koszulTwist 1
        (shiftedModuleComplexXEquiv hM (q + 1) n α : M) ∈ ℳ j := by
      rintro j rfl
      have h := (InternalGrading.ofDecomposition ℳ).koszulTwist_mem_piece hx 1
      rwa [InternalGrading.ofDecomposition_piece] at h
    exact op_smul_mem_of_mem_zero ha (hε _ (by omega))
  have hβ : (shiftedModuleComplexXEquiv hM q n'
      ((shiftedModuleComplexXEquiv hM q n').symm ⟨_, hmem⟩) : M) =
        op a • (InternalGrading.ofDecomposition ℳ).koszulTwist 1
          (shiftedModuleComplexXEquiv hM (q + 1) n α : M) := by
    rw [LinearEquiv.apply_symm_apply]
  have hβ' : ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).d n' (n' + 1)).hom
      ((shiftedModuleComplexXEquiv hM q n').symm ⟨_, hmem⟩) = 0 := by
    rw [shiftedModuleComplexXEquiv_d_eq_zero_iff, hβ]
    have h := op_smul_koszulTwist_dM hM hda (shiftedModuleComplexXEquiv hM (q + 1) n α).2
    rw [(shiftedModuleComplexXEquiv_d_eq_zero_iff hM (q + 1) n α).1 hα, map_zero,
      smul_zero] at h
    exact neg_eq_zero.1 h.symm
  exact ⟨_, hβ', hβ, shiftedModuleComplexActHomology_homologyπ hM ha hda q n n' hn α hα _ hβ hβ'⟩

end Action

end TauCeti
