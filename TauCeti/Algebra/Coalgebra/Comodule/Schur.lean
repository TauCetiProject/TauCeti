/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Intertwiner
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Isotypic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.RingTheory.Semisimple.Schur

/-!
# Schur's lemma for simple comodules

This file transports Schur's lemma from modules over the convolution dual to native right
comodules, and extracts the corresponding matrix-intertwiner criteria.

Between simple comodules over a projective coalgebra, every morphism is either bijective or zero,
and distinct simple coefficient spaces admit no nonzero intertwiner. Simple comodules with the same
coefficient space are intertwined by a scalar matrix whose `mulVec` is bijective. Over an
algebraically closed field every endomorphism of a simple comodule is a scalar multiple of the
identity, so a scalar matrix commuting with a simple comodule's coefficient matrix is scalar.

## Main declarations

* `TauCeti.Comodule.Hom.bijective_or_eq_zero`: Schur's lemma for morphisms of simple comodules.
* `TauCeti.Comodule.Hom.eq_zero_of_matrixCoefficientSubmodule_ne`: simple comodules with distinct
  coefficient spaces admit no nonzero morphism.
* `TauCeti.Comodule.Hom.exists_eq_smul_id`: over an algebraically closed field, every endomorphism
  of a simple comodule is a scalar multiple of the identity.
* `Module.Basis.exists_mulVec_bijective_coefficientMatrix_mul_eq`: simple comodules with the same
  coefficient space are intertwined by a scalar matrix with bijective `mulVec`.
* `Module.Basis.exists_eq_smul_one_of_coefficientMatrix_mul_eq`: a scalar matrix commuting with the
  coefficient matrix of a simple comodule over an algebraically closed field is scalar.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
-/

public noncomputable section

open Module
open scoped TensorProduct

namespace TauCeti.Comodule

attribute [local instance] convolutionModule

section Ring

variable {R C M N : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Projective R C]
  [AddCommGroup M] [Module R M] [Comodule R C M]
  [AddCommGroup N] [Module R N] [Comodule R C N]

/-- **Schur's lemma for comodules.** Every morphism between simple comodules over a projective
coalgebra is either bijective or zero. -/
theorem Hom.bijective_or_eq_zero [IsSimpleOrder (Subcomodule R C M)]
    [IsSimpleOrder (Subcomodule R C N)] (f : Hom R C M N) :
    Function.Bijective f ∨ f = 0 := by
  have : IsSimpleModule (WithConv (C →ₗ[R] R)) M := isSimpleModule_convolution_iff.mpr inferInstance
  have : IsSimpleModule (WithConv (C →ₗ[R] R)) N := isSimpleModule_convolution_iff.mpr inferInstance
  rcases f.toConvolutionLinearMap.bijective_or_eq_zero with h | h
  · left
    have hfun : (f.toConvolutionLinearMap : M → N) = f := funext f.toConvolutionLinearMap_apply
    rwa [hfun] at h
  · exact Or.inr (Hom.ext fun m ↦ by simpa using LinearMap.congr_fun h m)

/-- Simple comodules with distinct coefficient spaces admit no nonzero comodule morphism. -/
theorem Hom.eq_zero_of_matrixCoefficientSubmodule_ne [IsSimpleOrder (Subcomodule R C M)]
    [IsSimpleOrder (Subcomodule R C N)]
    (hne : matrixCoefficientSubmodule (R := R) (C := C) (M := M) ≠
      matrixCoefficientSubmodule (R := R) (C := C) (M := N))
    (f : Hom R C M N) : f = 0 := by
  by_contra hf
  exact hne (matrixCoefficientSubmodule_eq_of_ne_zero hf)

end Ring

section AlgClosed

variable {k C M : Type*} [Field k] [IsAlgClosed k]
  [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup M] [Module k M] [Comodule k C M]
  [IsSimpleOrder (Subcomodule k C M)]

/-- **Schur's lemma over an algebraically closed field.** Every comodule endomorphism of a simple
comodule is a scalar multiple of the identity. -/
theorem Hom.exists_eq_smul_id (f : Hom k C M M) : ∃ c : k, f = c • Hom.id k C M := by
  have : IsSimpleModule (WithConv (C →ₗ[k] k)) M := isSimpleModule_convolution_iff.mpr inferInstance
  have : Module.Finite k M := finite_of_isSimpleOrder (R := k) (C := C) (M := M)
  let c : k :=
    TauCeti.endAlgEquivSelfOfIsSimpleModule (k := k) (A := WithConv (C →ₗ[k] k)) (S := M)
      f.toConvolutionLinearMap
  refine ⟨c, Hom.ext fun m ↦ ?_⟩
  have hm := TauCeti.endAlgEquivSelfOfIsSimpleModule_smul (k := k)
    (A := WithConv (C →ₗ[k] k)) (S := M) f.toConvolutionLinearMap m
  rw [Hom.smul_apply, Hom.id_apply, ← Hom.toConvolutionLinearMap_apply]
  exact hm.symm

end AlgClosed

end TauCeti.Comodule

namespace Module.Basis

open TauCeti TauCeti.Comodule

section RingIntertwiner

variable {R A M N ι κ : Type*} [CommRing R] [Ring A] [Algebra R A] [Coalgebra R A]
  [AddCommGroup M] [Module R M] [Comodule R A M]
  [AddCommGroup N] [Module R N] [Comodule R A N]
  [Fintype ι] [Fintype κ]

/-- Simple comodules with the same coefficient space are intertwined by a scalar matrix whose
column-vector multiplication map is bijective. -/
theorem exists_mulVec_bijective_coefficientMatrix_mul_eq [Module.Projective R A]
    [IsSimpleOrder (Subcomodule R A M)] [IsSimpleOrder (Subcomodule R A N)]
    (b : Basis ι R M) (c : Basis κ R N)
    (heq : matrixCoefficientSubmodule (R := R) (C := A) (M := M) =
      matrixCoefficientSubmodule (R := R) (C := A) (M := N)) :
    ∃ T : Matrix κ ι R, Function.Bijective T.mulVec ∧
      coefficientMatrix (C := A) c * T.map (algebraMap R A) =
        T.map (algebraMap R A) * coefficientMatrix (C := A) b := by
  classical
  have : Module.Free R M := Module.Free.of_basis b
  obtain ⟨f, hf⟩ := (matrixCoefficientSubmodule_eq_iff (R := R) (C := A) (M := M) (N := N)).mp heq
  have hbij : Function.Bijective f := f.bijective_or_eq_zero.resolve_right hf
  refine ⟨LinearMap.toMatrix b c f.toLinearMap, ?_, f.coefficientMatrix_mul_toMatrix b c⟩
  have hrepr : ((LinearMap.toMatrix b c) f.toLinearMap).mulVec =
      c.equivFun ∘ f ∘ b.equivFun.symm := by
    funext v
    have h := LinearMap.toMatrix_mulVec_repr b c f.toLinearMap (b.equivFun.symm v)
    simpa only [Function.comp_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply,
      Comodule.Hom.coe_toLinearMap] using h
  rw [hrepr]
  exact (c.equivFun.bijective.comp hbij).comp b.equivFun.symm.bijective

end RingIntertwiner

section AlgClosed

variable {k A M ι : Type*} [Field k] [IsAlgClosed k]
  [Ring A] [Algebra k A] [Coalgebra k A]
  [AddCommGroup M] [Module k M] [Comodule k A M]
  [IsSimpleOrder (Subcomodule k A M)] [Fintype ι] [DecidableEq ι]

/-- **Matrix Schur's lemma.** Over an algebraically closed field, any scalar matrix commuting with
the coefficient matrix of a simple comodule is a scalar multiple of the identity matrix. -/
theorem exists_eq_smul_one_of_coefficientMatrix_mul_eq (b : Basis ι k M) {T : Matrix ι ι k}
    (hT : coefficientMatrix (C := A) b * T.map (algebraMap k A) =
      T.map (algebraMap k A) * coefficientMatrix (C := A) b) :
    ∃ c : k, T = c • (1 : Matrix ι ι k) := by
  let f : M →ₗ[k] M := (LinearMap.toMatrix b b).symm T
  have hf_mat : LinearMap.toMatrix b b f = T := (LinearMap.toMatrix b b).apply_symm_apply T
  have hcoact : TensorProduct.map f LinearMap.id ∘ₗ coact (R := k) (C := A) =
      coact (R := k) (C := A) ∘ₗ f :=
    (b.map_coact_iff_coefficientMatrix b f).mpr (by simpa [hf_mat] using hT)
  obtain ⟨c, hc⟩ := (⟨f, hcoact⟩ : Comodule.Hom k A M M).exists_eq_smul_id
  refine ⟨c, ?_⟩
  have hf_eq : f = c • LinearMap.id := congrArg Comodule.Hom.toLinearMap hc
  rw [← hf_mat, hf_eq, map_smul, LinearMap.toMatrix_id]

end AlgClosed

end Module.Basis
