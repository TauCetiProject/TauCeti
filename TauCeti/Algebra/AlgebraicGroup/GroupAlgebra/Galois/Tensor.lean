/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.BaseChange
import TauCeti.Algebra.TensorProduct.BaseChange
import TauCeti.RepresentationTheory.GaloisDescent.Range
import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor products of invariant group algebras

For a finite Galois extension `L/k`, the tensor square over `k` of the invariant group algebra
is the invariant subalgebra of the tensor square over `L` of the split group algebra. The
comparison sends `x ⊗ y` to the tensor of their inclusions. Its inverse converts the
invariant-valued comultiplication into a comultiplication with values in the tensor square
of the descended algebra.

There is no finite-generation assumption on the exponent group and no characteristic
restriction. The proof uses the scalar-extension equivalence for the invariant group algebra
and the compatibility of scalar extension with tensor products.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open scoped TensorProduct TauCeti.GaloisDescent

namespace TauCeti.GaloisDescent

variable {k L M : Type*} [Field k] [Field L] [Algebra k L] [AddCommGroup M]

/-- The tensor of the invariant-algebra inclusions, with the ambient tensor product over `L`. -/
private noncomputable def tensorInclusion (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho →ₐ[k]
      MonoidAlgebra L (Multiplicative M) ⊗[L] MonoidAlgebra L (Multiplicative M) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft (R := L) (S := L)).restrictScalars k).comp
      (groupAlgebraInvariants rho).val)
    (((Algebra.TensorProduct.includeRight (R := L)).restrictScalars k).comp
      (groupAlgebraInvariants rho).val)
    (fun _ _ ↦ Commute.all _ _)

@[simp]
private theorem tensorInclusion_tmul (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x y : groupAlgebraInvariants rho) :
    tensorInclusion rho (x ⊗ₜ[k] y) =
      (x : MonoidAlgebra L (Multiplicative M)) ⊗ₜ[L]
        (y : MonoidAlgebra L (Multiplicative M)) := by
  simp [tensorInclusion]

private theorem tensorInclusion_mem (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho) :
    tensorInclusion rho x ∈ groupAlgebraTensorInvariants rho := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [tensorInclusion_tmul, mem_groupAlgebraTensorInvariants_iff,
        groupAlgebraTensorActionSemilinearEquiv_tmul]
      intro σ
      rw [(mem_groupAlgebraInvariants_iff rho x).mp x.property σ,
        (mem_groupAlgebraInvariants_iff rho y).mp y.property σ]
  | add x y hx hy => simpa only [map_add] using
      (groupAlgebraTensorInvariants rho).add_mem hx hy

variable [FiniteDimensional k L] [IsGalois k L]

private theorem liftEquiv_tensorInclusion_bijective
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Function.Bijective (AlgHom.liftEquiv k L _ _ (tensorInclusion rho)) := by
  let e := (Algebra.TensorProduct.baseChangeTensorAlgEquiv k L
    (groupAlgebraInvariants rho) (groupAlgebraInvariants rho)).trans
      (Algebra.TensorProduct.congr (groupAlgebraInvariantsBaseChangeEquiv rho)
        (groupAlgebraInvariantsBaseChangeEquiv rho))
  have he : AlgHom.liftEquiv k L _ _ (tensorInclusion rho) = e.toAlgHom := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [e, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  rw [he]
  exact e.bijective

/-- The diagonal semilinear tensor action, regarded as a `k`-linear representation. -/
private noncomputable def tensorRepresentation
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Representation k (L ≃ₐ[k] L)
      (MonoidAlgebra L (Multiplicative M) ⊗[L] MonoidAlgebra L (Multiplicative M)) where
  toFun σ :=
    { toFun := groupAlgebraTensorActionSemilinearEquiv rho σ
      map_add' := map_add _
      map_smul' r x := by
        rw [← IsScalarTower.algebraMap_smul L r x,
          groupAlgebraTensorActionSemilinearEquiv_smul, σ.commutes,
          IsScalarTower.algebraMap_smul]
        rfl }
  map_one' := by ext x; exact groupAlgebraTensorActionSemilinearEquiv_one rho x
  map_mul' σ τ := by ext x; exact groupAlgebraTensorActionSemilinearEquiv_mul rho σ τ x

private theorem tensorInclusion_range (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    LinearMap.range (tensorInclusion rho).toLinearMap =
      (groupAlgebraTensorInvariants rho).toSubmodule := by
  have he : (AlgHom.liftEquiv k L _ _ (tensorInclusion rho)).toLinearMap =
      (tensorInclusion rho).toLinearMap.liftBaseChange L := by
    apply TensorProduct.AlgebraTensorModule.ext
    intros
    simp
  have hf : Function.Surjective ((tensorInclusion rho).toLinearMap.liftBaseChange L) := by
    rw [← he]
    exact (liftEquiv_tensorInclusion_bijective rho).surjective
  have hinv : (tensorRepresentation rho).invariants =
      (groupAlgebraTensorInvariants rho).toSubmodule := by
    ext x
    simp [Representation.mem_invariants, tensorRepresentation]
  rw [← hinv]
  exact range_eq_invariants_of_liftBaseChange_surjective
    (ρ := tensorRepresentation rho)
    (groupAlgebraTensorActionSemilinearEquiv_smul rho)
    (fun σ x ↦ (mem_groupAlgebraTensorInvariants_iff rho _).mp
      (tensorInclusion_mem rho x) σ) hf

private theorem tensorInclusion_injective (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Function.Injective (tensorInclusion rho) := by
  intro x y h
  apply Algebra.TensorProduct.includeRight_injective (A := L)
    (FaithfulSMul.algebraMap_injective k L)
  apply (liftEquiv_tensorInclusion_bijective rho).injective
  simpa only [Algebra.TensorProduct.includeRight_apply, AlgHom.liftEquiv_tmul, one_smul]
    using h

/-- The tensor square of the descended group algebra is the invariant subalgebra of the
split tensor square, for the diagonal semilinear Galois action. -/
noncomputable def groupAlgebraInvariantsTensorEquiv
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho ≃ₐ[k]
      groupAlgebraTensorInvariants rho :=
  AlgEquiv.ofBijective
    ((tensorInclusion rho).codRestrict _ (tensorInclusion_mem rho))
    ⟨(AlgHom.injective_codRestrict _ _ _).mpr (tensorInclusion_injective rho), by
      intro x
      obtain ⟨y, hy⟩ := (tensorInclusion_range rho).ge x.property
      exact ⟨y, Subtype.ext hy⟩⟩

/-- The tensor descent equivalence sends a pure tensor to the tensor of its inclusions. -/
@[simp]
theorem groupAlgebraInvariantsTensorEquiv_tmul
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (x y : groupAlgebraInvariants rho) :
    (groupAlgebraInvariantsTensorEquiv rho (x ⊗ₜ[k] y) :
        MonoidAlgebra L (Multiplicative M) ⊗[L] MonoidAlgebra L (Multiplicative M)) =
      (x : MonoidAlgebra L (Multiplicative M)) ⊗ₜ[L]
        (y : MonoidAlgebra L (Multiplicative M)) := by
  exact (congrArg Subtype.val (AlgEquiv.ofBijective_apply _ _ _)).trans
    ((AlgHom.coe_codRestrict _ _ _ _).trans (tensorInclusion_tmul rho x y))

/-- The inverse comparison recovers the tensor of invariant elements from their ambient
tensor, independently of the proof of invariance. -/
@[simp]
theorem groupAlgebraInvariantsTensorEquiv_symm_tmul
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (x y : groupAlgebraInvariants rho)
    (h : (x : MonoidAlgebra L (Multiplicative M)) ⊗ₜ[L]
      (y : MonoidAlgebra L (Multiplicative M)) ∈ groupAlgebraTensorInvariants rho) :
    (groupAlgebraInvariantsTensorEquiv rho).symm ⟨_, h⟩ = x ⊗ₜ[k] y := by
  apply (groupAlgebraInvariantsTensorEquiv rho).injective
  apply Subtype.ext
  simp

end TauCeti.GaloisDescent
