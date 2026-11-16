/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.PiTensorProduct.Projective.Normed
public import TauCeti.Analysis.Normed.Module.TensorProduct.Completion

/-!
# Binary and finite-family projective tensor products

The projective tensor product of a family indexed by `Unit ⊕ Unit` is isometrically the binary
projective tensor product of its two factors. Combining this identification with the norm
comparison identifies the locally convex completed construction on two normed factors with
`CompletedProjectiveTensor`. The comparison preserves pure tensors, including after completion.

The algebraic identification uses Mathlib's `PiTensorProduct.tmulEquivDep` and
`PiTensorProduct.subsingletonEquiv`. The seminorm bounds come from the maximality of the two
projective seminorms; no separation or completeness hypothesis on the factors is needed.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, §2.1.
-/

public section

open scoped TensorProduct
open UniformSpace

namespace TauCeti.ProjectiveTensor

variable {𝕜 : Type*} [NormedField 𝕜]
variable {E : Unit ⊕ Unit → Type*} [∀ i, SeminormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)]

private def binaryLinearEquiv :
    (⨂[𝕜] i, E i) ≃ₗ[𝕜] ProjectiveTensor 𝕜 (E (.inl ())) (E (.inr ())) :=
  ((PiTensorProduct.tmulEquivDep 𝕜 E).symm.trans
    (TensorProduct.congr (PiTensorProduct.subsingletonEquiv ())
      (PiTensorProduct.subsingletonEquiv ()))).trans (linearEquiv 𝕜 _ _).symm

private theorem binaryLinearEquiv_tprod (x : ∀ i, E i) :
    binaryLinearEquiv (⨂ₜ[𝕜] i, x i) = ⟨x (.inl ()) ⊗ₜ x (.inr ())⟩ := by
  simp [binaryLinearEquiv, PiTensorProduct.tmulEquivDep_symm_apply,
    PiTensorProduct.subsingletonEquiv_apply_tprod]

private theorem binaryLinearEquiv_symm_tmul (x : E (.inl ())) (y : E (.inr ())) :
    binaryLinearEquiv.symm (⟨x ⊗ₜ y⟩ : ProjectiveTensor 𝕜 _ _) =
      ⨂ₜ[𝕜] i, Sum.rec (fun | () => x) (fun | () => y) i := by
  apply binaryLinearEquiv.injective
  simp [binaryLinearEquiv_tprod]

/-- The finite-family and binary projective tensor products agree isometrically. -/
noncomputable def piTensorEquiv :
    (⨂[𝕜] i, E i) ≃ₗᵢ[𝕜] ProjectiveTensor 𝕜 (E (.inl ())) (E (.inr ())) :=
  LinearIsometryEquiv.ofBounds binaryLinearEquiv
    (fun u => by
      simpa only [PiTensorProduct.projectiveSeminormOf_normSeminorm, coe_normSeminorm,
        Seminorm.comp_apply, LinearEquiv.coe_coe, one_mul] using
        PiTensorProduct.seminorm_le_mul_projectiveSeminormOf
          (fun i => normSeminorm 𝕜 (E i))
          ((normSeminorm 𝕜 (ProjectiveTensor 𝕜 (E (.inl ())) (E (.inr ())))).comp
            binaryLinearEquiv.toLinearMap)
          zero_le_one (fun x => by
            simpa [binaryLinearEquiv_tprod, norm_def, Fintype.prod_sum_type] using
              TensorProduct.projectiveSeminorm_tmul_le (𝕜 := 𝕜) (x (.inl ())) (x (.inr ()))) u)
    (fun u => by
      simpa only [one_mul, coe_normSeminorm, LinearMap.comp_apply, LinearEquiv.coe_coe,
        linearEquiv_symm_apply, ← norm_def] using
        TensorProduct.apply_le_mul_projectiveSeminorm
          (p := normSeminorm 𝕜 _)
          (f := binaryLinearEquiv.symm.toLinearMap.comp (linearEquiv 𝕜 _ _).symm.toLinearMap)
          zero_le_one (fun x y => by
            simpa [binaryLinearEquiv_symm_tmul, Fintype.prod_sum_type] using
              PiTensorProduct.projectiveSeminorm_tprod_le
                (𝕜 := 𝕜) (E := E)
                (Sum.rec (fun | () => x) (fun | () => y))) u.toTensorProduct)

/-- The isometric comparison sends a family pure tensor to the binary pure tensor. -/
@[simp]
theorem piTensorEquiv_tprod (x : ∀ i, E i) :
    piTensorEquiv (⨂ₜ[𝕜] i, x i) = ⟨x (.inl ()) ⊗ₜ x (.inr ())⟩ :=
  binaryLinearEquiv_tprod x

/-- The inverse isometric comparison recovers a family pure tensor. -/
@[simp]
theorem piTensorEquiv_symm_tmul (x : ∀ i, E i) :
    piTensorEquiv.symm (⟨x (.inl ()) ⊗ₜ x (.inr ())⟩ : ProjectiveTensor 𝕜 _ _) =
      ⨂ₜ[𝕜] i, x i := by
  apply piTensorEquiv.injective
  simp

end TauCeti.ProjectiveTensor

namespace TauCeti.CompletedProjectiveTensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Unit ⊕ Unit → Type*} [∀ i, SeminormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)]

/-- The locally convex completed tensor of two normed spaces agrees with the binary Banach
projective tensor product, by the canonical pure-tensor comparison. -/
noncomputable def binaryNormEquiv :
    CompletedProjectiveTensorProduct (fun i (_ : Unit) => normSeminorm 𝕜 (E i)) ≃L[𝕜]
      CompletedProjectiveTensor 𝕜 (E (.inl ())) (E (.inr ())) :=
  normEquiv.trans ProjectiveTensor.piTensorEquiv.completion.toContinuousLinearEquiv

/-- The completed binary comparison preserves pure tensors. -/
@[simp]
theorem binaryNormEquiv_tprod (x : ∀ i, E i) :
    binaryNormEquiv
      ((⟨⨂ₜ[𝕜] i, x i⟩ : ProjectiveTensorProduct
        (fun i (_ : Unit) => normSeminorm 𝕜 (E i))) : CompletedProjectiveTensorProduct _) =
      ((⟨x (.inl ()) ⊗ₜ x (.inr ())⟩ : ProjectiveTensor 𝕜 _ _) :
        CompletedProjectiveTensor 𝕜 (E (.inl ())) (E (.inr ()))) := by
  simp [binaryNormEquiv]

/-- The inverse completed comparison recovers the completed family pure tensor. -/
@[simp]
theorem binaryNormEquiv_symm_tmul (x : ∀ i, E i) :
    binaryNormEquiv.symm
      ((⟨x (.inl ()) ⊗ₜ x (.inr ())⟩ : ProjectiveTensor 𝕜 _ _) :
        CompletedProjectiveTensor 𝕜 (E (.inl ())) (E (.inr ()))) =
      ((⟨⨂ₜ[𝕜] i, x i⟩ : ProjectiveTensorProduct
        (fun i (_ : Unit) => normSeminorm 𝕜 (E i))) : CompletedProjectiveTensorProduct _) := by
  apply binaryNormEquiv.injective
  simp

end TauCeti.CompletedProjectiveTensorProduct
