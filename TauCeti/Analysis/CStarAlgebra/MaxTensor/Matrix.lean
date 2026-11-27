/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.MinTensorNorm

/-!
# Uniqueness of the C*-norm on `M_n ⊙ A`

If the algebraic tensor product `A ⊗[ℂ] B` of two C*-algebras is carried bijectively onto a
C*-algebra `D` by a star homomorphism `Φ`, then every star homomorphism `Ψ` from `A ⊗[ℂ] B` into a
C*-algebra satisfies `‖Ψ x‖ ≤ ‖Φ x‖`, with equality when `Ψ` is injective
(`TauCeti.norm_apply_eq_of_bijective`): `Ψ ∘ Φ⁻¹` is a star homomorphism between C*-algebras, hence
contractive, and isometric when injective. So `A ⊗[ℂ] B` carries exactly one C*-norm, and every
supremum norm `TauCeti.supTensorNorm` over a family of commuting pairs containing one with injective
integrated form is `‖Φ x‖` (`TauCeti.supTensorNorm_eq_norm_of_bijective`); in particular
`‖x‖_min = ‖x‖_max = ‖Φ x‖` (`TauCeti.minTensorNorm_eq_norm_of_bijective`,
`TauCeti.maxTensorNorm_eq_norm_of_bijective`).

The matrix algebra is the example: `M_n(ℂ) ⊗[ℂ] A → M_n(A)`, `m ⊗ a ↦ [mᵢⱼ a]`
(`TauCeti.cstarMatrixTensorHom`), is a bijective star homomorphism for every, possibly non-unital,
C*-algebra `A`, with inverse `x ↦ Σᵢⱼ Eᵢⱼ ⊗ xᵢⱼ`. Hence `M_n ⊙ A` has a unique C*-norm, and both the
minimal and the maximal norm of `Σ Eᵢⱼ ⊗ aᵢⱼ` are the `CStarMatrix` norm of `[aᵢⱼ]`
(`TauCeti.minTensorNorm_cstarMatrix`, `TauCeti.maxTensorNorm_cstarMatrix`).

## Main declarations

* `TauCeti.norm_apply_eq_of_bijective`: uniqueness of the C*-norm on `A ⊗[ℂ] B` when it is a
  C*-algebra.
* `TauCeti.cstarMatrixTensorHom`, `TauCeti.cstarMatrixTensorHom_bijective`:
  `M_n(ℂ) ⊗[ℂ] A ≅ M_n(A)`.
* `TauCeti.minTensorNorm_cstarMatrix`, `TauCeti.maxTensorNorm_cstarMatrix`: both norms on
  `M_n(ℂ) ⊗[ℂ] A` are the `CStarMatrix` norm, and `TauCeti.minTensorNorm_cstarMatrixTensorInv`,
  `TauCeti.maxTensorNorm_cstarMatrixTensorInv`: both norms of `Σ Eᵢⱼ ⊗ aᵢⱼ` are `‖[aᵢⱼ]‖`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.9.4.2.
-/

public section

noncomputable section

open TensorProduct
open scoped ComplexOrder

universe u v w

namespace TauCeti

section Unique

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {D : Type w} [NonUnitalCStarAlgebra D] {Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] D}

/-- If a star homomorphism `Φ` carries `A ⊗[ℂ] B` bijectively onto a C*-algebra, every star
homomorphism `Ψ` from `A ⊗[ℂ] B` into a C*-algebra satisfies `‖Ψ x‖ ≤ ‖Φ x‖`. -/
theorem norm_apply_le_of_bijective (hΦ : Function.Bijective Φ) {C : Type*}
    [NonUnitalCStarAlgebra C] (Ψ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) (x : A ⊗[ℂ] B) : ‖Ψ x‖ ≤ ‖Φ x‖ := by
  let e := StarAlgEquiv.ofBijective Φ hΦ
  let g : D →⋆ₙₐ[ℂ] A ⊗[ℂ] B := NonUnitalStarAlgHom.ofClass e.symm
  have hg : g (Φ x) = x := e.symm_apply_apply x
  have h := NonUnitalStarAlgHom.norm_apply_le (Ψ.comp g) (Φ x)
  rwa [NonUnitalStarAlgHom.comp_apply, hg] at h

/-- **Uniqueness of the C*-norm.** If a star homomorphism `Φ` carries `A ⊗[ℂ] B` bijectively onto
a C*-algebra, every injective star homomorphism `Ψ` from `A ⊗[ℂ] B` into a C*-algebra satisfies
`‖Ψ x‖ = ‖Φ x‖`. -/
theorem norm_apply_eq_of_bijective (hΦ : Function.Bijective Φ) {C : Type*}
    [NonUnitalCStarAlgebra C] {Ψ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C} (hΨ : Function.Injective Ψ)
    (x : A ⊗[ℂ] B) : ‖Ψ x‖ = ‖Φ x‖ := by
  let e := StarAlgEquiv.ofBijective Φ hΦ
  let g : D →⋆ₙₐ[ℂ] A ⊗[ℂ] B := NonUnitalStarAlgHom.ofClass e.symm
  have hg : g (Φ x) = x := e.symm_apply_apply x
  have h := NonUnitalStarAlgHom.norm_map (Ψ.comp g) (hΨ.comp e.symm.injective) (Φ x)
  rwa [NonUnitalStarAlgHom.comp_apply, hg] at h

/-- If a star homomorphism `Φ` carries `A ⊗[ℂ] B` bijectively onto a C*-algebra, the supremum norm
over a family of commuting pairs one of which has injective integrated form is `‖Φ x‖`. -/
theorem supTensorNorm_eq_norm_of_bijective (hΦ : Function.Bijective Φ) {ι : Sort*}
    (f : ι → CommutingRepresentationPair A B) (hf : ∃ i, Function.Injective (f i).tensorHom)
    (x : A ⊗[ℂ] B) : supTensorNorm f x = ‖Φ x‖ := by
  obtain ⟨i, hi⟩ := hf
  refine le_antisymm (supTensorNorm_le_of_forall f (norm_nonneg _) fun j ↦
    norm_apply_le_of_bijective hΦ (f j).tensorHom x) ?_
  rw [← norm_apply_eq_of_bijective hΦ hi x]
  exact norm_tensorHom_le_supTensorNorm f i x

/-- If a star homomorphism `Φ` carries `A ⊗[ℂ] B` bijectively onto a C*-algebra, the maximal norm
is `‖Φ x‖`. -/
theorem maxTensorNorm_eq_norm_of_bijective (hΦ : Function.Bijective Φ) (x : A ⊗[ℂ] B) :
    maxTensorNorm A B x = ‖Φ x‖ := by
  refine le_antisymm (maxTensorNorm_le_of_forall fun p ↦ norm_apply_le_of_bijective hΦ _ x) ?_
  obtain ⟨p, hp⟩ := CommutingRepresentationPair.exists_tensorHom_injective A B
  rw [← norm_apply_eq_of_bijective hΦ hp x]
  exact norm_tensorHom_le_maxTensorNorm p x

/-- If a star homomorphism `Φ` carries `A ⊗[ℂ] B` bijectively onto a C*-algebra, the minimal norm
is `‖Φ x‖`. -/
theorem minTensorNorm_eq_norm_of_bijective (hΦ : Function.Bijective Φ) (x : A ⊗[ℂ] B) :
    minTensorNorm A B x = ‖Φ x‖ := by
  refine le_antisymm (minTensorNorm_le_of_forall fun p ↦ ?_) ?_
  · rw [← CommutingRepresentationPair.tensorHom_spatial]
    exact norm_apply_le_of_bijective hΦ _ x
  · obtain ⟨p, hp, -⟩ :=
      RepresentationPair.exists_tensorHom_spatial_injective_and_norm_tensorHom_spatial_tmul A B
    rw [← norm_apply_eq_of_bijective hΦ hp x, CommutingRepresentationPair.tensorHom_spatial]
    exact norm_spatialTensorHom_le_minTensorNorm _ _ x

end Unique

section Matrix

variable (n : Type) [Fintype n] [DecidableEq n] (A : Type u) [NonUnitalCStarAlgebra A]

section Algebraic

/-- The bilinear map `(m, a) ↦ [mᵢⱼ a]` from `M_n(ℂ) × A` to `M_n(A)`. -/
def cstarMatrixTensorBilin : CStarMatrix n n ℂ →ₗ[ℂ] A →ₗ[ℂ] CStarMatrix n n A :=
  LinearMap.mk₂ ℂ (fun m a ↦ CStarMatrix.ofMatrix fun i j ↦ m i j • a)
    (fun _ _ _ ↦ CStarMatrix.ext fun _ _ ↦ add_smul _ _ _)
    (fun _ _ _ ↦ CStarMatrix.ext fun _ _ ↦ mul_smul _ _ _)
    (fun _ _ _ ↦ CStarMatrix.ext fun _ _ ↦ smul_add _ _ _)
    (fun _ _ _ ↦ CStarMatrix.ext fun _ _ ↦ smul_comm _ _ _)

omit [Fintype n] [DecidableEq n] in
variable {n A} in
@[simp]
theorem cstarMatrixTensorBilin_apply (m : CStarMatrix n n ℂ) (a : A) (i j : n) :
    cstarMatrixTensorBilin n A m a i j = m i j • a :=
  (rfl)

/-- The star homomorphism `M_n(ℂ) ⊗[ℂ] A → M_n(A)`, `m ⊗ a ↦ [mᵢⱼ a]`. -/
def cstarMatrixTensorHom : CStarMatrix n n ℂ ⊗[ℂ] A →⋆ₙₐ[ℂ] CStarMatrix n n A where
  toFun := TensorProduct.lift (cstarMatrixTensorBilin n A)
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]
    | tmul m a =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
      | tmul m' a' =>
        refine CStarMatrix.ext fun i j ↦ ?_
        simp [CStarMatrix.mul_apply, Finset.sum_smul, smul_mul_smul_comm]
  map_star' x := by
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [star_add, map_add, h₁, h₂]
    | tmul m a =>
      refine CStarMatrix.ext fun i j ↦ ?_
      simp [CStarMatrix.star_apply, star_smul]

variable {n A}

@[simp]
theorem cstarMatrixTensorHom_tmul (m : CStarMatrix n n ℂ) (a : A) (i j : n) :
    cstarMatrixTensorHom n A (m ⊗ₜ a) i j = m i j • a :=
  (rfl)

/-- The inverse `x ↦ Σᵢⱼ Eᵢⱼ ⊗ xᵢⱼ` of `TauCeti.cstarMatrixTensorHom`. -/
def cstarMatrixTensorInv (x : CStarMatrix n n A) : CStarMatrix n n ℂ ⊗[ℂ] A :=
  ∑ i, ∑ j, CStarMatrix.ofMatrix (Matrix.single i j (1 : ℂ)) ⊗ₜ x i j

theorem cstarMatrixTensorHom_cstarMatrixTensorInv (x : CStarMatrix n n A) :
    cstarMatrixTensorHom n A (cstarMatrixTensorInv x) = x := by
  refine CStarMatrix.ext fun k l ↦ ?_
  simp [cstarMatrixTensorInv, map_sum, CStarMatrix.sum_apply, CStarMatrix.ofMatrix_apply,
    Matrix.single_apply, ite_smul, ite_and]

theorem cstarMatrixTensorInv_cstarMatrixTensorHom (x : CStarMatrix n n ℂ ⊗[ℂ] A) :
    cstarMatrixTensorInv (cstarMatrixTensorHom n A x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ =>
    simp only [cstarMatrixTensorInv] at h₁ h₂ ⊢
    simp only [map_add, CStarMatrix.add_apply, TensorProduct.tmul_add, Finset.sum_add_distrib, h₁,
      h₂]
  | tmul m a =>
    have hm : ∑ i, ∑ j, m i j • CStarMatrix.ofMatrix (Matrix.single i j (1 : ℂ)) = m := by
      refine CStarMatrix.ext fun k l ↦ ?_
      simp [CStarMatrix.sum_apply, CStarMatrix.ofMatrix_apply, Matrix.single_apply, ite_and]
    conv_rhs => rw [← hm]
    simp only [cstarMatrixTensorInv, cstarMatrixTensorHom_tmul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.sum_tmul]

/-- `M_n(ℂ) ⊗[ℂ] A → M_n(A)` is bijective. -/
theorem cstarMatrixTensorHom_bijective : Function.Bijective (cstarMatrixTensorHom n A) :=
  Function.bijective_iff_has_inverse.2 ⟨cstarMatrixTensorInv,
    cstarMatrixTensorInv_cstarMatrixTensorHom, cstarMatrixTensorHom_cstarMatrixTensorInv⟩

end Algebraic

variable [PartialOrder A] [StarOrderedRing A]

/-- **The minimal norm on `M_n ⊙ A`** is the `CStarMatrix` norm: `‖Σ Eᵢⱼ ⊗ aᵢⱼ‖_min = ‖[aᵢⱼ]‖`
(Blackadar II.9.4.2). -/
theorem minTensorNorm_cstarMatrix (x : CStarMatrix n n ℂ ⊗[ℂ] A) :
    minTensorNorm (CStarMatrix n n ℂ) A x = ‖cstarMatrixTensorHom n A x‖ :=
  minTensorNorm_eq_norm_of_bijective (Φ := cstarMatrixTensorHom n A)
    cstarMatrixTensorHom_bijective x

/-- **The maximal norm on `M_n ⊙ A`** is the `CStarMatrix` norm: `‖Σ Eᵢⱼ ⊗ aᵢⱼ‖_max = ‖[aᵢⱼ]‖`
(Blackadar II.9.4.2). -/
theorem maxTensorNorm_cstarMatrix (x : CStarMatrix n n ℂ ⊗[ℂ] A) :
    maxTensorNorm (CStarMatrix n n ℂ) A x = ‖cstarMatrixTensorHom n A x‖ :=
  maxTensorNorm_eq_norm_of_bijective (Φ := cstarMatrixTensorHom n A)
    cstarMatrixTensorHom_bijective x

/-- Both norms of `Σᵢⱼ Eᵢⱼ ⊗ aᵢⱼ` are the `CStarMatrix` norm of `[aᵢⱼ]`: the minimal norm. -/
theorem minTensorNorm_cstarMatrixTensorInv (x : CStarMatrix n n A) :
    minTensorNorm (CStarMatrix n n ℂ) A (cstarMatrixTensorInv x) = ‖x‖ := by
  rw [minTensorNorm_cstarMatrix, cstarMatrixTensorHom_cstarMatrixTensorInv]

/-- Both norms of `Σᵢⱼ Eᵢⱼ ⊗ aᵢⱼ` are the `CStarMatrix` norm of `[aᵢⱼ]`: the maximal norm. -/
theorem maxTensorNorm_cstarMatrixTensorInv (x : CStarMatrix n n A) :
    maxTensorNorm (CStarMatrix n n ℂ) A (cstarMatrixTensorInv x) = ‖x‖ := by
  rw [maxTensorNorm_cstarMatrix, cstarMatrixTensorHom_cstarMatrixTensorInv]

end Matrix

end TauCeti
