/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.Analysis.Normed.Module.TensorProduct.FiniteDimension
public import TauCeti.LinearAlgebra.Determinant.TensorProduct

/-!
# The normalized determinant of a complex-linear automorphism

The determinant of a complex-linear automorphism `A` is a nonzero complex number, so it is
`‖det A‖` times the point `det A / ‖det A‖` of the unit circle
(`ContinuousLinearEquiv.normalizedDet`). The normalized determinant depends continuously on `A`,
so a loop of automorphisms gives a loop on the circle; its degree is the winding number of the
loop of determinants.

## Main declarations

* `ContinuousLinearEquiv.normalizedDet`: the point `det A / ‖det A‖` of the circle.
* `ContinuousLinearEquiv.det_eq_norm_mul_normalizedDet`: `det A = ‖det A‖ * normalizedDet A`.
* `ContinuousLinearEquiv.normalizedDet_trans`, `ContinuousLinearEquiv.normalizedDet_refl`,
  `ContinuousLinearEquiv.normalizedDet_symm`: the normalized determinant is multiplicative.
* `ContinuousLinearEquiv.normalizedDet_trans_trans_symm`: it is invariant under conjugation by an
  isomorphism `E' ≃ E`.
* `ContinuousLinearEquiv.normalizedDet_prodCongr`: the normalized determinant of `A × B` is the
  product of those of `A` and `B`.
* `ContinuousLinearEquiv.normalizedDet_eq_pow_mul_pow_of_apply_tmul`: the normalized determinant
  of `A₁ ⊗ A₂` on the projective tensor product is
  `normalizedDet A₁ ^ dim E₂ * normalizedDet A₂ ^ dim E₁`.
* `Continuous.normalizedDet`, `ContinuousOn.normalizedDet`: a continuous family of automorphisms
  has continuous normalized determinant.
-/

public section

namespace ContinuousLinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The normalized determinant `det A / ‖det A‖` of a complex-linear automorphism, a point of the
circle. -/
noncomputable def normalizedDet (A : E ≃L[ℂ] E) : Circle :=
  ⟨LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) / ‖LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E)‖,
    mem_sphere_zero_iff_norm.2 (by simp [A.toLinearEquiv.isUnit_det'.ne_zero])⟩

/-- The normalized determinant, as a complex number. -/
@[simp]
theorem coe_normalizedDet (A : E ≃L[ℂ] E) :
    (A.normalizedDet : ℂ) =
      LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) /
        ‖LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E)‖ :=
  (rfl)

/-- The determinant of an automorphism is its modulus times its normalized determinant. -/
theorem det_eq_norm_mul_normalizedDet (A : E ≃L[ℂ] E) :
    LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) =
      ‖LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E)‖ * (A.normalizedDet : ℂ) := by
  have hd : LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  rw [coe_normalizedDet, mul_div_cancel₀ _ (by simpa using hd)]

/-- The normalized determinant of a composite is the product of the normalized determinants. -/
@[simp]
theorem normalizedDet_trans (A B : E ≃L[ℂ] E) :
    (A.trans B).normalizedDet = A.normalizedDet * B.normalizedDet := by
  have hdet : LinearMap.det ((A.trans B).toLinearEquiv : E →ₗ[ℂ] E) =
      LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) *
        LinearMap.det (B.toLinearEquiv : E →ₗ[ℂ] E) := by
    rw [ContinuousLinearEquiv.trans_toLinearEquiv, LinearEquiv.coe_trans, LinearMap.det_comp,
      mul_comm]
  ext1
  simp only [coe_normalizedDet, Circle.coe_mul, hdet, norm_mul, Complex.ofReal_mul]
  ring

/-- The identity has normalized determinant `1`. -/
@[simp]
theorem normalizedDet_refl : (ContinuousLinearEquiv.refl ℂ E).normalizedDet = 1 := by
  have h : ((ContinuousLinearEquiv.refl ℂ E).toLinearEquiv : E →ₗ[ℂ] E) = LinearMap.id :=
    LinearMap.ext fun v ↦ refl_apply ℂ E v
  ext1
  simp [coe_normalizedDet, h]

/-- The normalized determinant of the inverse is the inverse of the normalized determinant. -/
@[simp]
theorem normalizedDet_symm (A : E ≃L[ℂ] E) : A.symm.normalizedDet = A.normalizedDet⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← normalizedDet_trans, self_trans_symm, normalizedDet_refl])

/-- The normalized determinant is invariant under conjugation: transporting an automorphism `A` of
`E` along an isomorphism `L : E' ≃ E` does not change it. -/
@[simp]
theorem normalizedDet_trans_trans_symm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (L : E' ≃L[ℂ] E) (A : E ≃L[ℂ] E) :
    (L.trans (A.trans L.symm)).normalizedDet = A.normalizedDet := by
  have hdet : LinearMap.det ((L.trans (A.trans L.symm)).toLinearEquiv : E' →ₗ[ℂ] E') =
      LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) :=
    LinearMap.det_conj (A.toLinearEquiv : E →ₗ[ℂ] E) L.symm.toLinearEquiv
  ext1
  simp only [coe_normalizedDet, hdet]

/-- The normalized determinant of a product of automorphisms is the product of their normalized
determinants. -/
@[simp]
theorem normalizedDet_prodCongr {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] (A : E ≃L[ℂ] E) (B : E' ≃L[ℂ] E') :
    (A.prodCongr B).normalizedDet = A.normalizedDet * B.normalizedDet := by
  have hdet : LinearMap.det ((A.prodCongr B).toLinearEquiv : E × E' →ₗ[ℂ] E × E') =
      LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) *
        LinearMap.det (B.toLinearEquiv : E' →ₗ[ℂ] E') :=
    LinearMap.det_prodMap _ _
  ext1
  simp only [coe_normalizedDet, Circle.coe_mul, hdet, norm_mul, Complex.ofReal_mul]
  ring

section TensorProduct

open Module
open scoped TensorProduct

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [FiniteDimensional ℂ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [FiniteDimensional ℂ E₂]

/-- An automorphism of the projective tensor product `E₁ ⊗ E₂` acting on pure tensors as
`A₁ ⊗ A₂` has normalized determinant `normalizedDet A₁ ^ dim E₂ * normalizedDet A₂ ^ dim E₁`. -/
theorem normalizedDet_eq_pow_mul_pow_of_apply_tmul
    {A : TauCeti.ProjectiveTensor ℂ E₁ E₂ ≃L[ℂ] TauCeti.ProjectiveTensor ℂ E₁ E₂}
    {A₁ : E₁ ≃L[ℂ] E₁} {A₂ : E₂ ≃L[ℂ] E₂} (h : ∀ v w, A ⟨v ⊗ₜ w⟩ = ⟨A₁ v ⊗ₜ A₂ w⟩) :
    A.normalizedDet = A₁.normalizedDet ^ finrank ℂ E₂ * A₂.normalizedDet ^ finrank ℂ E₁ := by
  set L := TauCeti.ProjectiveTensor.linearEquiv ℂ E₁ E₂
  -- Read through the underlying algebraic tensor product, `A` is `TensorProduct.map A₁ A₂`.
  have hconj : (L : TauCeti.ProjectiveTensor ℂ E₁ E₂ →ₗ[ℂ] E₁ ⊗[ℂ] E₂) ∘ₗ
      (A.toLinearEquiv :
        TauCeti.ProjectiveTensor ℂ E₁ E₂ →ₗ[ℂ] TauCeti.ProjectiveTensor ℂ E₁ E₂) ∘ₗ
        (L.symm : E₁ ⊗[ℂ] E₂ →ₗ[ℂ] TauCeti.ProjectiveTensor ℂ E₁ E₂) =
      TensorProduct.map (A₁.toLinearEquiv : E₁ →ₗ[ℂ] E₁) (A₂.toLinearEquiv : E₂ →ₗ[ℂ] E₂) :=
    TensorProduct.ext' fun v w ↦ by simp [L, h]
  have hdet : LinearMap.det (A.toLinearEquiv :
      TauCeti.ProjectiveTensor ℂ E₁ E₂ →ₗ[ℂ] TauCeti.ProjectiveTensor ℂ E₁ E₂) =
      LinearMap.det (A₁.toLinearEquiv : E₁ →ₗ[ℂ] E₁) ^ finrank ℂ E₂ *
        LinearMap.det (A₂.toLinearEquiv : E₂ →ₗ[ℂ] E₂) ^ finrank ℂ E₁ := by
    rw [← LinearMap.det_conj _ L, hconj, LinearMap.det_tensorProductMap]
  ext1
  simp only [coe_normalizedDet, Circle.coe_mul, Circle.coe_pow, hdet, norm_mul, norm_pow,
    Complex.ofReal_mul, Complex.ofReal_pow]
  ring

end TensorProduct

end ContinuousLinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous family of complex-linear automorphisms has a continuous family of normalized
determinants. -/
theorem Continuous.normalizedDet {X : Type*} [TopologicalSpace X] {A : X → E ≃L[ℂ] E}
    (hA : Continuous fun x => (A x : E →L[ℂ] E)) : Continuous fun x => (A x).normalizedDet := by
  have hd : Continuous fun x => LinearMap.det ((A x).toLinearEquiv : E →ₗ[ℂ] E) :=
    ContinuousLinearMap.continuous_det.comp hA
  refine Continuous.subtype_mk (hd.div (Complex.continuous_ofReal.comp hd.norm) fun x => ?_) _
  simpa using (A x).toLinearEquiv.isUnit_det'.ne_zero

/-- A family of complex-linear automorphisms that is continuous on a set has normalized
determinants that are continuous on that set. -/
theorem ContinuousOn.normalizedDet {X : Type*} [TopologicalSpace X] {A : X → E ≃L[ℂ] E}
    {s : Set X} (hA : ContinuousOn (fun x => (A x : E →L[ℂ] E)) s) :
    ContinuousOn (fun x => (A x).normalizedDet) s := by
  rw [continuousOn_iff_continuous_domRestrict] at hA ⊢
  exact Continuous.normalizedDet (A := fun x : s => A x) hA
