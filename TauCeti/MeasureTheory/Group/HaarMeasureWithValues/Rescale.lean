/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Convolution

/-!
# Rescaling an `A`-valued Haar measure

For `c ∈ A` and an `A`-valued Haar measure `μ`, `c • μ` is the Haar measure `K ↦ c μ(K)`
(`TauCeti.HaarMeasureWithValues.smul_apply`). Integrals and convolutions rescale accordingly:
`∫ f d(cμ) = c ∫ f dμ` and `f₁ ⋆_{cμ} f₂ = c (f₁ ⋆_μ f₂)`. For a unit `c`, multiplication by `c`
is therefore a ring isomorphism `H(G, cμ) ≃ H(G, μ)` of Hecke algebras
(`TauCeti.HeckeAlgebra.rescaleRingEquiv`): the Hecke algebra does not depend, up to isomorphism, on
the normalisation of the Haar measure.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.1, pp. 11–12.
-/

public section

open LocallyConstant

namespace TauCeti

variable {A G : Type*} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

namespace HaarMeasureWithValues

section Semiring

variable [Semiring A]

/-- The rescaled Haar measure `c • μ : K ↦ c μ(K)`. -/
instance instSMul : SMul A (HaarMeasureWithValues A G) :=
  ⟨fun c μ ↦
    { toFun K := c * μ K
      map_bot' := by rw [μ.apply_bot, mul_zero]
      map_sup' K L h := by rw [μ.apply_sup h, mul_add]
      map_smul' g K := by rw [μ.apply_smul] }⟩

/-- The rescaled Haar measure gives `K` the volume `c μ(K)`. -/
@[simp]
theorem smul_apply (c : A) (μ : HaarMeasureWithValues A G) (K : TopologicalSpace.CompactOpens G) :
    (c • μ) K = c * μ K :=
  (rfl)

end Semiring

variable [CommSemiring A] [T2Space G] {M : Type*} [AddCommMonoid M] [Module A M]
  (μ : HaarMeasureWithValues A G)

/-- **Integrals against a rescaled measure**: `∫ f d(cμ) = c ∫ f dμ`. -/
theorem integral_smul_measure (c : A) (f : compactlySupported A G M) :
    (c • μ).integral f = c • μ.integral f := by
  have h := eq_integral_of_apply_compactOpenIndicator (c • μ)
      (c • μ.integral : compactlySupported A G M →ₗ[A] M) fun K m ↦ by
    rw [LinearMap.smul_apply, integral_compactOpenIndicator, smul_apply, smul_smul]
  exact (LinearMap.congr_fun h f).symm

variable [IsTopologicalGroup G]

/-- **Convolution against a rescaled measure**: `f₁ ⋆_{cμ} f₂ = c (f₁ ⋆_μ f₂)`. -/
theorem convolution_smul_measure (c : A) (f₁ f₂ : compactlySupported A G A) :
    (c • μ).convolution f₁ f₂ = c • μ.convolution f₁ f₂ := by
  ext x
  rw [convolution_apply, integral_smul_measure, Submodule.coe_smul, LocallyConstant.coe_smul,
    Pi.smul_apply, convolution_apply]

end HaarMeasureWithValues

namespace HeckeAlgebra

variable [CommSemiring A] [IsTopologicalGroup G] [T2Space G] (μ : HaarMeasureWithValues A G)

/-- **Rescaling the Haar measure by a unit does not change the Hecke algebra**: multiplication by
`c` is a ring isomorphism `H(G, cμ) ≃ H(G, μ)`, since
`(c f₁) ⋆_μ (c f₂) = c (c (f₁ ⋆_μ f₂)) = c (f₁ ⋆_{cμ} f₂)`. -/
noncomputable def rescaleRingEquiv (c : Aˣ) :
    HeckeAlgebra ((c : A) • μ) ≃+* HeckeAlgebra μ where
  toFun f := ⟨(c : A) • f.toCompactlySupported⟩
  invFun f := ⟨((c⁻¹ : Aˣ) : A) • f.toCompactlySupported⟩
  left_inv f := by
    ext1
    simp [smul_smul]
  right_inv f := by
    ext1
    simp [smul_smul]
  map_mul' f₁ f₂ := by
    ext1
    simp [HaarMeasureWithValues.convolution_smul_measure, smul_smul]
  map_add' f₁ f₂ := by
    ext1
    simp

/-- `rescaleRingEquiv μ c` multiplies the underlying function by `c`. -/
@[simp]
theorem toCompactlySupported_rescaleRingEquiv (c : Aˣ) (f : HeckeAlgebra ((c : A) • μ)) :
    (rescaleRingEquiv μ c f).toCompactlySupported = (c : A) • f.toCompactlySupported :=
  (rfl)

/-- The inverse of `rescaleRingEquiv μ c` multiplies the underlying function by `c⁻¹`. -/
@[simp]
theorem toCompactlySupported_rescaleRingEquiv_symm (c : Aˣ) (f : HeckeAlgebra μ) :
    ((rescaleRingEquiv μ c).symm f).toCompactlySupported =
      ((c⁻¹ : Aˣ) : A) • f.toCompactlySupported :=
  (rfl)

/-- `rescaleRingEquiv μ c` is `A`-linear. -/
theorem rescaleRingEquiv_smul (c : Aˣ) (a : A) (f : HeckeAlgebra ((c : A) • μ)) :
    rescaleRingEquiv μ c (a • f) = a • rescaleRingEquiv μ c f := by
  ext1
  simp [toCompactlySupported_smul, smul_comm a (c : A)]

end HeckeAlgebra

end TauCeti
