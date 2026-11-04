/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Representation.PolarizedMeasure
public import TauCeti.MeasureTheory.Function.BoundedBorel

/-!
# Bounded Borel symbols acting through a continuous-function representation

Let `π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)` be a unital star representation on a complex Hilbert space,
with `K` compact Hausdorff, and let `μ_(ψ,ξ)` be its polarized complex measures
(`StarAlgHom.representationPolarizedMeasure`), with `∫ g dμ_(ψ,ξ) = ⟪ψ, π g ξ⟫` for continuous
`g`. A bounded Borel symbol `f` on `K` defines the sesquilinear form

`(ψ, ξ) ↦ ∫ f dμ_(ψ,ξ)`,

bounded by `2 ‖f‖ ‖ψ‖ ‖ξ‖` because the total variation of `μ_(ψ,ξ)` is at most `2 ‖ψ‖ ‖ξ‖`.
By the Riesz representation of bounded sesquilinear forms
(`InnerProductSpace.continuousLinearMapOfBilin`) and the adjoint, it is the form of a unique
bounded operator `T_f` with

`⟪ψ, T_f ξ⟫ = ∫ f dμ_(ψ,ξ)`.

The assignment `f ↦ T_f` is `ℂ`-linear and extends `π`: `T_f = π f` for continuous `f`. So a
representation of `C(K, ℂ)` acts on all bounded Borel symbols, in particular on the indicators of
Borel sets.

## Main declarations

* `StarAlgHom.representationBorelOperator π`: the linear map `f ↦ T_f`.
* `StarAlgHom.inner_representationBorelOperator`: the matrix elements of `T_f`.
* `StarAlgHom.representationBorelOperator_ofContinuousMap`: `T_f = π f` for continuous `f`.
* `StarAlgHom.norm_integral_representationPolarizedMeasure_le`: the bound on the sesquilinear
  form.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.1.
-/

public section

noncomputable section

open MeasureTheory MeasureTheory.VectorMeasure TauCeti
open scoped InnerProductSpace

namespace StarAlgHom

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [BorelSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- The integral of a bounded Borel symbol `f` against the polarized measure `μ_(ψ,ξ)` is at most
`2 ‖f‖ ‖ψ‖ ‖ξ‖` in norm. -/
theorem norm_integral_representationPolarizedMeasure_le (f : BoundedBorelFunction K) (ψ ξ : H) :
    ‖∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; representationPolarizedMeasure π ψ ξ]‖ ≤
      2 * ‖f‖ * ‖ψ‖ * ‖ξ‖ := by
  refine (VectorMeasure.norm_integral_le_of_norm_le_const (ae_of_all _ f.norm_coe_le_norm)).trans ?_
  have hvar : (representationPolarizedMeasure π ψ ξ).variation.real Set.univ ≤ 2 * ‖ψ‖ * ‖ξ‖ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity)
      (variation_representationPolarizedMeasure_univ_le π ψ ξ)
  calc ‖f‖ * ‖ContinuousLinearMap.mul ℝ ℂ‖ *
        (representationPolarizedMeasure π ψ ξ).variation.real Set.univ
      ≤ ‖f‖ * 1 * (2 * ‖ψ‖ * ‖ξ‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_mul_le ℝ ℂ
    _ = 2 * ‖f‖ * ‖ψ‖ * ‖ξ‖ := by ring

/-- The bounded sesquilinear form `(ψ, ξ) ↦ ∫ f dμ_(ψ,ξ)` of a bounded Borel symbol. -/
private def representationBorelForm (f : BoundedBorelFunction K) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun ψ ξ => ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; representationPolarizedMeasure π ψ ξ])
    (fun ψ ψ' ξ => by
      rw [representationPolarizedMeasure_add_left, integral_add_vectorMeasure
        (f.integrable _) (f.integrable _)])
    (fun c ψ ξ => by
      rw [representationPolarizedMeasure_smul_left, integral_smul_vectorMeasure_mul,
        smul_eq_mul, starRingEnd_apply])
    (fun ψ ξ ξ' => by
      rw [representationPolarizedMeasure_add_right, integral_add_vectorMeasure
        (f.integrable _) (f.integrable _)])
    (fun c ψ ξ => by
      rw [representationPolarizedMeasure_smul_right, integral_smul_vectorMeasure_mul,
        smul_eq_mul, RingHom.id_apply])).mkContinuous₂
    (2 * ‖f‖) (norm_integral_representationPolarizedMeasure_le π f)

private theorem representationBorelForm_apply (f : BoundedBorelFunction K) (ψ ξ : H) :
    representationBorelForm π f ψ ξ =
      ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; representationPolarizedMeasure π ψ ξ] :=
  rfl

/-- The operator of a bounded Borel symbol, before linearity in the symbol is recorded. -/
private def representationBorelOperatorAux (f : BoundedBorelFunction K) : H →L[ℂ] H :=
  (InnerProductSpace.continuousLinearMapOfBilin (representationBorelForm π f)).adjoint

private theorem inner_representationBorelOperatorAux (f : BoundedBorelFunction K) (ψ ξ : H) :
    ⟪ψ, representationBorelOperatorAux π f ξ⟫_ℂ =
      ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; representationPolarizedMeasure π ψ ξ] := by
  rw [representationBorelOperatorAux, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply, representationBorelForm_apply]

/-- The **Borel extension** of a representation `π` of `C(K, ℂ)`: the bounded operator `T_f`
assigned to a bounded Borel symbol `f`, determined by its matrix elements
`⟪ψ, T_f ξ⟫ = ∫ f dμ_(ψ,ξ)` against the polarized measures (`inner_representationBorelOperator`).
It agrees with `π` on continuous symbols (`representationBorelOperator_ofContinuousMap`). -/
def representationBorelOperator : BoundedBorelFunction K →ₗ[ℂ] (H →L[ℂ] H) where
  toFun := representationBorelOperatorAux π
  map_add' f g := ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => by
    rw [_root_.add_apply, inner_add_right, inner_representationBorelOperatorAux,
      inner_representationBorelOperatorAux, inner_representationBorelOperatorAux]
    simp only [BoundedBorelFunction.coe_add, Pi.add_apply]
    exact VectorMeasure.integral_add (f.integrable _)
      (g.integrable _)
  map_smul' c f := ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => by
    rw [_root_.smul_apply, inner_smul_right, inner_representationBorelOperatorAux,
      inner_representationBorelOperatorAux, RingHom.id_apply]
    simp only [BoundedBorelFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul _ c f

/-- **Matrix elements of the Borel extension.** `⟪ψ, T_f ξ⟫ = ∫ f dμ_(ψ,ξ)`. -/
theorem inner_representationBorelOperator (f : BoundedBorelFunction K) (ψ ξ : H) :
    ⟪ψ, representationBorelOperator π f ξ⟫_ℂ =
      ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; representationPolarizedMeasure π ψ ξ] :=
  inner_representationBorelOperatorAux π f ψ ξ

/-- The Borel extension of `π` agrees with `π` on continuous symbols. -/
@[simp]
theorem representationBorelOperator_ofContinuousMap (g : C(K, ℂ)) :
    representationBorelOperator π (BoundedBorelFunction.ofContinuousMap g) = π g :=
  ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => by
    rw [inner_representationBorelOperator, BoundedBorelFunction.coe_ofContinuousMap,
      integral_representationPolarizedMeasure]

end StarAlgHom
