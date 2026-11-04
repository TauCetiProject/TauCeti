/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Representation.PolarizedMeasure
public import TauCeti.MeasureTheory.Function.BoundedBorel
import TauCeti.MeasureTheory.Function.ContinuousApproximation

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

The assignment `f ↦ T_f` extends `π`: `T_f = π f` for continuous `f`. It is a unital star algebra
homomorphism, hence contractive (`NonUnitalStarAlgHom.norm_apply_le`). Multiplicativity and star
preservation hold for continuous symbols because `π` is a star homomorphism, and pass to bounded
Borel symbols by approximation in `L¹` of the variations of the polarized measures
(`TauCeti.BoundedBorelFunction.eq_of_forall_ofContinuousMap_eq`): matrix elements of `T_f`
depend Lipschitz-continuously on `f` for these `L¹` distances. Multiplicativity is first proved
when one factor is continuous, then in general. So a representation of `C(K, ℂ)` extends to a
representation of the bounded Borel symbols; its values on indicators of Borel sets are the
projections of the representation's projection-valued measure.

## Main declarations

* `StarAlgHom.representationBorelOperator π`: the star algebra homomorphism `f ↦ T_f`.
* `StarAlgHom.inner_representationBorelOperator`: the matrix elements of `T_f`.
* `StarAlgHom.representationBorelOperator_ofContinuousMap`: `T_f = π f` for continuous `f`.
* `StarAlgHom.integral_representationPolarizedMeasure_representationBorelOperator`: the weighted
  matrix-element identity `∫ f dμ_(ψ, T_g ξ) = ∫ f g dμ_(ψ,ξ)`.
* `StarAlgHom.commute_representationBorelOperator`: an operator commuting with `π` commutes with
  every `T_g`.
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

/-- The operator of a bounded Borel symbol, before its algebraic laws are recorded. -/
private def representationBorelOperatorAux (f : BoundedBorelFunction K) : H →L[ℂ] H :=
  (InnerProductSpace.continuousLinearMapOfBilin (representationBorelForm π f)).adjoint

private theorem inner_representationBorelOperatorAux (f : BoundedBorelFunction K) (ψ ξ : H) :
    ⟪ψ, representationBorelOperatorAux π f ξ⟫_ℂ =
      ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; representationPolarizedMeasure π ψ ξ] := by
  rw [representationBorelOperatorAux, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply, representationBorelForm_apply]

private theorem representationBorelOperatorAux_add (f g : BoundedBorelFunction K) :
    representationBorelOperatorAux π (f + g) =
      representationBorelOperatorAux π f + representationBorelOperatorAux π g :=
  ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => by
    rw [_root_.add_apply, inner_add_right, inner_representationBorelOperatorAux,
      inner_representationBorelOperatorAux, inner_representationBorelOperatorAux]
    simp only [BoundedBorelFunction.coe_add, Pi.add_apply]
    exact VectorMeasure.integral_add (f.integrable _) (g.integrable _)

private theorem representationBorelOperatorAux_ofContinuousMap (g : C(K, ℂ)) :
    representationBorelOperatorAux π (BoundedBorelFunction.ofContinuousMap g) = π g :=
  ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => by
    rw [inner_representationBorelOperatorAux, BoundedBorelFunction.coe_ofContinuousMap,
      integral_representationPolarizedMeasure]

/-- Matrix elements of `T_f` are `1`-Lipschitz in `f` for the `L¹` distance against the variation
of the polarized measure. -/
private theorem dist_inner_representationBorelOperatorAux_le (ψ ξ : H)
    (f g : BoundedBorelFunction K) :
    dist ⟪ψ, representationBorelOperatorAux π f ξ⟫_ℂ ⟪ψ, representationBorelOperatorAux π g ξ⟫_ℂ ≤
      1 * ∫ x, ‖f x - g x‖ ∂(representationPolarizedMeasure π ψ ξ).variation := by
  rw [dist_eq_norm, inner_representationBorelOperatorAux, inner_representationBorelOperatorAux,
    ← VectorMeasure.integral_fun_sub (f.integrable _) (g.integrable _)]
  refine VectorMeasure.norm_integral_le_integral_norm.trans ?_
  gcongr
  exact ContinuousLinearMap.opNorm_mul_le ℝ ℂ

/-- Matrix elements of `T_(f a)` are `‖a‖`-Lipschitz in `f` for the `L¹` distance against the
variation of the polarized measure. -/
private theorem dist_inner_representationBorelOperatorAux_mul_le (ψ ξ : H)
    (a f g : BoundedBorelFunction K) :
    dist ⟪ψ, representationBorelOperatorAux π (f * a) ξ⟫_ℂ
        ⟪ψ, representationBorelOperatorAux π (g * a) ξ⟫_ℂ ≤
      ‖a‖ * ∫ x, ‖f x - g x‖ ∂(representationPolarizedMeasure π ψ ξ).variation := by
  refine (dist_inner_representationBorelOperatorAux_le π ψ ξ _ _).trans ?_
  rw [one_mul, ← MeasureTheory.integral_const_mul]
  refine integral_mono ((f * a - g * a).integrable _).norm
    (((f - g).integrable _).norm.const_mul _) fun x => ?_
  simp only [BoundedBorelFunction.mul_apply, ← sub_mul, norm_mul, mul_comm ‖a‖]
  exact mul_le_mul_of_nonneg_left (a.norm_coe_le_norm x) (norm_nonneg _)

/-- Star preservation of `f ↦ T_f`: it holds for continuous symbols since `π` preserves stars,
and passes to bounded Borel symbols by `L¹` approximation. -/
private theorem representationBorelOperatorAux_star (f : BoundedBorelFunction K) :
    representationBorelOperatorAux π (star f) = star (representationBorelOperatorAux π f) := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  -- The matrix element of the adjoint `T_f†` is the conjugate of a matrix element of `T_f`.
  have hadj (f : BoundedBorelFunction K) :
      ⟪ψ, star (representationBorelOperatorAux π f) ξ⟫_ℂ =
        starRingEnd ℂ ⟪ξ, representationBorelOperatorAux π f ψ⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      inner_conj_symm]
  refine congrFun (BoundedBorelFunction.eq_of_forall_ofContinuousMap_eq
    (ν₁ := (representationPolarizedMeasure π ψ ξ).variation)
    (ν₂ := (representationPolarizedMeasure π ξ ψ).variation) (C₁ := 1) (C₂ := 1)
    (Φ := fun f => ⟪ψ, representationBorelOperatorAux π (star f) ξ⟫_ℂ)
    (Ψ := fun f => ⟪ψ, star (representationBorelOperatorAux π f) ξ⟫_ℂ)
    (fun f g => ?_) (fun f g => ?_) fun g => ?_) f
  · refine (dist_inner_representationBorelOperatorAux_le π ψ ξ _ _).trans_eq ?_
    simp only [BoundedBorelFunction.star_apply, ← star_sub, norm_star]
  · rw [hadj, hadj, Complex.dist_conj_conj]
    exact dist_inner_representationBorelOperatorAux_le π ξ ψ f g
  · simp only [← map_star, representationBorelOperatorAux_ofContinuousMap]

/-- Multiplicativity of `f ↦ T_f` when the left factor is continuous. The matrix element
`⟪ψ, π h T_g ξ⟫` is `⟪(π h)† ψ, T_g ξ⟫`, which is Lipschitz in `g`, so the identity passes from
continuous to bounded Borel `g`. -/
private theorem representationBorelOperatorAux_ofContinuousMap_mul (h : C(K, ℂ))
    (g : BoundedBorelFunction K) :
    representationBorelOperatorAux π (BoundedBorelFunction.ofContinuousMap h * g) =
      π h * representationBorelOperatorAux π g := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  rw [mul_comm, mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left (π h)]
  refine congrFun (BoundedBorelFunction.eq_of_forall_ofContinuousMap_eq
    (ν₁ := (representationPolarizedMeasure π ψ ξ).variation)
    (ν₂ := (representationPolarizedMeasure π (ContinuousLinearMap.adjoint (π h) ψ) ξ).variation)
    (Φ := fun g => ⟪ψ, representationBorelOperatorAux π (g * .ofContinuousMap h) ξ⟫_ℂ)
    (Ψ := fun g => ⟪ContinuousLinearMap.adjoint (π h) ψ, representationBorelOperatorAux π g ξ⟫_ℂ)
    (dist_inner_representationBorelOperatorAux_mul_le π ψ ξ _)
    (dist_inner_representationBorelOperatorAux_le π _ ξ) fun g => ?_) g
  rw [← map_mul, representationBorelOperatorAux_ofContinuousMap,
    representationBorelOperatorAux_ofContinuousMap, ContinuousLinearMap.adjoint_inner_left,
    ← mul_apply_eq_comp, ← map_mul, mul_comm]

/-- Multiplicativity of `f ↦ T_f`. The matrix element `⟪ψ, T_f T_g ξ⟫` is Lipschitz in `f`, so the
continuous case `representationBorelOperatorAux_ofContinuousMap_mul` extends to bounded Borel
`f`. -/
private theorem representationBorelOperatorAux_mul (f g : BoundedBorelFunction K) :
    representationBorelOperatorAux π (f * g) =
      representationBorelOperatorAux π f * representationBorelOperatorAux π g := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  refine congrFun (BoundedBorelFunction.eq_of_forall_ofContinuousMap_eq
    (ν₁ := (representationPolarizedMeasure π ψ ξ).variation)
    (ν₂ := (representationPolarizedMeasure π ψ (representationBorelOperatorAux π g ξ)).variation)
    (Φ := fun f => ⟪ψ, representationBorelOperatorAux π (f * g) ξ⟫_ℂ)
    (Ψ := fun f => ⟪ψ, (representationBorelOperatorAux π f *
      representationBorelOperatorAux π g) ξ⟫_ℂ)
    (dist_inner_representationBorelOperatorAux_mul_le π ψ ξ g)
    (fun f f' => dist_inner_representationBorelOperatorAux_le π ψ _ f f') fun h => ?_) f
  simp only [representationBorelOperatorAux_ofContinuousMap_mul,
    representationBorelOperatorAux_ofContinuousMap]

/-- The **Borel extension** of a representation `π` of `C(K, ℂ)`: the bounded operator `T_f`
assigned to a bounded Borel symbol `f`, determined by its matrix elements
`⟪ψ, T_f ξ⟫ = ∫ f dμ_(ψ,ξ)` against the polarized measures (`inner_representationBorelOperator`).
It is a unital star algebra homomorphism that agrees with `π` on continuous symbols
(`representationBorelOperator_ofContinuousMap`). -/
def representationBorelOperator : BoundedBorelFunction K →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := representationBorelOperatorAux π
  map_one' := by
    rw [← map_one BoundedBorelFunction.ofContinuousMap,
      representationBorelOperatorAux_ofContinuousMap, map_one]
  map_mul' := representationBorelOperatorAux_mul π
  map_zero' := by simpa using representationBorelOperatorAux_add π 0 0
  map_add' := representationBorelOperatorAux_add π
  commutes' c := by
    rw [← AlgHomClass.commutes BoundedBorelFunction.ofContinuousMap c,
      representationBorelOperatorAux_ofContinuousMap, AlgHomClass.commutes]
  map_star' := representationBorelOperatorAux_star π

/-- **Matrix elements of the Borel extension.** `⟪ψ, T_f ξ⟫ = ∫ f dμ_(ψ,ξ)`. -/
theorem inner_representationBorelOperator (f : BoundedBorelFunction K) (ψ ξ : H) :
    ⟪ψ, representationBorelOperator π f ξ⟫_ℂ =
      ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; representationPolarizedMeasure π ψ ξ] :=
  inner_representationBorelOperatorAux π f ψ ξ

/-- The Borel extension of `π` agrees with `π` on continuous symbols. -/
@[simp]
theorem representationBorelOperator_ofContinuousMap (g : C(K, ℂ)) :
    representationBorelOperator π (BoundedBorelFunction.ofContinuousMap g) = π g :=
  representationBorelOperatorAux_ofContinuousMap π g

/-- **Weighted matrix elements.** Integrating `f` against the polarized measure `μ_(ψ, T_g ξ)` is
integrating `f g` against `μ_(ψ,ξ)`, since both are `⟪ψ, T_f T_g ξ⟫`. This is the integrated form
of the identity `μ_(ψ, T_g ξ) = g · μ_(ψ,ξ)`. -/
theorem integral_representationPolarizedMeasure_representationBorelOperator
    (f g : BoundedBorelFunction K) (ψ ξ : H) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ;
        representationPolarizedMeasure π ψ (representationBorelOperator π g ξ)] =
      ∫ᵛ x, f x * g x ∂[ContinuousLinearMap.mul ℝ ℂ; representationPolarizedMeasure π ψ ξ] := by
  rw [← inner_representationBorelOperator, ← mul_apply_eq_comp, ← map_mul,
    inner_representationBorelOperator, BoundedBorelFunction.coe_mul]
  rfl

/-- **Commutant of the Borel extension.** An operator commuting with `π f` for every continuous
`f` commutes with `T_g` for every bounded Borel symbol `g`: the matrix elements
`⟪A† ψ, T_g ξ⟫` and `⟪ψ, T_g (A ξ)⟫` are Lipschitz in `g` for `L¹` distances and agree on continuous
symbols. -/
theorem commute_representationBorelOperator {A : H →L[ℂ] H} (hA : ∀ f : C(K, ℂ), Commute A (π f))
    (g : BoundedBorelFunction K) : Commute A (representationBorelOperator π g) := by
  rw [commute_iff_eq]
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left A]
  refine congrFun (BoundedBorelFunction.eq_of_forall_ofContinuousMap_eq
    (ν₁ := (representationPolarizedMeasure π (ContinuousLinearMap.adjoint A ψ) ξ).variation)
    (ν₂ := (representationPolarizedMeasure π ψ (A ξ)).variation)
    (Φ := fun g => ⟪ContinuousLinearMap.adjoint A ψ, representationBorelOperatorAux π g ξ⟫_ℂ)
    (Ψ := fun g => ⟪ψ, representationBorelOperatorAux π g (A ξ)⟫_ℂ)
    (dist_inner_representationBorelOperatorAux_le π _ ξ)
    (dist_inner_representationBorelOperatorAux_le π ψ _) fun f => ?_) g
  rw [representationBorelOperatorAux_ofContinuousMap, ContinuousLinearMap.adjoint_inner_left,
    ← mul_apply_eq_comp, (hA f).eq, mul_apply_eq_comp]

end StarAlgHom
