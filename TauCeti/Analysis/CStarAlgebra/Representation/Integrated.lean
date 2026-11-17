/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Vector-valued integrated forms of C⋆-algebra representations

For a Hilbert-space C⋆-algebra representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` and a strongly
continuous contractive operator family `U : X → (H →L[ℂ] H)` over a topological measure space `X`,
the vector-valued integrated form sends `f : C_c(X, A)` to the bounded operator
`v ↦ ∫ x, π (f x) (U x v) ∂μ`. Integration is taken in `H` rather than in operator norm because
strong continuity of `U` does not imply norm continuity.

This construction needs no group structure, action, covariance, separability, second countability,
or σ-finiteness — only a measure `μ` finite on compact sets — and is shared by untwisted covariant
representations and cocycle-twisted covariant pairs.

## Main declarations

* `NonUnitalStarAlgHom.integral_apply`: vector evaluation commutes with Bochner integration.
* `NonUnitalStarAlgHom.continuous_apply_apply`, `hasCompactSupport_apply_apply`, and
  `integrable_apply_apply_of_hasCompactSupport`: regularity of `x ↦ π (f x) (u x)`.
* `NonUnitalStarAlgHom.vectorIntegratedOperator`: the integrated linear map
  `C_c(X, A) →ₗ[ℂ] (H →L[ℂ] H)`, with `vectorIntegratedOperator_apply`,
  `norm_vectorIntegratedOperator_le`, `inner_vectorIntegratedOperator_apply`, and
  `vectorIntegratedOperator_smul`.

## References

* Dana P. Williams, *Crossed Products of C*-Algebras*, AMS Mathematical Surveys and Monographs
  134 (2007), Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported InnerProductSpace CStarAlgebra

namespace NonUnitalStarAlgHom

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}

/-- Vector evaluation of a C⋆-representation commutes with Bochner integration. -/
theorem integral_apply {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {F : X → A} (hF : Integrable F ν) (w : H) :
    ∫ x, π (F x) w ∂ν = π (∫ x, F x ∂ν) w :=
  ((ContinuousLinearMap.apply ℂ H w).comp
    { toLinearMap := (π : A →ₗ[ℂ] (H →L[ℂ] H)), cont := map_continuous π }).integral_comp_comm hF

variable {X : Type*} [TopologicalSpace X]

/-- The vector-valued map `x ↦ π (f x) (u x)` is continuous when `f` and `u` are continuous. -/
@[fun_prop]
theorem continuous_apply_apply {f : X → A} {u : X → H} (hf : Continuous f) (hu : Continuous u) :
    Continuous fun x => π (f x) (u x) :=
  (map_continuous π |>.comp hf).clm_apply hu

/-- The vector-valued map `x ↦ π (f x) (u x)` has compact support when `f` has compact support. -/
theorem hasCompactSupport_apply_apply {f : X → A} (hf : HasCompactSupport f) (u : X → H) :
    HasCompactSupport fun x => π (f x) (u x) :=
  hf.mono fun _ hx hz => hx (by simp [hz])

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A continuous compactly supported coefficient function `f` and continuous vector family `u`
yield a Bochner integrable map `x ↦ π (f x) (u x)`. -/
theorem integrable_apply_apply_of_hasCompactSupport {f : X → A} (hf_cont : Continuous f)
    (hf_supp : HasCompactSupport f) {u : X → H} (hu : Continuous u)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] :
    Integrable (fun x => π (f x) (u x)) μ :=
  (π.continuous_apply_apply hf_cont hu).integrable_of_hasCompactSupport
    (π.hasCompactSupport_apply_apply hf_supp u)

private theorem norm_integral_vectorIntegrand_le {U : X → (H →L[ℂ] H)} {v : H}
    (hU_norm : ∀ x, ‖U x v‖ ≤ ‖v‖) (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (f : C_c(X, A)) :
    ‖∫ x, π (f x) (U x v) ∂μ‖ ≤ (∫ x, ‖f x‖ ∂μ) * ‖v‖ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (.of_forall fun x => ?_)
  exact ((π (f x)).le_opNorm _).trans <|
    mul_le_mul (norm_apply_le π (f x)) (hU_norm x) (norm_nonneg _) (norm_nonneg _)

variable (π) in
/-- The vector-valued integrated form on `C_c(X, A)` for a C⋆-representation `π` and strongly
continuous contractive operator family `U`: `f ↦ (v ↦ ∫ x, π (f x) (U x v) ∂μ)`. -/
def vectorIntegratedOperator (U : X → (H →L[ℂ] H))
    (hU_cont : ∀ v, Continuous fun x => U x v) (hU_norm : ∀ x v, ‖U x v‖ ≤ ‖v‖)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] : C_c(X, A) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun f := LinearMap.mkContinuous
    { toFun v := ∫ x, π (f x) (U x v) ∂μ
      map_add' v w := by
        simp_rw [map_add]
        exact integral_add
          (π.integrable_apply_apply_of_hasCompactSupport (map_continuous f) f.hasCompactSupport
            (hU_cont v) μ)
          (π.integrable_apply_apply_of_hasCompactSupport (map_continuous f) f.hasCompactSupport
            (hU_cont w) μ)
      map_smul' c _ := by simp_rw [map_smul]; exact integral_smul c _ }
    (∫ x, ‖f x‖ ∂μ) (fun v => π.norm_integral_vectorIntegrand_le (fun x => hU_norm x v) μ f)
  map_add' f h := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.add_apply, map_add,
      add_apply]
    exact integral_add
      (π.integrable_apply_apply_of_hasCompactSupport (map_continuous f) f.hasCompactSupport
        (hU_cont v) μ)
      (π.integrable_apply_apply_of_hasCompactSupport (map_continuous h) h.hasCompactSupport
        (hU_cont v) μ)
  map_smul' c f := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.smul_apply, map_smul,
      smul_apply, RingHom.id_apply]
    exact integral_smul c _

section Lemmas

variable {U : X → (H →L[ℂ] H)} {hU_cont : ∀ v, Continuous fun x => U x v}
  {hU_norm : ∀ x v, ‖U x v‖ ≤ ‖v‖} {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- The defining vector formula for `vectorIntegratedOperator`. -/
theorem vectorIntegratedOperator_apply (f : C_c(X, A)) (v : H) :
    π.vectorIntegratedOperator U hU_cont hU_norm μ f v = ∫ x, π (f x) (U x v) ∂μ := (rfl)

/-- The operator norm of `vectorIntegratedOperator` is bounded by the `L¹` norm of `f`. -/
theorem norm_vectorIntegratedOperator_le (f : C_c(X, A)) :
    ‖π.vectorIntegratedOperator U hU_cont hU_norm μ f‖ ≤ ∫ x, ‖f x‖ ∂μ :=
  ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
    (fun v => π.norm_integral_vectorIntegrand_le (fun x => hU_norm x v) μ f)

/-- Matrix coefficients of `vectorIntegratedOperator` equal integrals of matrix coefficients. -/
theorem inner_vectorIntegratedOperator_apply (f : C_c(X, A)) (w v : H) :
    ⟪w, π.vectorIntegratedOperator U hU_cont hU_norm μ f v⟫_ℂ =
      ∫ x, ⟪w, π (f x) (U x v)⟫_ℂ ∂μ := by
  rw [vectorIntegratedOperator_apply, integral_inner
    (π.integrable_apply_apply_of_hasCompactSupport (map_continuous f) f.hasCompactSupport
      (hU_cont v) μ)]

/-- Left multiplication by a coefficient pulls out of `vectorIntegratedOperator` as `π a * ·`. -/
@[simp]
theorem vectorIntegratedOperator_smul (a : A) (f : C_c(X, A)) :
    π.vectorIntegratedOperator U hU_cont hU_norm μ (a • f) =
      π a * π.vectorIntegratedOperator U hU_cont hU_norm μ f := by
  ext v
  simpa only [vectorIntegratedOperator_apply, CompactlySupportedContinuousMap.smul_apply,
    smul_eq_mul, map_mul, mul_apply_eq_comp] using (π a).integral_comp_comm
      (π.integrable_apply_apply_of_hasCompactSupport (map_continuous f) f.hasCompactSupport
        (hU_cont v) μ)

end Lemmas

end NonUnitalStarAlgHom
