/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import TauCeti.Analysis.InnerProductSpace.StarAlgHom
public import TauCeti.MeasureTheory.Integral.ContinuousMap
public import TauCeti.Topology.ContinuousMap.CompactlySupported

/-!
# Diagonal Riesz measures for continuous-function representations

Let `π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)` be a unital star representation on a complex
Hilbert space, with `K` compact Hausdorff. For each `ξ : H`, the positive functional
`f ↦ ⟪ξ, π(f) ξ⟫` determines a finite regular Borel measure on `K`.

The measure is determined by the identity
`∫ f dμ_ξ = ⟪ξ, π f ξ⟫` for each continuous `f`. Its total mass is `‖ξ‖²`, and
`∫ ‖f‖² dμ_ξ = ‖π f ξ‖²`. The continuous functional calculus of a normal operator
specializes this construction: `ContinuousLinearMap.diagMeasure` is the
`StarAlgHom.representationDiagMeasure` of `cfcHom`.

## Main results

* `StarAlgHom.representationDiagMeasure`: the finite regular Riesz measure at a vector.
* `StarAlgHom.integral_representationDiagMeasure`: the continuous scalar integral identity.
* `StarAlgHom.eq_representationDiagMeasure_iff`: characterization among regular measures.
* `StarAlgHom.representationDiagMeasure_real_univ` and
  `StarAlgHom.representationDiagMeasure_univ`: total mass `‖ξ‖²`.
* `StarAlgHom.integral_norm_sq_representationDiagMeasure`: the squared `L²` identity.

The final identity uses `StarAlgHom.norm_sq_apply_eq_re_inner_star_mul`, a
quadratic identity for arbitrary star-algebra representations.
-/

public section

noncomputable section

open MeasureTheory ContinuousMap
open scoped InnerProductSpace ComplexOrder CompactlySupported

namespace StarAlgHom

variable {K : Type*} [TopologicalSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

-- The remaining diagonal-measure construction needs compactness and Borel measurability.
variable [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

/-- The positive real functional associated with a vector in a unital representation. -/
private def representationDiagFunctional (ξ : H) : C_c(K, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun g := RCLike.re ⟪ξ, π (g.toContinuousMap.realToRCLike ℂ) ξ⟫_ℂ
      map_add' g h := by
        -- The compact-support forgetful map, real-to-complex embedding, and π are additive.
        -- The inner product is additive in its right argument, and real part preserves sums.
        simp only [← realToRCLikeStarAlgHom_apply]
        rw [CompactlySupportedContinuousMap.toContinuousMap_add, map_add, map_add,
          _root_.add_apply, inner_add_right, map_add]
      map_smul' c g := by
        -- Real scalar multiplication passes through the embedding and π; the
        -- complex inner product is linear in the right argument.
        simp only [← realToRCLikeStarAlgHom_apply]
        rw [CompactlySupportedContinuousMap.toContinuousMap_smul, map_smul,
          ← algebraMap_smul ℂ c (M := C(K, ℂ)), map_smul,
          _root_.smul_apply, inner_smul_right]
        simp }
    fun g hg => by
      have hT : 0 ≤ π (g.toContinuousMap.realToRCLike ℂ) := by
        apply map_nonneg π
        intro x
        simpa using hg x
      exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).re_inner_nonneg_right ξ

omit [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] in
private theorem representationDiagFunctional_apply (ξ : H) (g : C_c(K, ℝ)) :
    representationDiagFunctional π ξ g =
      RCLike.re ⟪ξ, π (g.toContinuousMap.realToRCLike ℂ) ξ⟫_ℂ :=
  rfl

/-- The finite regular Riesz measure of the positive functional
`f ↦ ⟪ξ, π f ξ⟫`. For continuous `f`, it satisfies
`∫ f dμ_ξ = ⟪ξ, π f ξ⟫` and is unique among regular Borel measures. -/
def representationDiagMeasure (ξ : H) : Measure K :=
  RealRMK.rieszMeasure (representationDiagFunctional π ξ)

instance isFiniteMeasure_representationDiagMeasure (ξ : H) :
    IsFiniteMeasure (representationDiagMeasure π ξ) := by
  unfold representationDiagMeasure
  infer_instance

instance regular_representationDiagMeasure (ξ : H) :
    (representationDiagMeasure π ξ).Regular := by
  unfold representationDiagMeasure
  infer_instance

private theorem ofReal_integral_representationDiagMeasure (ξ : H) (g : C(K, ℝ)) :
    ((∫ x, g x ∂(representationDiagMeasure π ξ) : ℝ) : ℂ) =
      ⟪ξ, π (g.realToRCLike ℂ) ξ⟫_ℂ := by
  have h := RealRMK.integral_rieszMeasure (representationDiagFunctional π ξ)
    ⟨g, .of_compactSpace _⟩
  rw [CompactlySupportedContinuousMap.coe_mk, representationDiagFunctional_apply] at h
  have hsa : IsSelfAdjoint (π (g.realToRCLike ℂ)) :=
    (isSelfAdjoint_realToRCLike (𝕜 := ℂ) (f := g)).map π
  rw [representationDiagMeasure, h]
  exact RCLike.conj_eq_iff_re.mp ((inner_conj_symm _ _).trans (hsa.isSymmetric ξ ξ))

/-- Integrating a continuous function against the diagonal measure gives the scalar
matrix coefficient `⟪ξ, π f ξ⟫` for the fixed vector `ξ`. -/
theorem integral_representationDiagMeasure (ξ : H) (f : C(K, ℂ)) :
    ∫ x, f x ∂(representationDiagMeasure π ξ) = ⟪ξ, π f ξ⟫_ℂ := by
  let φ : C(K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun f := ⟪ξ, π f ξ⟫_ℂ
      map_add' f g := by simp
      map_smul' c f := by simp }
  exact (φ.apply_eq_integral_of_forall_realToRCLike
    (fun g => (ofReal_integral_representationDiagMeasure π ξ g).symm) f).symm

/-- A regular measure `μ` equals the diagonal measure `μ_ξ` iff
`∫ f dμ = ⟪ξ, π f ξ⟫` for every continuous complex-valued `f`. -/
theorem eq_representationDiagMeasure_iff (ξ : H) (μ : Measure K)
    [μ.Regular] :
    μ = representationDiagMeasure π ξ ↔
      ∀ f : C(K, ℂ), ∫ x, f x ∂μ = ⟪ξ, π f ξ⟫_ℂ := by
  refine ⟨fun h => h ▸ integral_representationDiagMeasure π ξ, fun h => ?_⟩
  refine Measure.ext_of_integral_eq_on_compactlySupported fun g => ?_
  have hg := h (g.toContinuousMap.realToRCLike ℂ)
  rw [← integral_representationDiagMeasure] at hg
  simpa [integral_complex_ofReal] using hg

/-- The mass of the representation diagonal measure is the squared vector norm. -/
@[simp]
theorem representationDiagMeasure_real_univ (ξ : H) :
    (representationDiagMeasure π ξ).real Set.univ = ‖ξ‖ ^ 2 := by
  simpa [← Complex.ofReal_pow] using
    congrArg Complex.re (integral_representationDiagMeasure π ξ 1)

/-- The total mass, in extended nonnegative reals. -/
@[simp]
theorem representationDiagMeasure_univ (ξ : H) :
    representationDiagMeasure π ξ Set.univ = ‖ξ‖ₑ ^ 2 := by
  rw [← ofReal_measureReal, representationDiagMeasure_real_univ,
    ENNReal.ofReal_pow (norm_nonneg ξ), ofReal_norm]

/-- For every continuous symbol `f`, the squared `L²(μ_ξ)` norm equals
`‖π(f) ξ‖²`: explicitly, `∫ ‖f‖² dμ_ξ = ‖π(f) ξ‖²`. -/
theorem integral_norm_sq_representationDiagMeasure (ξ : H) (f : C(K, ℂ)) :
    ∫ x, ‖f x‖ ^ 2 ∂(representationDiagMeasure π ξ) = ‖π f ξ‖ ^ 2 := by
  rw [norm_sq_apply_eq_re_inner_star_mul π ξ f,
    ← integral_representationDiagMeasure]
  simp [Complex.conj_mul', ← Complex.ofReal_pow, integral_complex_ofReal]

end StarAlgHom
