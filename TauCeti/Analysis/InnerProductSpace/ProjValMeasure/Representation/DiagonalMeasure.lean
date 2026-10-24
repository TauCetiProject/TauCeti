/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# Diagonal Riesz measures for continuous-function representations

Let `π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)` be a unital star representation on a complex
Hilbert space, with `K` compact Hausdorff. For each `ξ : H`, the positive functional
`f ↦ ⟪ξ, π(f) ξ⟫` determines a finite regular Borel measure on `K`.

This supplies the diagonal-measure input to the representation PVM construction.
It does not construct `ProjValMeasure.ofRepresentation`: that additionally requires
polarized matrix elements and multiplicative, strongly additive indicator operators.

Unlike the existing `ContinuousLinearMap.diagMeasure`, this construction has an arbitrary
compact Hausdorff base `K` and an arbitrary unital representation, not a normal operator
and its functional calculus. The argument specializes Mathlib's Riesz-Markov-Kakutani
measure, with the positive-functional calculation adapted from TauCeti's normal-operator
`BorelCalculus/DiagonalMeasure.lean`. No parallel Borel calculus is introduced.
-/

public section

noncomputable section

open MeasureTheory ContinuousMap
open scoped InnerProductSpace ComplexOrder CompactlySupported

namespace TauCeti
namespace ProjValMeasure

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- The positive real functional associated with a vector in a unital representation. -/
private def representationDiagFunctional (ξ : H) : C_c(K, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun g := RCLike.re ⟪ξ, π (g.toContinuousMap.realToRCLike ℂ) ξ⟫_ℂ
      map_add' g h := by
        simp only [← realToRCLikeStarAlgHom_apply]
        rw [show (g + h).toContinuousMap = g.toContinuousMap + h.toContinuousMap by
          ext; simp, map_add, map_add, _root_.add_apply, inner_add_right, map_add]
      map_smul' c g := by
        simp only [← realToRCLikeStarAlgHom_apply]
        rw [show (c • g).toContinuousMap = c • g.toContinuousMap by ext; simp, map_smul,
          ← algebraMap_smul ℂ c (M := C(K, ℂ)), map_smul, _root_.smul_apply,
          inner_smul_right]
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

/-- The finite regular diagonal measure on `K` associated with `ξ` and `π`. -/
def representationDiagMeasure (ξ : H) : Measure K :=
  RealRMK.rieszMeasure (representationDiagFunctional π ξ)

instance representationDiagMeasure_finite (ξ : H) :
    IsFiniteMeasure (representationDiagMeasure π ξ) := by
  unfold representationDiagMeasure
  infer_instance

instance representationDiagMeasure_regular (ξ : H) :
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

/-- The representation is integration against the canonical diagonal measure on `K`. -/
theorem integral_representationDiagMeasure (ξ : H) (f : C(K, ℂ)) :
    ∫ x, f x ∂(representationDiagMeasure π ξ) = ⟪ξ, π f ξ⟫_ℂ := by
  let φ : C(K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun f := ⟪ξ, π f ξ⟫_ℂ
      map_add' f g := by simp
      map_smul' c f := by simp }
  exact (φ.apply_eq_integral_of_forall_realToRCLike
    (fun g => (ofReal_integral_representationDiagMeasure π ξ g).symm) f).symm

/-- A regular measure is the diagonal measure exactly when its continuous matrix elements agree. -/
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

/-- The representation preserves the continuous-symbol `L²` diagonal identity. -/
theorem integral_norm_sq_representationDiagMeasure (ξ : H) (f : C(K, ℂ)) :
    ∫ x, ‖f x‖ ^ 2 ∂(representationDiagMeasure π ξ) = ‖π f ξ‖ ^ 2 := by
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def,
    ← map_star, ← map_mul, ← integral_representationDiagMeasure]
  simp [Complex.conj_mul', ← Complex.ofReal_pow, integral_complex_ofReal]

end ProjValMeasure
end TauCeti
