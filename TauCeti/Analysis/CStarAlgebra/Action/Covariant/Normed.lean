/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated

/-!
# Contractive integrated representations

The vector-valued integrated form of a covariant representation is a contraction from the
compact-support twisted convolution algebra with its L¹ seminorm to the bounded operators on
the representation space. We bundle it both as a continuous linear map and, for a left-invariant
measure, as a nonunital algebra homomorphism. The continuous linear map is the input for extending
the integrated form to the completion using `ContinuousLinearMap.fromCompletion`.

Only finiteness on compact sets is needed for continuity. Left invariance is needed for the
algebra homomorphism. Neither unitality of the coefficient algebra, nondegeneracy of the
representation, nor separability or σ-finiteness is assumed.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- The integrated form as a continuous linear map on the convolution algebra with its L¹
seminorm. -/
def integratedOperatorCLM : ConvolutionAlgebra α μ →L[ℂ] (H →L[ℂ] H) :=
  ((P.integratedOperator μ).comp (ConvolutionAlgebra.linearEquiv α μ).toLinearMap).mkContinuous
    1 fun f => by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        ConvolutionAlgebra.linearEquiv_apply, one_mul, ConvolutionAlgebra.norm_def] using
        P.norm_integratedOperator_le μ f.ofConv

@[simp]
theorem integratedOperatorCLM_apply (f : ConvolutionAlgebra α μ) :
    P.integratedOperatorCLM μ f = P.integratedOperator μ f.ofConv := by
  simp [integratedOperatorCLM]

/-- The operator norm of the integrated map is at most one, including zero representation spaces
and measures without full support. -/
theorem norm_integratedOperatorCLM_le : ‖P.integratedOperatorCLM μ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  simpa only [integratedOperatorCLM_apply, one_mul, ConvolutionAlgebra.norm_def] using
    P.norm_integratedOperator_le μ f.ofConv

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The integrated form as a nonunital algebra homomorphism on compact-support twisted
convolution coefficients. -/
def integratedAlgHom : ConvolutionAlgebra α μ →ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun := P.integratedOperatorCLM μ
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' f g := by simp

@[simp]
theorem integratedAlgHom_apply (f : ConvolutionAlgebra α μ) :
    P.integratedAlgHom μ f = P.integratedOperator μ f.ofConv := by
  simp [integratedAlgHom]

/-- The algebra homomorphism is continuous in the L¹ topology. -/
@[fun_prop]
theorem continuous_integratedAlgHom : Continuous (P.integratedAlgHom μ) :=
  (P.integratedOperatorCLM μ).continuous

end Multiplication

end TauCeti.CStarAction.CovariantRepresentation
