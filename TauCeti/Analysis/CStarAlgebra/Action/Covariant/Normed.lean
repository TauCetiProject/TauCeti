/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Ring.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Contractive integrated representations

The vector-valued integrated form of a covariant representation is a contraction from the
compact-support twisted convolution algebra with its L¹ seminorm to the bounded operators on
the representation space. We bundle it both as a continuous linear map and, for a left-invariant
measure, as a nonunital algebra homomorphism. Extending by continuity, the integrated form is a
contractive nonunital algebra homomorphism on the twisted L¹ algebra, the completion
`UniformSpace.Completion (ConvolutionAlgebra α μ)`.

Only finiteness on compact sets is needed for continuity. Left invariance is needed for the
algebra homomorphism. Neither unitality of the coefficient algebra, nondegeneracy of the
representation, nor separability or σ-finiteness is assumed.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
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
        ConvolutionAlgebra.linearEquiv_apply, one_mul,
        ConvolutionAlgebra.norm_eq_integral_norm] using
        P.norm_integratedOperator_le μ f.ofConv

@[simp]
theorem integratedOperatorCLM_apply (f : ConvolutionAlgebra α μ) :
    P.integratedOperatorCLM μ f = P.integratedOperator μ f.ofConv := by
  simp [integratedOperatorCLM]

/-- The operator norm of the integrated map is at most one, including zero representation spaces
and measures without full support. -/
theorem norm_integratedOperatorCLM_le : ‖P.integratedOperatorCLM μ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  simpa only [integratedOperatorCLM_apply, one_mul,
    ConvolutionAlgebra.norm_eq_integral_norm] using
    P.norm_integratedOperator_le μ f.ofConv

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The integrated form as a nonunital algebra homomorphism on compact-support twisted
convolution coefficients. -/
def integratedNonUnitalAlgHom : ConvolutionAlgebra α μ →ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun := P.integratedOperatorCLM μ
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' f g := by simp

@[simp]
theorem integratedNonUnitalAlgHom_apply (f : ConvolutionAlgebra α μ) :
    P.integratedNonUnitalAlgHom μ f = P.integratedOperator μ f.ofConv := by
  simp [integratedNonUnitalAlgHom]

/-- The algebra homomorphism is continuous in the L¹ topology. -/
@[fun_prop]
theorem continuous_integratedNonUnitalAlgHom : Continuous (P.integratedNonUnitalAlgHom μ) :=
  (P.integratedOperatorCLM μ).continuous

/-- The integrated form on the twisted L¹ algebra: the extension by continuity of
`integratedNonUnitalAlgHom` to the completion of the convolution algebra in its L¹ seminorm. -/
def integratedOperatorL1 :
    Completion (ConvolutionAlgebra α μ) →ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun := (P.integratedOperatorCLM μ).fromCompletion
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f g => simp only [← Completion.coe_mul', ContinuousLinearMap.fromCompletion_apply_coe,
        integratedOperatorCLM_apply, ConvolutionAlgebra.ofConv_mul, integratedOperator_convolution]

/-- On compactly supported coefficients the L¹ integrated form is the integrated form. -/
@[simp]
theorem integratedOperatorL1_coe (f : ConvolutionAlgebra α μ) :
    P.integratedOperatorL1 μ f = P.integratedOperator μ f.ofConv := by
  simp [integratedOperatorL1]

/-- The L¹ integrated form is continuous. -/
@[fun_prop]
theorem continuous_integratedOperatorL1 : Continuous (P.integratedOperatorL1 μ) :=
  (P.integratedOperatorCLM μ).fromCompletion.continuous

/-- The L¹ integrated form is a contraction: `‖(π ⋊ U)(x)‖ ≤ ‖x‖₁` on the twisted L¹ algebra. -/
theorem norm_integratedOperatorL1_le (x : Completion (ConvolutionAlgebra α μ)) :
    ‖P.integratedOperatorL1 μ x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih f =>
    simpa only [integratedOperatorL1_coe, Completion.norm_coe, one_mul,
      integratedOperatorCLM_apply] using (P.integratedOperatorCLM μ).le_of_opNorm_le
        (P.norm_integratedOperatorCLM_le μ) f

end Multiplication

end TauCeti.CStarAction.CovariantRepresentation
