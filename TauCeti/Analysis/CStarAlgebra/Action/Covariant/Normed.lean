/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.Analysis.Normed.Ring.Completion
public import TauCeti.Topology.Algebra.LinearMapCompletion

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
  CompactlySupportedL1.liftCLM (P.integratedOperator μ) 1 fun f => by
    simpa only [one_mul] using P.norm_integratedOperator_le μ f

@[simp]
theorem integratedOperatorCLM_apply (f : ConvolutionAlgebra α μ) :
    P.integratedOperatorCLM μ f = P.integratedOperator μ f.ofConv :=
  CompactlySupportedL1.liftCLM_apply (P.integratedOperator μ) _ f

/-- The operator norm of the integrated map is at most one, including zero representation spaces
and measures without full support. -/
theorem norm_integratedOperatorCLM_le : ‖P.integratedOperatorCLM μ‖ ≤ 1 :=
  CompactlySupportedL1.norm_liftCLM_le (P.integratedOperator μ) zero_le_one _

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The integrated form as a nonunital algebra homomorphism on compact-support twisted
convolution coefficients. -/
def integratedNonUnitalAlgHom : ConvolutionAlgebra α μ →ₙₐ[ℂ] (H →L[ℂ] H) :=
  (P.integratedOperatorCLM μ).toNonUnitalAlgHomOfMul fun f g => by simp

@[simp]
theorem integratedNonUnitalAlgHom_apply (f : ConvolutionAlgebra α μ) :
    P.integratedNonUnitalAlgHom μ f = P.integratedOperator μ f.ofConv := by
  rw [integratedNonUnitalAlgHom, ContinuousLinearMap.toNonUnitalAlgHomOfMul_apply,
    integratedOperatorCLM_apply]

/-- The algebra homomorphism is continuous in the L¹ topology. -/
@[fun_prop]
theorem continuous_integratedNonUnitalAlgHom : Continuous (P.integratedNonUnitalAlgHom μ) :=
  (P.integratedOperatorCLM μ).continuous_toNonUnitalAlgHomOfMul _

/-- The integrated form on the twisted L¹ algebra: the extension by continuity of
`integratedNonUnitalAlgHom` to the completion of the convolution algebra in its L¹ seminorm. -/
def integratedOperatorL1 :
    Completion (ConvolutionAlgebra α μ) →ₙₐ[ℂ] (H →L[ℂ] H) :=
  ((P.integratedOperatorCLM μ).toNonUnitalAlgHomOfMul fun f g => by simp).fromCompletion
    ((P.integratedOperatorCLM μ).continuous_toNonUnitalAlgHomOfMul _)

/-- On compactly supported coefficients the L¹ integrated form is the integrated form. -/
@[simp]
theorem integratedOperatorL1_coe (f : ConvolutionAlgebra α μ) :
    P.integratedOperatorL1 μ f = P.integratedOperator μ f.ofConv := by
  rw [integratedOperatorL1, NonUnitalAlgHom.fromCompletion_apply_coe,
    ContinuousLinearMap.toNonUnitalAlgHomOfMul_apply, integratedOperatorCLM_apply]

/-- The L¹ integrated form is continuous. -/
@[fun_prop]
theorem continuous_integratedOperatorL1 : Continuous (P.integratedOperatorL1 μ) :=
  NonUnitalAlgHom.continuous_fromCompletion _ _

/-- The L¹ integrated form is a contraction: `‖(π ⋊ U)(x)‖ ≤ ‖x‖₁` on the twisted L¹ algebra. -/
theorem norm_integratedOperatorL1_le (x : Completion (ConvolutionAlgebra α μ)) :
    ‖P.integratedOperatorL1 μ x‖ ≤ ‖x‖ := by
  have hle : ‖(P.integratedOperatorCLM μ).fromCompletion‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_fromCompletion]
    exact P.norm_integratedOperatorCLM_le μ
  simpa only [integratedOperatorL1, NonUnitalAlgHom.coe_fromCompletion,
    ContinuousLinearMap.coe_toNonUnitalAlgHomOfMul, ContinuousLinearMap.coe_fromCompletion] using
    ((P.integratedOperatorCLM μ).fromCompletion.le_of_opNorm_le hle x).trans_eq (one_mul _)

end Multiplication

end TauCeti.CStarAction.CovariantRepresentation
