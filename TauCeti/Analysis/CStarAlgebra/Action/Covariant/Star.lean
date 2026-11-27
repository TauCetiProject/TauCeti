/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Normed

/-!
# Integrated covariant ⋆-representations

The vector-integrated form of a covariant representation preserves the twisted involution:
`(π ⋊ U)(f*) = ((π ⋊ U)(f))*`. Together with multiplicativity, this gives a nonunital complex
⋆-algebra homomorphism from the compact-support convolution algebra to bounded operators, which
extends by continuity to a contractive nonunital ⋆-algebra homomorphism
`CovariantRepresentation.integratedStarAlgHomL1` on the twisted L¹ completion
`UniformSpace.Completion (ConvolutionAlgebra α μ)`. This is the representation used to define the
universal crossed-product norm.

For any left-invariant measure finite on compact sets, integrals of compactly supported continuous
functions are scalar multiples of Haar integrals, where Haar inversion cancels the modular weight
`c(g) = Δ(g)⁻¹`. All integrands tested in matrix coefficients have compact support, so neither full
support (`IsOpenPosMeasure`), global σ-finiteness, separability, nor operator-norm continuity of
the unitary representation is required. Coefficient representations may be degenerate and
coefficient algebras may be nonunital or zero.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2. The
matrix-coefficient argument follows the existing scalar construction
`ContRepresentation.adjoint_integratedOperatorL1`, with covariance and the Haar modular factor
in place of invariance under additive negation.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported InnerProductSpace

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- The vector-integrated covariant form sends the twisted involution to the operator adjoint.
The modular factor in the involution cancels the change of Haar measure under inversion. -/
@[simp]
theorem integratedOperator_twistedInvolution (f : C_c(G, A)) :
    P.integratedOperator μ (α.twistedInvolution f) = star (P.integratedOperator μ f) := by
  rw [P.integratedOperator_eq_coefficient μ]
  refine P.coefficient.integratedOperator_eq_star P.continuous_orbit P.isUnitary.exists_norm_le μ
    (.of_forall fun g => ?_)
  rw [twistedInvolution_apply, map_smul, smul_mul_assoc, ← P.group_mul_coefficient,
    star_mul, map_star, P.isUnitary.star_eq_inv, inv_inv]

/-- The integrated form as a nonunital complex ⋆-algebra homomorphism on the compact-support
convolution algebra. Its values are defined by Hilbert-space vector integrals. -/
def integratedStarAlgHom : ConvolutionAlgebra α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  (P.integratedOperatorCLM μ).toNonUnitalStarAlgHomOfMulStar (fun f g => by simp)
    (fun f => by simp)

/-- Evaluation of the integrated ⋆-homomorphism uses the compactly supported coefficient
function underlying the convolution-algebra element. -/
@[simp]
theorem integratedStarAlgHom_apply (f : ConvolutionAlgebra α μ) :
    P.integratedStarAlgHom μ f = P.integratedOperator μ f.ofConv := by
  rw [integratedStarAlgHom, ContinuousLinearMap.toNonUnitalStarAlgHomOfMulStar_apply,
    integratedOperatorCLM_apply]

/-- The integrated ⋆-homomorphism is bounded by the L¹ norm of the convolution algebra. -/
theorem norm_integratedStarAlgHom_le_norm (f : ConvolutionAlgebra α μ) :
    ‖P.integratedStarAlgHom μ f‖ ≤ ‖f‖ := by
  rw [integratedStarAlgHom, ContinuousLinearMap.toNonUnitalStarAlgHomOfMulStar_apply]
  exact ((P.integratedOperatorCLM μ).le_of_opNorm_le (P.norm_integratedOperatorCLM_le μ) f).trans_eq
    (one_mul _)

/-- The integrated ⋆-homomorphism is continuous in the L¹ topology. -/
@[fun_prop]
theorem continuous_integratedStarAlgHom : Continuous (P.integratedStarAlgHom μ) :=
  (P.integratedOperatorCLM μ).continuous_toNonUnitalStarAlgHomOfMulStar _ _

/-- The integrated form on `Completion (ConvolutionAlgebra α μ)` bundled as a nonunital complex
`⋆`-algebra homomorphism. -/
def integratedStarAlgHomL1 :
    Completion (ConvolutionAlgebra α μ) →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  ((P.integratedOperatorCLM μ).toNonUnitalStarAlgHomOfMulStar (fun f g => by simp)
    (fun f => by simp)).fromCompletion
    ((P.integratedOperatorCLM μ).continuous_toNonUnitalStarAlgHomOfMulStar _ _)

@[simp]
theorem toNonUnitalAlgHom_integratedStarAlgHomL1 :
    (P.integratedStarAlgHomL1 μ).toNonUnitalAlgHom = P.integratedOperatorL1 μ := by
  simp only [integratedStarAlgHomL1, NonUnitalStarAlgHom.toNonUnitalAlgHom_fromCompletion,
    ContinuousLinearMap.toNonUnitalAlgHom_toNonUnitalStarAlgHomOfMulStar]
  exact NonUnitalAlgHom.fromCompletion_unique _ _ _ (P.continuous_integratedOperatorL1 μ)
    fun f => by simp

@[simp]
theorem integratedStarAlgHomL1_apply (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedStarAlgHomL1 μ x = P.integratedOperatorL1 μ x :=
  DFunLike.congr_fun (P.toNonUnitalAlgHom_integratedStarAlgHomL1 μ) x

/-- The L¹ integrated form preserves the `⋆`-involution on the L¹ completion. -/
@[simp]
theorem integratedOperatorL1_star (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedOperatorL1 μ (star x) = star (P.integratedOperatorL1 μ x) := by
  simpa only [integratedStarAlgHomL1_apply] using map_star (P.integratedStarAlgHomL1 μ) x

/-- The L¹ integrated `⋆`-homomorphism is continuous. -/
@[fun_prop]
theorem continuous_integratedStarAlgHomL1 : Continuous (P.integratedStarAlgHomL1 μ) :=
  NonUnitalStarAlgHom.continuous_fromCompletion _ _

/-- The L¹ integrated `⋆`-homomorphism is a contraction on the twisted L¹ completion. -/
theorem norm_integratedStarAlgHomL1_le (x : Completion (ConvolutionAlgebra α μ)) :
    ‖P.integratedStarAlgHomL1 μ x‖ ≤ ‖x‖ := by
  simpa only [integratedStarAlgHomL1_apply] using P.norm_integratedOperatorL1_le μ x

end TauCeti.CStarAction.CovariantRepresentation
