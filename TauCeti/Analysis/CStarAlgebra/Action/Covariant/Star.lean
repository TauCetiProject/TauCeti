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
  have hdef (h : C_c(G, A)) : P.integratedOperator μ h =
      P.coefficient.integratedOperator (fun g => P.group g) P.continuous_orbit
        P.isUnitary.exists_norm_le μ h := by
    ext v
    simp [integratedOperator_apply, NonUnitalStarAlgHom.integratedOperator_apply]
  rw [hdef, hdef]
  refine P.coefficient.integratedOperator_eq_star P.continuous_orbit P.isUnitary.exists_norm_le μ
    (.of_forall fun g => ?_)
  rw [twistedInvolution_apply, map_smul, smul_mul_assoc, ← P.group_mul_coefficient,
    star_mul, map_star, P.isUnitary.star_eq_inv, inv_inv]

/-- The integrated form as a nonunital complex ⋆-algebra homomorphism on the compact-support
convolution algebra. Its values are defined by Hilbert-space vector integrals. -/
def integratedStarAlgHom : ConvolutionAlgebra α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  __ := P.integratedNonUnitalAlgHom μ
  map_star' _ := by simp

/-- Evaluation of the integrated ⋆-homomorphism uses the compactly supported coefficient
function underlying the convolution-algebra element. -/
@[simp]
theorem integratedStarAlgHom_apply (f : ConvolutionAlgebra α μ) :
    P.integratedStarAlgHom μ f = P.integratedOperator μ f.ofConv :=
  P.integratedNonUnitalAlgHom_apply μ f

/-- The integrated ⋆-homomorphism is bounded by the L¹ norm of the convolution algebra. -/
theorem norm_integratedStarAlgHom_le_norm (f : ConvolutionAlgebra α μ) :
    ‖P.integratedStarAlgHom μ f‖ ≤ ‖f‖ := by
  simpa [ConvolutionAlgebra.norm_eq_integral_norm] using P.norm_integratedOperator_le μ f.ofConv

/-- The integrated ⋆-homomorphism is continuous in the L¹ topology. -/
@[fun_prop]
theorem continuous_integratedStarAlgHom : Continuous (P.integratedStarAlgHom μ) :=
  (P.integratedOperatorCLM μ).continuous.congr fun f => by simp

/-- The integrated form on `Completion (ConvolutionAlgebra α μ)` bundled as a nonunital complex
`⋆`-algebra homomorphism. -/
def integratedStarAlgHomL1 :
    Completion (ConvolutionAlgebra α μ) →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  (P.integratedStarAlgHom μ).fromCompletion (P.continuous_integratedStarAlgHom μ)

@[simp]
theorem toNonUnitalAlgHom_integratedStarAlgHomL1 :
    (P.integratedStarAlgHomL1 μ).toNonUnitalAlgHom = P.integratedOperatorL1 μ := by
  rw [integratedStarAlgHomL1, NonUnitalStarAlgHom.toNonUnitalAlgHom_fromCompletion]
  exact (P.integratedStarAlgHom μ).toNonUnitalAlgHom.fromCompletion_unique
    (P.continuous_integratedStarAlgHom μ) (P.integratedOperatorL1 μ)
    (P.continuous_integratedOperatorL1 μ) fun f => by simp

@[simp]
theorem integratedStarAlgHomL1_apply (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedStarAlgHomL1 μ x = P.integratedOperatorL1 μ x :=
  DFunLike.congr_fun (P.toNonUnitalAlgHom_integratedStarAlgHomL1 μ) x

/-- The L¹ integrated form preserves the `⋆`-involution on the twisted L¹ completion. -/
@[simp]
theorem integratedOperatorL1_star (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedOperatorL1 μ (star x) = star (P.integratedOperatorL1 μ x) := by
  simpa only [integratedStarAlgHomL1_apply] using map_star (P.integratedStarAlgHomL1 μ) x

/-- The L¹ integrated `⋆`-homomorphism is continuous. -/
@[fun_prop]
theorem continuous_integratedStarAlgHomL1 : Continuous (P.integratedStarAlgHomL1 μ) :=
  (P.integratedStarAlgHom μ).continuous_fromCompletion _

/-- The L¹ integrated `⋆`-homomorphism is a contraction on the twisted L¹ completion. -/
theorem norm_integratedStarAlgHomL1_le (x : Completion (ConvolutionAlgebra α μ)) :
    ‖P.integratedStarAlgHomL1 μ x‖ ≤ ‖x‖ := by
  simpa only [integratedStarAlgHomL1_apply] using P.norm_integratedOperatorL1_le μ x

end TauCeti.CStarAction.CovariantRepresentation
