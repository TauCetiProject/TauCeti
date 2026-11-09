/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated

/-!
# Integrated covariant ⋆-representations

The vector-integrated form of a covariant representation preserves the twisted involution:
`(π ⋊ U)(f*) = ((π ⋊ U)(f))*`. Together with multiplicativity, this gives a nonunital complex
⋆-algebra homomorphism from the compact-support convolution algebra to bounded operators.
This is the representation used to define the universal crossed-product norm. It is bounded by
the L¹ norm of the convolution algebra.

The proof uses Haar inversion with the modular weight `c(g) = Δ(g)⁻¹`. All integrands tested
in matrix coefficients have compact support, so no global σ-finiteness, separability, or
operator-norm continuity of the unitary representation is required. Coefficient representations
may be degenerate and coefficient algebras may be nonunital or zero.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2. The
matrix-coefficient argument follows the existing scalar construction
`ContRepresentation.adjoint_integratedOperatorL1`, with covariance and the Haar modular factor
in place of invariance under additive negation.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported InnerProductSpace

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (μ : Measure G) [μ.IsHaarMeasure]

/-- The vector-integrated covariant form sends the twisted involution to the operator adjoint.
The modular factor in the involution cancels the change of Haar measure under inversion. -/
@[simp]
theorem integratedOperator_twistedInvolution (f : C_c(G, A)) :
    P.integratedOperator μ (α.twistedInvolution f) = star (P.integratedOperator μ f) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun v w => ?_
  rw [← inner_conj_symm _ w, P.inner_integratedOperator_apply,
    P.inner_integratedOperator_apply, ← integral_conj]
  calc
    (∫ g, starRingEnd ℂ ⟪w, P.coefficient (α.twistedInvolution f g) (P.group g v)⟫_ℂ ∂μ) =
        ∫ g, (Measure.modularCharacter g : ℝ) •
          ⟪v, P.coefficient (f g⁻¹) (P.group g⁻¹ w)⟫_ℂ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [inner_conj_symm]
      calc
        ⟪P.coefficient (α.twistedInvolution f g) (P.group g v), w⟫_ℂ =
            (Measure.modularCharacter g : ℝ) •
              ⟪P.coefficient (α g (star (f g⁻¹))) (P.group g v), w⟫_ℂ := by
          simp only [twistedInvolution_apply, map_smul, smul_apply]
          exact inner_smul_real_left _ _ _
        _ = (Measure.modularCharacter g : ℝ) •
              ⟪P.group g (P.coefficient (star (f g⁻¹)) v), w⟫_ℂ := by
          rw [P.covariance]
        _ = (Measure.modularCharacter g : ℝ) •
              ⟪P.coefficient (star (f g⁻¹)) v, P.group g⁻¹ w⟫_ℂ := by
          rw [P.isUnitary.inner_map_left]
        _ = (Measure.modularCharacter g : ℝ) •
              ⟪v, P.coefficient (f g⁻¹) (P.group g⁻¹ w)⟫_ℂ := by
          simp only [map_star, ContinuousLinearMap.star_eq_adjoint,
            ContinuousLinearMap.adjoint_inner_left]
    _ = ∫ g, ⟪v, P.coefficient (f g) (P.group g w)⟫_ℂ ∂μ :=
      integral_modularCharacter_smul_inv_eq_self (μ := μ)
        (f := fun g => ⟪v, P.coefficient (f g) (P.group g w)⟫_ℂ)
        (continuous_const.inner (P.continuous_integrand f w))
        ((P.hasCompactSupport_integrand f w).comp_left (inner_zero_right v))

/-- The integrated form as a nonunital complex ⋆-algebra homomorphism on the compact-support
convolution algebra. Its values are defined by Hilbert-space vector integrals. -/
def integratedStarAlgHom : ConvolutionAlgebra α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun f := P.integratedOperator μ f.ofConv
  map_zero' := by simp
  map_add' f g := by simp
  map_mul' f g := by simp
  map_smul' c f := by simp
  map_star' f := by simp

/-- Evaluation of the integrated ⋆-homomorphism uses the compactly supported coefficient
function underlying the convolution-algebra element. -/
@[simp]
theorem integratedStarAlgHom_apply (f : ConvolutionAlgebra α μ) :
    P.integratedStarAlgHom μ f = P.integratedOperator μ f.ofConv :=
  (rfl)

/-- The integrated ⋆-homomorphism is bounded by the L¹ norm of the convolution algebra. -/
theorem norm_integratedStarAlgHom_le_norm (f : ConvolutionAlgebra α μ) :
    ‖P.integratedStarAlgHom μ f‖ ≤ ‖f‖ := by
  simpa [ConvolutionAlgebra.norm_eq_integral_norm] using P.norm_integratedOperator_le μ f.ofConv

end TauCeti.CStarAction.CovariantRepresentation
