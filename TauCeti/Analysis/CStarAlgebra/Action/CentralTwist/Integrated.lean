/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Algebra
public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Covariant
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Algebra.Completion
public import TauCeti.Topology.Algebra.LinearMapCompletion

/-!
# Integrated L¹ representations of twisted covariant pairs

For a point-norm continuous action `α` of a topological group `G` on a C⋆-algebra `A` and a
normalized continuous central multiplier cocycle `ω : CentralCocycle α`, the vector-valued
integrated form `P.integratedOperator μ` of a twisted covariant pair
`P : CentralCovariantPair H α ω` extends to contractive homomorphisms on
`TwistedConvolutionAlgebra ω μ` and its `L¹` completion
`UniformSpace.Completion (TwistedConvolutionAlgebra ω μ)`:

* `CentralCovariantPair.integratedOperatorCLM`, `CentralCovariantPair.integratedNonUnitalAlgHom`,
  and `CentralCovariantPair.integratedOperatorL1` (for left-invariant `μ` finite on compacts);
* `CentralCovariantPair.integratedStarAlgHom` and `CentralCovariantPair.integratedStarAlgHomL1`
  (additionally preserving `ω.involution` for left-invariant Borel `μ` finite on compacts);
* `CentralCovariantPair.equivCovariantRepresentation`: canonical equivalence between
  `CentralCovariantPair H α 1` and nondegenerate `CovariantRepresentation α H`.

## References

* J. Packer and I. Raeburn, *Twisted crossed products of C*-algebras*, Math. Proc. Cambridge
  Philos. Soc. 106 (1989), 293–311, Section 2.
* D. P. Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported CStarAlgebra InnerProductSpace MultiplierAlgebra

namespace TauCeti.CStarAction.CentralCovariantPair

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {ω : CentralCocycle α} (P : CentralCovariantPair H α ω)

section Normed

variable [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ]

/-- The integrated form bundled as a contractive continuous linear map on
`TwistedConvolutionAlgebra ω μ`. -/
def integratedOperatorCLM : TwistedConvolutionAlgebra ω μ →L[ℂ] (H →L[ℂ] H) :=
  ((P.integratedOperator μ).comp
      (TwistedConvolutionAlgebra.linearEquiv ω μ).toLinearMap).mkContinuous
    1 fun f => by
      simpa [TwistedConvolutionAlgebra.norm_eq_integral_norm] using
        P.norm_integratedOperator_le μ f.ofConv

@[simp] theorem integratedOperatorCLM_apply (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedOperatorCLM μ f = P.integratedOperator μ f.ofConv := by
  simp [integratedOperatorCLM]

theorem norm_integratedOperatorCLM_le : ‖P.integratedOperatorCLM μ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    simpa [TwistedConvolutionAlgebra.norm_eq_integral_norm] using
      P.norm_integratedOperator_le μ f.ofConv

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The integrated form as a nonunital algebra homomorphism on `TwistedConvolutionAlgebra ω μ`. -/
def integratedNonUnitalAlgHom : TwistedConvolutionAlgebra ω μ →ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun := P.integratedOperatorCLM μ
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' _ _ := by simp

@[simp] theorem integratedNonUnitalAlgHom_apply (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedNonUnitalAlgHom μ f = P.integratedOperator μ f.ofConv := by
  simp [integratedNonUnitalAlgHom]

@[fun_prop] theorem continuous_integratedNonUnitalAlgHom :
    Continuous (P.integratedNonUnitalAlgHom μ) :=
  (P.integratedOperatorCLM μ).continuous

/-- Extension by continuity of the integrated form to
`Completion (TwistedConvolutionAlgebra ω μ)`. -/
def integratedOperatorL1 :
    Completion (TwistedConvolutionAlgebra ω μ) →ₙₐ[ℂ] (H →L[ℂ] H) :=
  (P.integratedNonUnitalAlgHom μ).fromCompletion (P.continuous_integratedNonUnitalAlgHom μ)

@[simp] theorem integratedOperatorL1_coe (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedOperatorL1 μ f = P.integratedOperator μ f.ofConv := by
  simp [integratedOperatorL1]

@[fun_prop] theorem continuous_integratedOperatorL1 : Continuous (P.integratedOperatorL1 μ) :=
  (P.integratedNonUnitalAlgHom μ).continuous_fromCompletion _

theorem norm_integratedOperatorL1_le (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    ‖P.integratedOperatorL1 μ x‖ ≤ ‖x‖ :=
  ((P.integratedNonUnitalAlgHom μ).norm_fromCompletion_le
    (P.continuous_integratedNonUnitalAlgHom μ) (fun f => by
      simpa only [integratedNonUnitalAlgHom_apply, one_mul,
        TwistedConvolutionAlgebra.norm_eq_integral_norm] using
        P.norm_integratedOperator_le μ f.ofConv) x).trans_eq (one_mul _)

end Multiplication

end Normed

section Star

variable [MeasurableSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- The integrated form as a nonunital complex ⋆-algebra homomorphism on
`TwistedConvolutionAlgebra ω μ`. -/
def integratedStarAlgHom : TwistedConvolutionAlgebra ω μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  __ := P.integratedNonUnitalAlgHom μ
  map_star' _ := by simp

@[simp] theorem integratedStarAlgHom_apply (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedStarAlgHom μ f = P.integratedOperator μ f.ofConv :=
  P.integratedNonUnitalAlgHom_apply μ f

theorem norm_integratedStarAlgHom_le_norm (f : TwistedConvolutionAlgebra ω μ) :
    ‖P.integratedStarAlgHom μ f‖ ≤ ‖f‖ := by
  simpa [TwistedConvolutionAlgebra.norm_eq_integral_norm] using
    P.norm_integratedOperator_le μ f.ofConv

@[fun_prop] theorem continuous_integratedStarAlgHom : Continuous (P.integratedStarAlgHom μ) :=
  (P.integratedOperatorCLM μ).continuous.congr fun f => by simp

/-- Extension by continuity of the integrated ⋆-representation to
`Completion (TwistedConvolutionAlgebra ω μ)`. -/
def integratedStarAlgHomL1 :
    Completion (TwistedConvolutionAlgebra ω μ) →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  (P.integratedStarAlgHom μ).fromCompletion (P.continuous_integratedStarAlgHom μ)

@[simp] theorem toNonUnitalAlgHom_integratedStarAlgHomL1 :
    (P.integratedStarAlgHomL1 μ).toNonUnitalAlgHom = P.integratedOperatorL1 μ := by
  rw [integratedStarAlgHomL1, NonUnitalStarAlgHom.toNonUnitalAlgHom_fromCompletion]
  exact (NonUnitalAlgHom.fromCompletion_unique _ _ (P.integratedOperatorL1 μ)
    (P.continuous_integratedOperatorL1 μ) fun f => by simp).symm

@[simp] theorem integratedStarAlgHomL1_apply (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    P.integratedStarAlgHomL1 μ x = P.integratedOperatorL1 μ x :=
  DFunLike.congr_fun (P.toNonUnitalAlgHom_integratedStarAlgHomL1 μ) x

theorem integratedStarAlgHomL1_coe (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedStarAlgHomL1 μ f = P.integratedOperator μ f.ofConv := by
  rw [integratedStarAlgHomL1_apply, integratedOperatorL1_coe]

/-- The L¹ integrated form preserves the `⋆`-involution on the twisted L¹ completion. -/
@[simp] theorem integratedOperatorL1_star (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    P.integratedOperatorL1 μ (star x) = star (P.integratedOperatorL1 μ x) := by
  simpa only [integratedStarAlgHomL1_apply] using map_star (P.integratedStarAlgHomL1 μ) x

@[fun_prop] theorem continuous_integratedStarAlgHomL1 : Continuous (P.integratedStarAlgHomL1 μ) :=
  (P.integratedStarAlgHom μ).continuous_fromCompletion _

theorem norm_integratedStarAlgHomL1_le (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    ‖P.integratedStarAlgHomL1 μ x‖ ≤ ‖x‖ := by
  simpa only [integratedStarAlgHomL1_apply] using P.norm_integratedOperatorL1_le μ x

end Star

section Untwisted

/-- `CentralCovariantPair H α 1` is canonically equivalent to nondegenerate
`CovariantRepresentation α H`. -/
def equivCovariantRepresentation :
    CentralCovariantPair H α 1 ≃
      {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate} where
  toFun P :=
    ⟨P.toCovariantRepresentation,
      P.toCovariantRepresentation_coefficient.symm ▸ P.nondegenerate⟩
  invFun Q := Q.val.toCentralCovariantPair Q.property
  left_inv P := P.toCentralCovariantPair_toCovariantRepresentation
    (P.toCovariantRepresentation_coefficient.symm ▸ P.nondegenerate)
  right_inv Q := Subtype.ext (Q.val.toCovariantRepresentation_toCentralCovariantPair Q.property)

end Untwisted

end TauCeti.CStarAction.CentralCovariantPair
