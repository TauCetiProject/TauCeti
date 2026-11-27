/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Algebra
public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Covariant
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Operator.Completion
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
  CompactlySupportedL1.liftCLM (P.integratedOperator μ) 1 fun f => by
    simpa only [one_mul] using P.norm_integratedOperator_le μ f

@[simp] theorem integratedOperatorCLM_apply (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedOperatorCLM μ f = P.integratedOperator μ f.ofConv :=
  CompactlySupportedL1.liftCLM_apply (P.integratedOperator μ) _ f

theorem norm_integratedOperatorCLM_le : ‖P.integratedOperatorCLM μ‖ ≤ 1 :=
  CompactlySupportedL1.norm_liftCLM_le (P.integratedOperator μ) zero_le_one _

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The integrated form as a nonunital algebra homomorphism on `TwistedConvolutionAlgebra ω μ`. -/
def integratedNonUnitalAlgHom : TwistedConvolutionAlgebra ω μ →ₙₐ[ℂ] (H →L[ℂ] H) :=
  (P.integratedOperatorCLM μ).toNonUnitalAlgHomOfMul fun f g => by simp

@[simp] theorem integratedNonUnitalAlgHom_apply (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedNonUnitalAlgHom μ f = P.integratedOperator μ f.ofConv := by
  rw [integratedNonUnitalAlgHom, ContinuousLinearMap.toNonUnitalAlgHomOfMul_apply,
    integratedOperatorCLM_apply]

@[fun_prop] theorem continuous_integratedNonUnitalAlgHom :
    Continuous (P.integratedNonUnitalAlgHom μ) :=
  (P.integratedOperatorCLM μ).continuous_toNonUnitalAlgHomOfMul _

/-- Extension by continuity of the integrated form to
`Completion (TwistedConvolutionAlgebra ω μ)`. -/
def integratedOperatorL1 :
    Completion (TwistedConvolutionAlgebra ω μ) →ₙₐ[ℂ] (H →L[ℂ] H) :=
  ((P.integratedOperatorCLM μ).toNonUnitalAlgHomOfMul fun f g => by simp).fromCompletion
    ((P.integratedOperatorCLM μ).continuous_toNonUnitalAlgHomOfMul _)

@[simp] theorem integratedOperatorL1_coe (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedOperatorL1 μ f = P.integratedOperator μ f.ofConv := by
  rw [integratedOperatorL1, NonUnitalAlgHom.fromCompletion_apply_coe,
    ContinuousLinearMap.toNonUnitalAlgHomOfMul_apply, integratedOperatorCLM_apply]

@[fun_prop] theorem continuous_integratedOperatorL1 : Continuous (P.integratedOperatorL1 μ) :=
  NonUnitalAlgHom.continuous_fromCompletion _ _

theorem norm_integratedOperatorL1_le (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    ‖P.integratedOperatorL1 μ x‖ ≤ ‖x‖ := by
  have hle : ‖(P.integratedOperatorCLM μ).fromCompletion‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_fromCompletion]
    exact P.norm_integratedOperatorCLM_le μ
  simpa only [integratedOperatorL1, NonUnitalAlgHom.coe_fromCompletion,
    ContinuousLinearMap.coe_toNonUnitalAlgHomOfMul, ContinuousLinearMap.coe_fromCompletion] using
    ((P.integratedOperatorCLM μ).fromCompletion.le_of_opNorm_le hle x).trans_eq (one_mul _)

end Multiplication

end Normed

section Star

variable [MeasurableSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- The integrated form as a nonunital complex ⋆-algebra homomorphism on
`TwistedConvolutionAlgebra ω μ`. -/
def integratedStarAlgHom : TwistedConvolutionAlgebra ω μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  (P.integratedOperatorCLM μ).toNonUnitalStarAlgHomOfMulStar (fun f g => by simp)
    (fun f => by simp)

@[simp] theorem integratedStarAlgHom_apply (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedStarAlgHom μ f = P.integratedOperator μ f.ofConv := by
  rw [integratedStarAlgHom, ContinuousLinearMap.toNonUnitalStarAlgHomOfMulStar_apply,
    integratedOperatorCLM_apply]

theorem norm_integratedStarAlgHom_le_norm (f : TwistedConvolutionAlgebra ω μ) :
    ‖P.integratedStarAlgHom μ f‖ ≤ ‖f‖ := by
  rw [integratedStarAlgHom, ContinuousLinearMap.toNonUnitalStarAlgHomOfMulStar_apply]
  exact ((P.integratedOperatorCLM μ).le_of_opNorm_le (P.norm_integratedOperatorCLM_le μ) f).trans_eq
    (one_mul _)

@[fun_prop] theorem continuous_integratedStarAlgHom : Continuous (P.integratedStarAlgHom μ) :=
  (P.integratedOperatorCLM μ).continuous_toNonUnitalStarAlgHomOfMulStar _ _

/-- Extension by continuity of the integrated ⋆-representation to
`Completion (TwistedConvolutionAlgebra ω μ)`. -/
def integratedStarAlgHomL1 :
    Completion (TwistedConvolutionAlgebra ω μ) →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  ((P.integratedOperatorCLM μ).toNonUnitalStarAlgHomOfMulStar (fun f g => by simp)
    (fun f => by simp)).fromCompletion
    ((P.integratedOperatorCLM μ).continuous_toNonUnitalStarAlgHomOfMulStar _ _)

@[simp] theorem toNonUnitalAlgHom_integratedStarAlgHomL1 :
    (P.integratedStarAlgHomL1 μ).toNonUnitalAlgHom = P.integratedOperatorL1 μ := by
  simp only [integratedStarAlgHomL1, NonUnitalStarAlgHom.toNonUnitalAlgHom_fromCompletion,
    ContinuousLinearMap.toNonUnitalAlgHom_toNonUnitalStarAlgHomOfMulStar,
    CentralCovariantPair.integratedOperatorL1]

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
  NonUnitalStarAlgHom.continuous_fromCompletion _ _

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
