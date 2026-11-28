/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Algebra
public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Covariant
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Ring.Completion
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Hom

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
* `TwistedConvolutionAlgebra.untwistRingEquivL1` and
  `TwistedConvolutionAlgebra.untwistStarAlgEquivL1`: isometric extensions of `untwistRingEquiv` and
  `untwistStarAlgEquiv` to the `L¹` completions at `ω = 1`, together with the commuting identities
  intertwining the compact-support and `L¹` integrated homomorphisms across
  `CentralCovariantPair.equivCovariantRepresentation`.

## References

* J. Packer and I. Raeburn, *Twisted crossed products of C*-algebras*, Math. Proc. Cambridge
  Philos. Soc. 106 (1989), 293–311, Section 2.
* D. P. Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported CStarAlgebra InnerProductSpace MultiplierAlgebra

namespace TauCeti.CStarAction

namespace CentralCovariantPair

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {ω : CentralCocycle α} (P : CentralCovariantPair H α ω)

section Normed

variable [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ]

/-- The integrated form bundled as a contractive continuous linear map on
`TwistedConvolutionAlgebra ω μ`. -/
def integratedOperatorCLM : TwistedConvolutionAlgebra ω μ →L[ℂ] (H →L[ℂ] H) :=
  P.pi.integratedOperatorCLM ω P.strong_continuous μ P.norm_unitaryMap_le_one

@[simp] theorem integratedOperatorCLM_apply (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedOperatorCLM μ f = P.integratedOperator μ f.toFun := by
  rw [integratedOperatorCLM, NonUnitalStarAlgHom.integratedOperatorCLM_apply,
    P.integratedOperator_eq_pi]

/-- The operator norm of `P.integratedOperatorCLM μ` is at most `1`. -/
theorem norm_integratedOperatorCLM_le : ‖P.integratedOperatorCLM μ‖ ≤ 1 :=
  P.pi.norm_integratedOperatorCLM_le ω P.strong_continuous μ P.norm_unitaryMap_le_one zero_le_one

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The integrated form as a nonunital algebra homomorphism on `TwistedConvolutionAlgebra ω μ`. -/
def integratedNonUnitalAlgHom : TwistedConvolutionAlgebra ω μ →ₙₐ[ℂ] (H →L[ℂ] H) :=
  (P.integratedOperatorCLM μ).toNonUnitalAlgHomOfMul fun f g => by simp

@[simp] theorem integratedNonUnitalAlgHom_apply (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedNonUnitalAlgHom μ f = P.integratedOperator μ f.toFun := by
  rw [integratedNonUnitalAlgHom, ContinuousLinearMap.toNonUnitalAlgHomOfMul_apply,
    integratedOperatorCLM_apply]

@[fun_prop] theorem continuous_integratedNonUnitalAlgHom :
    Continuous (P.integratedNonUnitalAlgHom μ) :=
  (P.integratedOperatorCLM μ).continuous_toNonUnitalAlgHomOfMul _

/-- Extension by continuity of the integrated form to
`Completion (TwistedConvolutionAlgebra ω μ)`. -/
def integratedOperatorL1 :
    Completion (TwistedConvolutionAlgebra ω μ) →ₙₐ[ℂ] (H →L[ℂ] H) :=
  (P.integratedNonUnitalAlgHom μ).fromCompletion (P.continuous_integratedNonUnitalAlgHom μ)

@[simp] theorem integratedOperatorL1_coe (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedOperatorL1 μ f = P.integratedOperator μ f.toFun := by
  rw [integratedOperatorL1, NonUnitalAlgHom.fromCompletion_apply_coe,
    integratedNonUnitalAlgHom_apply]

@[fun_prop] theorem continuous_integratedOperatorL1 : Continuous (P.integratedOperatorL1 μ) :=
  NonUnitalAlgHom.continuous_fromCompletion _ _

/-- The `L¹` integrated form is a contraction: `‖P.integratedOperatorL1 μ x‖ ≤ ‖x‖`. -/
theorem norm_integratedOperatorL1_le (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    ‖P.integratedOperatorL1 μ x‖ ≤ ‖x‖ := by
  have h : ((P.integratedOperatorCLM μ).toNonUnitalAlgHomOfMul fun f g => by simp).fromCompletion
      ((P.integratedOperatorCLM μ).continuous_toNonUnitalAlgHomOfMul _) =
      P.integratedOperatorL1 μ :=
    NonUnitalAlgHom.fromCompletion_unique _ _ _ (P.continuous_integratedOperatorL1 μ) fun f => by
      simp
  rw [← h]
  simpa only [one_mul] using
    (P.integratedOperatorCLM μ).norm_fromCompletion_toNonUnitalAlgHomOfMul_le _
      (P.norm_integratedOperatorCLM_le μ) x

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
    P.integratedStarAlgHom μ f = P.integratedOperator μ f.toFun := by
  rw [integratedStarAlgHom, ContinuousLinearMap.toNonUnitalStarAlgHomOfMulStar_apply,
    integratedOperatorCLM_apply]

/-- The integrated `⋆`-homomorphism is contractive with respect to the `L¹` norm. -/
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
  (P.integratedStarAlgHom μ).fromCompletion (P.continuous_integratedStarAlgHom μ)

@[simp] theorem toNonUnitalAlgHom_integratedStarAlgHomL1 :
    (P.integratedStarAlgHomL1 μ).toNonUnitalAlgHom = P.integratedOperatorL1 μ := by
  rw [integratedStarAlgHomL1, NonUnitalStarAlgHom.toNonUnitalAlgHom_fromCompletion]
  exact NonUnitalAlgHom.fromCompletion_unique _ _ (P.integratedOperatorL1 μ)
    (P.continuous_integratedOperatorL1 μ) fun f => by simp

@[simp] theorem integratedStarAlgHomL1_apply (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    P.integratedStarAlgHomL1 μ x = P.integratedOperatorL1 μ x :=
  DFunLike.congr_fun (P.toNonUnitalAlgHom_integratedStarAlgHomL1 μ) x

theorem integratedStarAlgHomL1_coe (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedStarAlgHomL1 μ f = P.integratedOperator μ f.toFun := by
  rw [integratedStarAlgHomL1_apply, integratedOperatorL1_coe]

/-- The L¹ integrated form preserves the `⋆`-involution on the twisted L¹ completion. -/
@[simp] theorem integratedOperatorL1_star (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    P.integratedOperatorL1 μ (star x) = star (P.integratedOperatorL1 μ x) := by
  simpa only [integratedStarAlgHomL1_apply] using map_star (P.integratedStarAlgHomL1 μ) x

@[fun_prop] theorem continuous_integratedStarAlgHomL1 : Continuous (P.integratedStarAlgHomL1 μ) :=
  NonUnitalStarAlgHom.continuous_fromCompletion _ _

/-- The `L¹` integrated `⋆`-homomorphism is a contraction on the twisted `L¹` completion. -/
theorem norm_integratedStarAlgHomL1_le (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    ‖P.integratedStarAlgHomL1 μ x‖ ≤ ‖x‖ := by
  simpa only [integratedStarAlgHomL1_apply] using P.norm_integratedOperatorL1_le μ x

end Star

end CentralCovariantPair

section Untwisted

namespace TwistedConvolutionAlgebra

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NonUnitalCStarAlgebra A] [MeasurableSpace G] [OpensMeasurableSpace G]
  (α : CStarAction G A) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
  [MeasurableMul G] [μ.IsMulLeftInvariant]

private theorem isometry_untwistRingEquiv : Isometry (untwistRingEquiv α μ) :=
  AddMonoidHomClass.isometry_of_norm (untwistRingEquiv α μ) (norm_untwistRingEquiv α μ)

private theorem isometry_untwistRingEquiv_symm : Isometry (untwistRingEquiv α μ).symm :=
  AddMonoidHomClass.isometry_of_norm (untwistRingEquiv α μ).symm (norm_untwistRingEquiv_symm α μ)

/-- Isometric `ℂ`-linear ring equivalence between the `L¹` completions at `ω = 1`, without
requiring local compactness. -/
def untwistRingEquivL1 :
    Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) ≃+*
      Completion (ConvolutionAlgebra α μ) where
  toFun := Completion.map (untwistRingEquiv α μ)
  invFun := Completion.map (untwistRingEquiv α μ).symm
  left_inv x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (Completion.continuous_map.comp Completion.continuous_map) continuous_id
    | ih f =>
      simp only [Completion.map_coe (isometry_untwistRingEquiv α μ).uniformContinuous,
        Completion.map_coe (isometry_untwistRingEquiv_symm α μ).uniformContinuous,
        RingEquiv.symm_apply_apply]
  right_inv y := by
    induction y using Completion.induction_on with
    | hp =>
      exact isClosed_eq (Completion.continuous_map.comp Completion.continuous_map) continuous_id
    | ih f =>
      simp only [Completion.map_coe (isometry_untwistRingEquiv_symm α μ).uniformContinuous,
        Completion.map_coe (isometry_untwistRingEquiv α μ).uniformContinuous,
        RingEquiv.apply_symm_apply]
  map_mul' x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f g =>
      simp only [← Completion.coe_mul',
        Completion.map_coe (isometry_untwistRingEquiv α μ).uniformContinuous, map_mul]
  map_add' x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f g =>
      simp only [← Completion.coe_add,
        Completion.map_coe (isometry_untwistRingEquiv α μ).uniformContinuous, map_add]

@[simp] theorem untwistRingEquivL1_coe
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    untwistRingEquivL1 α μ f = (untwistRingEquiv α μ f : Completion (ConvolutionAlgebra α μ)) :=
  Completion.map_coe (isometry_untwistRingEquiv α μ).uniformContinuous f

@[simp] theorem untwistRingEquivL1_symm_coe (f : ConvolutionAlgebra α μ) :
    (untwistRingEquivL1 α μ).symm f =
      ((untwistRingEquiv α μ).symm f :
        Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :=
  Completion.map_coe (isometry_untwistRingEquiv_symm α μ).uniformContinuous f

@[fun_prop, continuity]
theorem continuous_untwistRingEquivL1 : Continuous (untwistRingEquivL1 α μ) :=
  Completion.continuous_map

@[fun_prop, continuity]
theorem continuous_untwistRingEquivL1_symm : Continuous (untwistRingEquivL1 α μ).symm :=
  Completion.continuous_map

@[simp] theorem untwistRingEquivL1_smul (c : ℂ)
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    untwistRingEquivL1 α μ (c • x) = c • untwistRingEquivL1 α μ x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    simp only [← Completion.coe_smul, untwistRingEquivL1_coe, untwistRingEquiv_smul]

@[simp] theorem untwistRingEquivL1_symm_smul (c : ℂ)
    (y : Completion (ConvolutionAlgebra α μ)) :
    (untwistRingEquivL1 α μ).symm (c • y) = c • (untwistRingEquivL1 α μ).symm y := by
  induction y using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    simp only [← Completion.coe_smul, untwistRingEquivL1_symm_coe, untwistRingEquiv_symm_smul]

@[simp] theorem norm_untwistRingEquivL1
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    ‖untwistRingEquivL1 α μ x‖ = ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp only [untwistRingEquivL1_coe, Completion.norm_coe, norm_untwistRingEquiv]

@[simp] theorem norm_untwistRingEquivL1_symm
    (y : Completion (ConvolutionAlgebra α μ)) :
    ‖(untwistRingEquivL1 α μ).symm y‖ = ‖y‖ := by
  induction y using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    simp only [untwistRingEquivL1_symm_coe, Completion.norm_coe, norm_untwistRingEquiv_symm]

section LocallyCompact

variable [LocallyCompactSpace G]

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
private theorem untwistStarAlgEquiv_eq_untwistRingEquiv
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    untwistStarAlgEquiv α μ f = untwistRingEquiv α μ f := by
  ext1; simp

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
private theorem untwistStarAlgEquiv_symm_eq_untwistRingEquiv_symm
    (f : ConvolutionAlgebra α μ) :
    (untwistStarAlgEquiv α μ).symm f = (untwistRingEquiv α μ).symm f := by
  ext1; simp

variable [BorelSpace G]

/-- Isometric nonunital `⋆`-algebra equivalence between the `L¹` completions
`Completion (TwistedConvolutionAlgebra 1 μ)` and `Completion (ConvolutionAlgebra α μ)`. -/
def untwistStarAlgEquivL1 :
    Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) ≃⋆ₐ[ℂ]
      Completion (ConvolutionAlgebra α μ) where
  __ := untwistRingEquivL1 α μ
  map_smul' := untwistRingEquivL1_smul α μ
  map_star' x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq ((continuous_untwistRingEquivL1 α μ).comp continuous_star)
        (continuous_star.comp (continuous_untwistRingEquivL1 α μ))
    | ih f =>
      change untwistRingEquivL1 α μ (star (f : Completion _)) =
        star (untwistRingEquivL1 α μ f)
      rw [← Completion.coe_star, untwistRingEquivL1_coe, untwistRingEquivL1_coe,
        ← Completion.coe_star]
      refine congrArg
        ((↑) : ConvolutionAlgebra α μ → Completion (ConvolutionAlgebra α μ)) ?_
      simp only [← untwistStarAlgEquiv_eq_untwistRingEquiv, map_star]

@[simp] theorem toRingEquiv_untwistStarAlgEquivL1 :
    (untwistStarAlgEquivL1 α μ).toRingEquiv = untwistRingEquivL1 α μ :=
  (rfl)

theorem untwistStarAlgEquivL1_apply
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    untwistStarAlgEquivL1 α μ x = untwistRingEquivL1 α μ x := by
  rw [untwistStarAlgEquivL1]; rfl

theorem untwistStarAlgEquivL1_symm_apply
    (y : Completion (ConvolutionAlgebra α μ)) :
    (untwistStarAlgEquivL1 α μ).symm y = (untwistRingEquivL1 α μ).symm y := by
  rw [untwistStarAlgEquivL1]; rfl

@[simp] theorem untwistStarAlgEquivL1_coe
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    untwistStarAlgEquivL1 α μ f =
      (untwistStarAlgEquiv α μ f : Completion (ConvolutionAlgebra α μ)) := by
  rw [untwistStarAlgEquivL1_apply, untwistRingEquivL1_coe,
    untwistStarAlgEquiv_eq_untwistRingEquiv]

@[simp] theorem untwistStarAlgEquivL1_symm_coe (f : ConvolutionAlgebra α μ) :
    (untwistStarAlgEquivL1 α μ).symm f =
      ((untwistStarAlgEquiv α μ).symm f :
        Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) := by
  rw [untwistStarAlgEquivL1_symm_apply, untwistRingEquivL1_symm_coe,
    untwistStarAlgEquiv_symm_eq_untwistRingEquiv_symm]

@[fun_prop, continuity]
theorem continuous_untwistStarAlgEquivL1 : Continuous (untwistStarAlgEquivL1 α μ) := by
  simpa only [funext (untwistStarAlgEquivL1_apply α μ)] using
    continuous_untwistRingEquivL1 α μ

@[fun_prop, continuity]
theorem continuous_untwistStarAlgEquivL1_symm : Continuous (untwistStarAlgEquivL1 α μ).symm := by
  simpa only [funext (untwistStarAlgEquivL1_symm_apply α μ)] using
    continuous_untwistRingEquivL1_symm α μ

@[simp] theorem norm_untwistStarAlgEquivL1
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    ‖untwistStarAlgEquivL1 α μ x‖ = ‖x‖ := by
  rw [untwistStarAlgEquivL1_apply, norm_untwistRingEquivL1]

@[simp] theorem norm_untwistStarAlgEquivL1_symm
    (y : Completion (ConvolutionAlgebra α μ)) :
    ‖(untwistStarAlgEquivL1 α μ).symm y‖ = ‖y‖ := by
  rw [untwistStarAlgEquivL1_symm_apply, norm_untwistRingEquivL1_symm]

end LocallyCompact

end TwistedConvolutionAlgebra

namespace CentralCovariantPair

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} [MeasurableSpace G] [OpensMeasurableSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

theorem equivCovariantRepresentation_integratedOperatorCLM
    (P : CentralCovariantPair H α 1)
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    (equivCovariantRepresentation P).val.integratedOperatorCLM μ
        (TwistedConvolutionAlgebra.untwistRingEquiv α μ f) =
      P.integratedOperatorCLM μ f := by
  simp

theorem equivCovariantRepresentation_symm_integratedOperatorCLM
    (Q : {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate})
    (f : ConvolutionAlgebra α μ) :
    (equivCovariantRepresentation.symm Q).integratedOperatorCLM μ
        ((TwistedConvolutionAlgebra.untwistRingEquiv α μ).symm f) =
      Q.val.integratedOperatorCLM μ f := by
  simp

section Multiplication

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

theorem equivCovariantRepresentation_integratedNonUnitalAlgHom
    (P : CentralCovariantPair H α 1)
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    (equivCovariantRepresentation P).val.integratedNonUnitalAlgHom μ
        (TwistedConvolutionAlgebra.untwistRingEquiv α μ f) =
      P.integratedNonUnitalAlgHom μ f := by
  simp

theorem equivCovariantRepresentation_symm_integratedNonUnitalAlgHom
    (Q : {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate})
    (f : ConvolutionAlgebra α μ) :
    (equivCovariantRepresentation.symm Q).integratedNonUnitalAlgHom μ
        ((TwistedConvolutionAlgebra.untwistRingEquiv α μ).symm f) =
      Q.val.integratedNonUnitalAlgHom μ f := by
  simp

theorem equivCovariantRepresentation_integratedOperatorL1
    (P : CentralCovariantPair H α 1)
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    (equivCovariantRepresentation P).val.integratedOperatorL1 μ
        (TwistedConvolutionAlgebra.untwistRingEquivL1 α μ x) =
      P.integratedOperatorL1 μ x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((CovariantRepresentation.continuous_integratedOperatorL1 _ μ).comp
        (TwistedConvolutionAlgebra.continuous_untwistRingEquivL1 α μ))
      (P.continuous_integratedOperatorL1 μ)
  | ih f =>
    simp only [TwistedConvolutionAlgebra.untwistRingEquivL1_coe,
      CovariantRepresentation.integratedOperatorL1_coe,
      TwistedConvolutionAlgebra.toFun_untwistRingEquiv,
      integratedOperatorL1_coe, coe_equivCovariantRepresentation_apply,
      toCovariantRepresentation_integratedOperator]

theorem equivCovariantRepresentation_symm_integratedOperatorL1
    (Q : {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate})
    (y : Completion (ConvolutionAlgebra α μ)) :
    (equivCovariantRepresentation.symm Q).integratedOperatorL1 μ
        ((TwistedConvolutionAlgebra.untwistRingEquivL1 α μ).symm y) =
      Q.val.integratedOperatorL1 μ y := by
  have h := equivCovariantRepresentation_integratedOperatorL1 μ
    (equivCovariantRepresentation.symm Q)
    ((TwistedConvolutionAlgebra.untwistRingEquivL1 α μ).symm y)
  simpa only [Equiv.apply_symm_apply, RingEquiv.apply_symm_apply] using h.symm

end Multiplication

section Star

variable [LocallyCompactSpace G] [BorelSpace G] [μ.IsMulLeftInvariant]

theorem equivCovariantRepresentation_integratedStarAlgHom_comp
    (P : CentralCovariantPair H α 1) :
    ((equivCovariantRepresentation P).val.integratedStarAlgHom μ).comp
        (TwistedConvolutionAlgebra.untwistStarAlgEquiv α μ).toNonUnitalStarAlgHom =
      P.integratedStarAlgHom μ := by
  ext1 f
  simp

theorem equivCovariantRepresentation_symm_integratedStarAlgHom_comp
    (Q : {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate}) :
    ((equivCovariantRepresentation.symm Q).integratedStarAlgHom μ).comp
        (TwistedConvolutionAlgebra.untwistStarAlgEquiv α μ).symm.toNonUnitalStarAlgHom =
      Q.val.integratedStarAlgHom μ := by
  ext1 f
  simp

theorem equivCovariantRepresentation_integratedStarAlgHom
    (P : CentralCovariantPair H α 1)
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    (equivCovariantRepresentation P).val.integratedStarAlgHom μ
        (TwistedConvolutionAlgebra.untwistStarAlgEquiv α μ f) =
      P.integratedStarAlgHom μ f :=
  DFunLike.congr_fun (equivCovariantRepresentation_integratedStarAlgHom_comp μ P) f

theorem equivCovariantRepresentation_symm_integratedStarAlgHom
    (Q : {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate})
    (f : ConvolutionAlgebra α μ) :
    (equivCovariantRepresentation.symm Q).integratedStarAlgHom μ
        ((TwistedConvolutionAlgebra.untwistStarAlgEquiv α μ).symm f) =
      Q.val.integratedStarAlgHom μ f :=
  DFunLike.congr_fun (equivCovariantRepresentation_symm_integratedStarAlgHom_comp μ Q) f

theorem equivCovariantRepresentation_integratedStarAlgHomL1_comp
    (P : CentralCovariantPair H α 1) :
    ((equivCovariantRepresentation P).val.integratedStarAlgHomL1 μ).comp
        (TwistedConvolutionAlgebra.untwistStarAlgEquivL1 α μ).toNonUnitalStarAlgHom =
      P.integratedStarAlgHomL1 μ := by
  ext1 x
  simp only [NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    CovariantRepresentation.integratedStarAlgHomL1_apply, integratedStarAlgHomL1_apply,
    TwistedConvolutionAlgebra.untwistStarAlgEquivL1_apply]
  exact equivCovariantRepresentation_integratedOperatorL1 μ P x

theorem equivCovariantRepresentation_symm_integratedStarAlgHomL1_comp
    (Q : {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate}) :
    ((equivCovariantRepresentation.symm Q).integratedStarAlgHomL1 μ).comp
        (TwistedConvolutionAlgebra.untwistStarAlgEquivL1 α μ).symm.toNonUnitalStarAlgHom =
      Q.val.integratedStarAlgHomL1 μ := by
  ext1 y
  simp only [NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    integratedStarAlgHomL1_apply, CovariantRepresentation.integratedStarAlgHomL1_apply,
    TwistedConvolutionAlgebra.untwistStarAlgEquivL1_symm_apply]
  exact equivCovariantRepresentation_symm_integratedOperatorL1 μ Q y

theorem equivCovariantRepresentation_integratedStarAlgHomL1
    (P : CentralCovariantPair H α 1)
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    (equivCovariantRepresentation P).val.integratedStarAlgHomL1 μ
        (TwistedConvolutionAlgebra.untwistStarAlgEquivL1 α μ x) =
      P.integratedStarAlgHomL1 μ x :=
  DFunLike.congr_fun (equivCovariantRepresentation_integratedStarAlgHomL1_comp μ P) x

theorem equivCovariantRepresentation_symm_integratedStarAlgHomL1
    (Q : {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate})
    (y : Completion (ConvolutionAlgebra α μ)) :
    (equivCovariantRepresentation.symm Q).integratedStarAlgHomL1 μ
        ((TwistedConvolutionAlgebra.untwistStarAlgEquivL1 α μ).symm y) =
      Q.val.integratedStarAlgHomL1 μ y :=
  DFunLike.congr_fun (equivCovariantRepresentation_symm_integratedStarAlgHomL1_comp μ Q) y

end Star

end CentralCovariantPair

end Untwisted

end TauCeti.CStarAction
