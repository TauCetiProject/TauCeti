/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Algebra
public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Completion
public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Covariant
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star
public import TauCeti.MeasureTheory.Function.Lp.CompactlySupported.L1Completion
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Hom
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# Integrated L¹ representations of twisted covariant pairs

For a point-norm continuous action `α` of a topological group `G` on a C⋆-algebra `A` and a
normalized continuous central multiplier cocycle `ω : CentralCocycle α`, the vector-valued
integrated form `P.integratedOperator μ` of a twisted covariant pair
`P : CentralCovariantPair H α ω` extends to contractive maps on
`TwistedConvolutionAlgebra ω μ` and its `L¹` completion
`UniformSpace.Completion (TwistedConvolutionAlgebra ω μ)`:

* `CentralCovariantPair.integratedOperatorCLM`: contractive continuous linear map on
  `TwistedConvolutionAlgebra ω μ` for any `[OpensMeasurableSpace G]` and
  `[IsFiniteMeasureOnCompacts μ]` (without topological-group continuity of multiplication,
  left invariance, or local compactness).
* `CentralCovariantPair.integratedNonUnitalAlgHom` and
  `CentralCovariantPair.integratedOperatorL1`: contractive nonunital algebra homomorphisms on
  `TwistedConvolutionAlgebra ω μ` and its completion when `G` is a topological group with
  `[MeasurableMul G]` and `[μ.IsMulLeftInvariant]`; under
  `[R1Space G] [WeaklyLocallyCompactSpace G] [BorelSpace G] [μ.InnerRegularCompactLTTop]`,
  `CentralCovariantPair.integratedOperatorL1_completionEquivL1_symm_apply` evaluates
  `P.integratedOperatorL1 μ` on Bochner `Lp A 1 μ` coefficients by the vector integral
  `v ↦ ∫ g, P.pi (f g) ((P.unitaryMap g : H →L[ℂ] H) v) ∂μ`.
* `CentralCovariantPair.integratedStarAlgHom` and
  `CentralCovariantPair.integratedStarAlgHomL1`: contractive complex nonunital `⋆`-algebra
  homomorphisms when `G` is additionally locally compact and Borel (`[LocallyCompactSpace G]`,
  `[BorelSpace G]`).
* `CentralCovariantPair.equivCovariantRepresentation_integratedOperatorCLM`,
  `CentralCovariantPair.equivCovariantRepresentation_integratedOperatorL1`, and
  `CentralCovariantPair.equivCovariantRepresentation_integratedStarAlgHomL1` (and their reverse
  `.symm` forms): commuting comparison identities at `ω = 1` intertwining the compact-support
  and `L¹` integrated homomorphisms across `CentralCovariantPair.equivCovariantRepresentation`
  and `TwistedConvolutionAlgebra.untwistRingEquiv` / `untwistRingEquivL1` /
  `untwistStarAlgEquiv` / `untwistStarAlgEquivL1` (the `L¹` untwisting equivalences live in
  `TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Completion`).

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
  rw [integratedOperatorL1]
  simpa only [one_mul] using
    (P.integratedNonUnitalAlgHom μ).norm_fromCompletion_le
      (P.continuous_integratedNonUnitalAlgHom μ) (C := 1)
      (fun f => by
        simpa only [integratedNonUnitalAlgHom, ContinuousLinearMap.toNonUnitalAlgHomOfMul_apply]
          using (P.integratedOperatorCLM μ).le_of_opNorm_le (P.norm_integratedOperatorCLM_le μ) f)
      x

section BochnerL1

omit [IsTopologicalGroup G] [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
  [MeasurableMul G] [μ.IsMulLeftInvariant] [MeasurableSpace G] in
private theorem norm_pi_unitaryMap_le (a : A) (g : G) (v : H) :
    ‖P.pi a ((P.unitaryMap g : H →L[ℂ] H) v)‖ ≤ ‖a‖ * ‖v‖ := by
  refine (P.pi a).le_opNorm _ |>.trans ?_
  rw [Unitary.norm_map]
  exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)

omit [IsTopologicalGroup G] [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
  [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- For a Bochner-integrable coefficient function `f : G → A` against an inner-regular Borel
measure on an `R₁` space, `g ↦ P.pi (f g) ((P.unitaryMap g : H →L[ℂ] H) v)` is Bochner
integrable. -/
theorem integrable_integrand_of_integrable [R1Space G] [BorelSpace G]
    [μ.InnerRegularCompactLTTop] {f : G → A} (hf : Integrable f μ) (v : H) :
    Integrable (fun g => P.pi (f g) ((P.unitaryMap g : H →L[ℂ] H) v)) μ := by
  let L : H →L[ℂ] A →L[ℂ] H :=
    ({ toLinearMap := (P.pi : A →ₗ[ℂ] H →L[ℂ] H)
       cont := map_continuous P.pi } : A →L[ℂ] H →L[ℂ] H).flip
  have hmeas : AEStronglyMeasurable (fun g => L ((P.unitaryMap g : H →L[ℂ] H) v) (f g)) μ :=
    hf.aefinStronglyMeasurable.aestronglyMeasurable_clm_apply
      (L.continuous.comp (P.strong_continuous v))
  exact (hf.norm.mul_const ‖v‖).mono' hmeas
    (.of_forall fun g => P.norm_pi_unitaryMap_le _ g v)

omit [IsTopologicalGroup G] [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
  [MeasurableMul G] [μ.IsMulLeftInvariant] in
private theorem norm_integral_pi_unitaryMap_le {f : G → A} (hf : Integrable f μ) (v : H) :
    ‖∫ g, P.pi (f g) ((P.unitaryMap g : H →L[ℂ] H) v) ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖v‖ := by
  rw [← integral_mul_const]
  exact norm_integral_le_of_norm_le (hf.norm.mul_const _)
    (.of_forall fun g => P.norm_pi_unitaryMap_le _ g v)

variable [R1Space G] [WeaklyLocallyCompactSpace G] [BorelSpace G] [μ.InnerRegularCompactLTTop]

/-- Evaluating `P.integratedOperatorL1 μ` on the completion class corresponding to a Bochner `L¹`
function `f : Lp A 1 μ` computes the Hilbert-space vector integral
`v ↦ ∫ g, P.pi (f g) ((P.unitaryMap g : H →L[ℂ] H) v) ∂μ`. -/
theorem integratedOperatorL1_completionEquivL1_symm_apply (f : Lp A 1 μ) (v : H) :
    P.integratedOperatorL1 μ ((CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm f) v =
      ∫ g, P.pi (f g) ((P.unitaryMap g : H →L[ℂ] H) v) ∂μ := by
  let T : Lp A 1 μ →ₗ[ℂ] H :=
    { toFun := fun u => ∫ g, P.pi (u g) ((P.unitaryMap g : H →L[ℂ] H) v) ∂μ
      map_add' := fun u₁ u₂ => by
        rw [← integral_add
          (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u₁) v)
          (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u₂) v)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add u₁ u₂] with g hg
        rw [hg, Pi.add_apply, map_add, add_apply]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, ← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c u] with g hg
        rw [hg, Pi.smul_apply, map_smul, smul_apply] }
  have hT_cont : Continuous T :=
    AddMonoidHomClass.continuous_of_bound T ‖v‖ fun u => by
      have h := P.norm_integral_pi_unitaryMap_le μ (L1.integrable_coeFn u) v
      rw [← L1.norm_eq_integral_norm] at h
      dsimp only [T]
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, mul_comm ‖v‖ ‖u‖] using h
  have hc₁ : Continuous fun u : Lp A 1 μ =>
      P.integratedOperatorL1 μ ((CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm u) v :=
    ((ContinuousLinearMap.apply ℂ H v).continuous.comp
      ((P.continuous_integratedOperatorL1 μ).comp
        (CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm.continuous))
  refine congrFun ((CompactlySupportedL1.denseRange_toL1 ℂ
    (tag := ω) (E := A) (μ := μ)).equalizer hc₁ hT_cont ?_) f
  ext g : 1
  dsimp only [Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, T]
  rw [CompactlySupportedL1.completionEquivL1_symm_toL1, P.integratedOperatorL1_coe,
    P.integratedOperator_apply]
  refine integral_congr_ae ?_
  filter_upwards [CompactlySupportedL1.coeFn_toL1 (tag := ω) (E := A) (μ := μ) ℂ g] with s hs
  rw [hs]

/-- Evaluating `P.integratedOperatorL1 μ` on the completion class of the `L¹` representative of
an integrable function `f : G → A` computes the vector integral
`v ↦ ∫ g, P.pi (f g) ((P.unitaryMap g : H →L[ℂ] H) v) ∂μ`. -/
@[simp] theorem integratedOperatorL1_completionEquivL1_symm_toL1_apply {f : G → A}
    (hf : Integrable f μ) (v : H) :
    P.integratedOperatorL1 μ ((CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm
        (hf.toL1 f)) v =
      ∫ g, P.pi (f g) ((P.unitaryMap g : H →L[ℂ] H) v) ∂μ := by
  rw [P.integratedOperatorL1_completionEquivL1_symm_apply]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL1] with g hg
  rw [hg]

end BochnerL1

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

namespace CentralCovariantPair

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} [MeasurableSpace G] [OpensMeasurableSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- Forward comparison for `integratedOperatorCLM` at `ω = 1`: applying the untwisted
`CovariantRepresentation.integratedOperatorCLM` of `equivCovariantRepresentation P` after
`TwistedConvolutionAlgebra.untwistRingEquiv` agrees pointwise with `P.integratedOperatorCLM μ`. -/
theorem equivCovariantRepresentation_integratedOperatorCLM
    (P : CentralCovariantPair H α 1)
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    (equivCovariantRepresentation P).val.integratedOperatorCLM μ
        (TwistedConvolutionAlgebra.untwistRingEquiv α μ f) =
      P.integratedOperatorCLM μ f := by
  simp

/-- Reverse comparison for `integratedOperatorCLM` at `ω = 1`: applying
`(equivCovariantRepresentation.symm Q).integratedOperatorCLM μ` after
`(TwistedConvolutionAlgebra.untwistRingEquiv α μ).symm` agrees pointwise with
`Q.val.integratedOperatorCLM μ`. -/
theorem equivCovariantRepresentation_symm_integratedOperatorCLM
    (Q : {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate})
    (f : ConvolutionAlgebra α μ) :
    (equivCovariantRepresentation.symm Q).integratedOperatorCLM μ
        ((TwistedConvolutionAlgebra.untwistRingEquiv α μ).symm f) =
      Q.val.integratedOperatorCLM μ f := by
  simp

section Multiplication

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Forward comparison for `integratedNonUnitalAlgHom` at `ω = 1`: evaluating
`(equivCovariantRepresentation P).val.integratedNonUnitalAlgHom μ` after
`TwistedConvolutionAlgebra.untwistRingEquiv` agrees pointwise with
`P.integratedNonUnitalAlgHom μ`. -/
theorem equivCovariantRepresentation_integratedNonUnitalAlgHom
    (P : CentralCovariantPair H α 1)
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    (equivCovariantRepresentation P).val.integratedNonUnitalAlgHom μ
        (TwistedConvolutionAlgebra.untwistRingEquiv α μ f) =
      P.integratedNonUnitalAlgHom μ f := by
  simp

/-- Reverse comparison for `integratedNonUnitalAlgHom` at `ω = 1`: evaluating
`(equivCovariantRepresentation.symm Q).integratedNonUnitalAlgHom μ` after
`(TwistedConvolutionAlgebra.untwistRingEquiv α μ).symm` agrees pointwise with
`Q.val.integratedNonUnitalAlgHom μ`. -/
theorem equivCovariantRepresentation_symm_integratedNonUnitalAlgHom
    (Q : {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate})
    (f : ConvolutionAlgebra α μ) :
    (equivCovariantRepresentation.symm Q).integratedNonUnitalAlgHom μ
        ((TwistedConvolutionAlgebra.untwistRingEquiv α μ).symm f) =
      Q.val.integratedNonUnitalAlgHom μ f := by
  simp

/-- Forward comparison on `L¹` completions at `ω = 1`: evaluating
`(equivCovariantRepresentation P).val.integratedOperatorL1 μ` after
`TwistedConvolutionAlgebra.untwistRingEquivL1` agrees pointwise with `P.integratedOperatorL1 μ`. -/
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

/-- Reverse comparison on `L¹` completions at `ω = 1`: evaluating
`(equivCovariantRepresentation.symm Q).integratedOperatorL1 μ` after
`(TwistedConvolutionAlgebra.untwistRingEquivL1 α μ).symm` agrees pointwise with
`Q.val.integratedOperatorL1 μ`. -/
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

/-- Forward bundled `⋆`-homomorphism comparison at `ω = 1`: precomposing
`(equivCovariantRepresentation P).val.integratedStarAlgHom μ` with
`TwistedConvolutionAlgebra.untwistStarAlgEquiv` equals `P.integratedStarAlgHom μ`. -/
theorem equivCovariantRepresentation_integratedStarAlgHom_comp
    (P : CentralCovariantPair H α 1) :
    ((equivCovariantRepresentation P).val.integratedStarAlgHom μ).comp
        (TwistedConvolutionAlgebra.untwistStarAlgEquiv α μ).toNonUnitalStarAlgHom =
      P.integratedStarAlgHom μ := by
  ext1 f
  simp

/-- Reverse bundled `⋆`-homomorphism comparison at `ω = 1`: precomposing
`(equivCovariantRepresentation.symm Q).integratedStarAlgHom μ` with
`(TwistedConvolutionAlgebra.untwistStarAlgEquiv α μ).symm` equals
`Q.val.integratedStarAlgHom μ`. -/
theorem equivCovariantRepresentation_symm_integratedStarAlgHom_comp
    (Q : {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate}) :
    ((equivCovariantRepresentation.symm Q).integratedStarAlgHom μ).comp
        (TwistedConvolutionAlgebra.untwistStarAlgEquiv α μ).symm.toNonUnitalStarAlgHom =
      Q.val.integratedStarAlgHom μ := by
  ext1 f
  simp

/-- Forward pointwise comparison for `integratedStarAlgHom` at `ω = 1` across
`equivCovariantRepresentation` and `TwistedConvolutionAlgebra.untwistStarAlgEquiv`. -/
theorem equivCovariantRepresentation_integratedStarAlgHom
    (P : CentralCovariantPair H α 1)
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    (equivCovariantRepresentation P).val.integratedStarAlgHom μ
        (TwistedConvolutionAlgebra.untwistStarAlgEquiv α μ f) =
      P.integratedStarAlgHom μ f :=
  DFunLike.congr_fun (equivCovariantRepresentation_integratedStarAlgHom_comp μ P) f

/-- Reverse pointwise comparison for `integratedStarAlgHom` at `ω = 1` across
`equivCovariantRepresentation.symm` and
`(TwistedConvolutionAlgebra.untwistStarAlgEquiv α μ).symm`. -/
theorem equivCovariantRepresentation_symm_integratedStarAlgHom
    (Q : {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate})
    (f : ConvolutionAlgebra α μ) :
    (equivCovariantRepresentation.symm Q).integratedStarAlgHom μ
        ((TwistedConvolutionAlgebra.untwistStarAlgEquiv α μ).symm f) =
      Q.val.integratedStarAlgHom μ f :=
  DFunLike.congr_fun (equivCovariantRepresentation_symm_integratedStarAlgHom_comp μ Q) f

/-- Forward bundled `L¹` `⋆`-homomorphism comparison at `ω = 1`: precomposing
`(equivCovariantRepresentation P).val.integratedStarAlgHomL1 μ` with
`TwistedConvolutionAlgebra.untwistStarAlgEquivL1` equals `P.integratedStarAlgHomL1 μ`. -/
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

/-- Reverse bundled `L¹` `⋆`-homomorphism comparison at `ω = 1`: precomposing
`(equivCovariantRepresentation.symm Q).integratedStarAlgHomL1 μ` with
`(TwistedConvolutionAlgebra.untwistStarAlgEquivL1 α μ).symm` equals
`Q.val.integratedStarAlgHomL1 μ`. -/
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

/-- Forward pointwise comparison for `integratedStarAlgHomL1` at `ω = 1` across
`equivCovariantRepresentation` and `TwistedConvolutionAlgebra.untwistStarAlgEquivL1`. -/
theorem equivCovariantRepresentation_integratedStarAlgHomL1
    (P : CentralCovariantPair H α 1)
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    (equivCovariantRepresentation P).val.integratedStarAlgHomL1 μ
        (TwistedConvolutionAlgebra.untwistStarAlgEquivL1 α μ x) =
      P.integratedStarAlgHomL1 μ x :=
  DFunLike.congr_fun (equivCovariantRepresentation_integratedStarAlgHomL1_comp μ P) x

/-- Reverse pointwise comparison for `integratedStarAlgHomL1` at `ω = 1` across
`equivCovariantRepresentation.symm` and
`(TwistedConvolutionAlgebra.untwistStarAlgEquivL1 α μ).symm`. -/
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
