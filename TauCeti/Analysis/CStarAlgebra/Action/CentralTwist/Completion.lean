/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Algebra
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.MeasureTheory.Function.Lp.CompactlySupported.L1Completion
public import TauCeti.Topology.Algebra.Star.Completion
public import TauCeti.Topology.Algebra.UniformRing

/-!
# Untwisted `L¹`-completion comparison at `ω = 1`

For the trivial cocycle `1 : CentralCocycle α`, the compact-support identification
`TwistedConvolutionAlgebra.untwistLIE` extends via `LinearIsometryEquiv.completion` to the `L¹`
completions `UniformSpace.Completion (TwistedConvolutionAlgebra 1 μ)` and
`UniformSpace.Completion (ConvolutionAlgebra α μ)`, giving:

* `TwistedConvolutionAlgebra.untwistRingEquivL1`: isometric `ℂ`-linear ring equivalence
  between the `L¹` completions (for a left-invariant measure finite on compacts, without local
  compactness);
* `TwistedConvolutionAlgebra.untwistStarAlgEquivL1`: isometric complex nonunital `⋆`-algebra
  equivalence between the `L¹` completions (under `[LocallyCompactSpace G] [BorelSpace G]`);
* `TwistedConvolutionAlgebra.completionEquivL1_untwistRingEquivL1` (and its symmetric and
  `untwistStarAlgEquivL1` forms): under `[R1Space G] [WeaklyLocallyCompactSpace G] [BorelSpace G]`
  and `[μ.InnerRegularCompactLTTop]`, completed untwisting commutes with
  `CompactlySupportedL1.completionEquivL1`, acting as the identity on the shared Bochner space
  `Lp A 1 μ`.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported

namespace TauCeti.CStarAction.TwistedConvolutionAlgebra

section Untwisted

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NonUnitalCStarAlgebra A] [MeasurableSpace G] [OpensMeasurableSpace G]
  (α : CStarAction G A) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
  [MeasurableMul G] [μ.IsMulLeftInvariant]

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
private theorem untwistLIE_eq_untwistRingEquiv
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    untwistLIE α μ f = untwistRingEquiv α μ f := by
  ext1; simp

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
private theorem untwistLIE_symm_eq_untwistRingEquiv_symm (f : ConvolutionAlgebra α μ) :
    (untwistLIE α μ).symm f = (untwistRingEquiv α μ).symm f := by
  ext1; simp

/-- Isometric `ℂ`-linear ring equivalence between the `L¹` completions at `ω = 1`, built from
`LinearIsometryEquiv.completion (untwistLIE α μ)` without requiring local compactness. -/
def untwistRingEquivL1 :
    Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) ≃+*
      Completion (ConvolutionAlgebra α μ) where
  __ := (untwistLIE α μ).completion
  map_mul' x y := by
    change (untwistLIE α μ).completion (x * y) =
      (untwistLIE α μ).completion x * (untwistLIE α μ).completion y
    rw [LinearIsometryEquiv.coe_completion]
    exact Completion.map_mul (untwistLIE α μ).isometry.uniformContinuous
      (fun a b => by
        rw [untwistLIE_eq_untwistRingEquiv, untwistLIE_eq_untwistRingEquiv,
          untwistLIE_eq_untwistRingEquiv, map_mul])
      x y

/-- `untwistRingEquivL1` agrees pointwise with `(untwistLIE α μ).completion`. -/
theorem untwistRingEquivL1_apply
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    untwistRingEquivL1 α μ x = (untwistLIE α μ).completion x :=
  (rfl)

/-- The inverse of `untwistRingEquivL1` agrees pointwise with `(untwistLIE α μ).completion.symm`. -/
theorem untwistRingEquivL1_symm_apply (y : Completion (ConvolutionAlgebra α μ)) :
    (untwistRingEquivL1 α μ).symm y = (untwistLIE α μ).completion.symm y :=
  (rfl)

@[simp] theorem untwistRingEquivL1_coe
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    untwistRingEquivL1 α μ f = (untwistRingEquiv α μ f : Completion (ConvolutionAlgebra α μ)) := by
  rw [untwistRingEquivL1_apply, LinearIsometryEquiv.completion_apply_coe,
    untwistLIE_eq_untwistRingEquiv]

@[simp] theorem untwistRingEquivL1_symm_coe (f : ConvolutionAlgebra α μ) :
    (untwistRingEquivL1 α μ).symm f =
      ((untwistRingEquiv α μ).symm f :
        Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) := by
  rw [untwistRingEquivL1_symm_apply, LinearIsometryEquiv.completion_symm_apply_coe,
    untwistLIE_symm_eq_untwistRingEquiv_symm]

@[fun_prop, continuity]
theorem continuous_untwistRingEquivL1 : Continuous (untwistRingEquivL1 α μ) :=
  (untwistLIE α μ).completion.continuous

@[fun_prop, continuity]
theorem continuous_untwistRingEquivL1_symm : Continuous (untwistRingEquivL1 α μ).symm :=
  (untwistLIE α μ).completion.symm.continuous

@[simp] theorem untwistRingEquivL1_smul (c : ℂ)
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    untwistRingEquivL1 α μ (c • x) = c • untwistRingEquivL1 α μ x :=
  (untwistLIE α μ).completion.map_smul c x

@[simp] theorem untwistRingEquivL1_symm_smul (c : ℂ)
    (y : Completion (ConvolutionAlgebra α μ)) :
    (untwistRingEquivL1 α μ).symm (c • y) = c • (untwistRingEquivL1 α μ).symm y :=
  (untwistLIE α μ).completion.symm.map_smul c y

@[simp] theorem norm_untwistRingEquivL1
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    ‖untwistRingEquivL1 α μ x‖ = ‖x‖ :=
  (untwistLIE α μ).completion.norm_map x

@[simp] theorem norm_untwistRingEquivL1_symm
    (y : Completion (ConvolutionAlgebra α μ)) :
    ‖(untwistRingEquivL1 α μ).symm y‖ = ‖y‖ :=
  (untwistLIE α μ).completion.symm.norm_map y

section BochnerComparison

variable [R1Space G] [WeaklyLocallyCompactSpace G] [BorelSpace G] [μ.InnerRegularCompactLTTop]

/-- `untwistRingEquivL1` commutes with `CompactlySupportedL1.completionEquivL1`, acting as the
identity on Bochner `Lp A 1 μ`. -/
@[simp] theorem completionEquivL1_untwistRingEquivL1
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    CompactlySupportedL1.completionEquivL1 α A μ ℂ (untwistRingEquivL1 α μ x) =
      CompactlySupportedL1.completionEquivL1 (1 : CentralCocycle α) A μ ℂ x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    simp only [untwistRingEquivL1_coe, CompactlySupportedL1.completionEquivL1_coe,
      CompactlySupportedL1.toL1_eq_toLp ℂ, toFun_untwistRingEquiv]

/-- The inverse `(untwistRingEquivL1 α μ).symm` commutes with
`CompactlySupportedL1.completionEquivL1`. -/
@[simp] theorem completionEquivL1_untwistRingEquivL1_symm
    (y : Completion (ConvolutionAlgebra α μ)) :
    CompactlySupportedL1.completionEquivL1 (1 : CentralCocycle α) A μ ℂ
        ((untwistRingEquivL1 α μ).symm y) =
      CompactlySupportedL1.completionEquivL1 α A μ ℂ y := by
  simpa only [RingEquiv.apply_symm_apply] using
    (completionEquivL1_untwistRingEquivL1 α μ ((untwistRingEquivL1 α μ).symm y)).symm

/-- Mapping a Bochner `L¹` element back to `Completion (TwistedConvolutionAlgebra 1 μ)` and
applying `untwistRingEquivL1` gives the corresponding element in
`Completion (ConvolutionAlgebra α μ)`. -/
@[simp] theorem untwistRingEquivL1_completionEquivL1_symm (f : Lp A 1 μ) :
    untwistRingEquivL1 α μ
        ((CompactlySupportedL1.completionEquivL1 (1 : CentralCocycle α) A μ ℂ).symm f) =
      (CompactlySupportedL1.completionEquivL1 α A μ ℂ).symm f := by
  apply (CompactlySupportedL1.completionEquivL1 α A μ ℂ).injective
  simp only [completionEquivL1_untwistRingEquivL1, LinearIsometryEquiv.apply_symm_apply]

/-- Mapping a Bochner `L¹` element back to `Completion (ConvolutionAlgebra α μ)` and applying
`(untwistRingEquivL1 α μ).symm` gives the corresponding element in
`Completion (TwistedConvolutionAlgebra 1 μ)`. -/
@[simp] theorem untwistRingEquivL1_symm_completionEquivL1_symm (f : Lp A 1 μ) :
    (untwistRingEquivL1 α μ).symm ((CompactlySupportedL1.completionEquivL1 α A μ ℂ).symm f) =
      (CompactlySupportedL1.completionEquivL1 (1 : CentralCocycle α) A μ ℂ).symm f := by
  apply (CompactlySupportedL1.completionEquivL1 (1 : CentralCocycle α) A μ ℂ).injective
  simp only [completionEquivL1_untwistRingEquivL1_symm, LinearIsometryEquiv.apply_symm_apply]

end BochnerComparison

section LocallyCompact

variable [LocallyCompactSpace G] [BorelSpace G]

omit [MeasurableMul G] [μ.IsMulLeftInvariant] [BorelSpace G] in
private theorem untwistStarAlgEquiv_eq_untwistRingEquiv
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    untwistStarAlgEquiv α μ f = untwistRingEquiv α μ f := by
  ext1; simp

omit [MeasurableMul G] [μ.IsMulLeftInvariant] [BorelSpace G] in
private theorem untwistStarAlgEquiv_symm_eq_untwistRingEquiv_symm
    (f : ConvolutionAlgebra α μ) :
    (untwistStarAlgEquiv α μ).symm f = (untwistRingEquiv α μ).symm f := by
  ext1; simp

/-- `untwistRingEquivL1` commutes with `star` on completions over a locally compact Borel group. -/
@[simp] theorem untwistRingEquivL1_star
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    untwistRingEquivL1 α μ (star x) = star (untwistRingEquivL1 α μ x) := by
  rw [untwistRingEquivL1_apply, untwistRingEquivL1_apply, LinearIsometryEquiv.coe_completion]
  exact Completion.map_star TauCeti.uniformContinuous_star TauCeti.uniformContinuous_star
    (untwistLIE α μ).isometry.uniformContinuous
    (fun f => by
      rw [untwistLIE_eq_untwistRingEquiv, untwistLIE_eq_untwistRingEquiv,
        ← untwistStarAlgEquiv_eq_untwistRingEquiv, ← untwistStarAlgEquiv_eq_untwistRingEquiv]
      exact map_star (untwistStarAlgEquiv α μ) f)
    x

/-- Isometric nonunital `⋆`-algebra equivalence between the `L¹` completions
`Completion (TwistedConvolutionAlgebra 1 μ)` and `Completion (ConvolutionAlgebra α μ)`. -/
def untwistStarAlgEquivL1 :
    Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) ≃⋆ₐ[ℂ]
      Completion (ConvolutionAlgebra α μ) where
  __ := untwistRingEquivL1 α μ
  map_smul' := untwistRingEquivL1_smul α μ
  map_star' := untwistRingEquivL1_star α μ

@[simp] theorem toRingEquiv_untwistStarAlgEquivL1 :
    (untwistStarAlgEquivL1 α μ).toRingEquiv = untwistRingEquivL1 α μ :=
  (rfl)

/-- `untwistStarAlgEquivL1` agrees pointwise with `untwistRingEquivL1`. -/
theorem untwistStarAlgEquivL1_apply
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    untwistStarAlgEquivL1 α μ x = untwistRingEquivL1 α μ x :=
  (rfl)

/-- The inverse of `untwistStarAlgEquivL1` agrees pointwise with `(untwistRingEquivL1 α μ).symm`. -/
theorem untwistStarAlgEquivL1_symm_apply
    (y : Completion (ConvolutionAlgebra α μ)) :
    (untwistStarAlgEquivL1 α μ).symm y = (untwistRingEquivL1 α μ).symm y :=
  (rfl)

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
theorem continuous_untwistStarAlgEquivL1 : Continuous (untwistStarAlgEquivL1 α μ) :=
  continuous_untwistRingEquivL1 α μ

@[fun_prop, continuity]
theorem continuous_untwistStarAlgEquivL1_symm : Continuous (untwistStarAlgEquivL1 α μ).symm :=
  continuous_untwistRingEquivL1_symm α μ

@[simp] theorem norm_untwistStarAlgEquivL1
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    ‖untwistStarAlgEquivL1 α μ x‖ = ‖x‖ :=
  norm_untwistRingEquivL1 α μ x

@[simp] theorem norm_untwistStarAlgEquivL1_symm
    (y : Completion (ConvolutionAlgebra α μ)) :
    ‖(untwistStarAlgEquivL1 α μ).symm y‖ = ‖y‖ :=
  norm_untwistRingEquivL1_symm α μ y

/-- `untwistStarAlgEquivL1` commutes with `CompactlySupportedL1.completionEquivL1`, acting as the
identity on Bochner `Lp A 1 μ`. -/
@[simp] theorem completionEquivL1_untwistStarAlgEquivL1 [μ.InnerRegularCompactLTTop]
    (x : Completion (TwistedConvolutionAlgebra (1 : CentralCocycle α) μ)) :
    CompactlySupportedL1.completionEquivL1 α A μ ℂ (untwistStarAlgEquivL1 α μ x) =
      CompactlySupportedL1.completionEquivL1 (1 : CentralCocycle α) A μ ℂ x :=
  completionEquivL1_untwistRingEquivL1 α μ x

/-- The inverse `(untwistStarAlgEquivL1 α μ).symm` commutes with
`CompactlySupportedL1.completionEquivL1`. -/
@[simp] theorem completionEquivL1_untwistStarAlgEquivL1_symm [μ.InnerRegularCompactLTTop]
    (y : Completion (ConvolutionAlgebra α μ)) :
    CompactlySupportedL1.completionEquivL1 (1 : CentralCocycle α) A μ ℂ
        ((untwistStarAlgEquivL1 α μ).symm y) =
      CompactlySupportedL1.completionEquivL1 α A μ ℂ y :=
  completionEquivL1_untwistRingEquivL1_symm α μ y

end LocallyCompact

end Untwisted

end TauCeti.CStarAction.TwistedConvolutionAlgebra
