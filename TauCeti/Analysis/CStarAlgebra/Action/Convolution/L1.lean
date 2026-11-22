/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Multiplier
public import TauCeti.Analysis.CStarAlgebra.Action.Lp
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.MeasureTheory.Function.Lp.CompactlySupported
public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
public import TauCeti.MeasureTheory.Function.Lp.Star
public import TauCeti.Topology.Algebra.UniformRing
import TauCeti.Analysis.Normed.Group.Completion
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular
import TauCeti.MeasureTheory.Group.Convolution.Support

/-!
# Realizing the twisted `L¹` Banach ⋆-algebra in Bochner `L¹`

Let `α : CStarAction G A` be a point-norm continuous action of a topological group `G` on a
possibly nonunital complex C⋆-algebra `A`. In
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed`, the compact-support convolution algebra
`CStarAction.ConvolutionAlgebra α μ` carries the `L¹` seminorm pulled back along
`ConvolutionAlgebra.toL1 : ConvolutionAlgebra α μ →ₗ[ℂ] Lp A 1 μ`, `toL1FromCompletion` extends
it from `UniformSpace.Completion (ConvolutionAlgebra α μ)` without local compactness, and the
abstract completion is the twisted `L¹` Banach ⋆-algebra.

When `G` is weakly locally compact and `μ` is finite on compact sets and inner regular on sets of
finite measure (`IsFiniteMeasureOnCompacts μ` and `μ.InnerRegularCompactLTTop`), compactly supported
continuous functions are dense in `Lp A 1 μ`. Consequently `toL1` has dense range and extends to a
linear isometric equivalence
`ConvolutionAlgebra.completionEquivL1 α μ : Completion (ConvolutionAlgebra α μ) ≃ₗᵢ[ℂ] Lp A 1 μ`,
agreeing with `toL1FromCompletion` (`toL1FromCompletion_eq_completionEquivL1`), and every `L¹` class
is the sum of an absolutely convergent series of compactly supported elements
(`ConvolutionAlgebra.exists_hasSum_toL1`). This holds without separability of `A`, second
countability of `G`, σ-finiteness of `μ`, unitality of `A`, or full support of `μ`, including zero
algebras and the zero measure.

Using `CStarAction.actionLp` and `CStarAction.translateLp` from
`TauCeti.Analysis.CStarAlgebra.Action.Lp`, we construct the concrete dynamical convolution and
involution on `Lp A p μ` and `Lp A 1 μ` and show that they match those of
`Completion (ConvolutionAlgebra α μ)` across `toL1FromCompletion` and `completionEquivL1`:

* `CStarAction.convolutionLp`: twisted Bochner `L¹` convolution on `Lp A p μ` for `1 ≤ p < ∞`
  (`Lp A 1 μ →L[ℂ] Lp A p μ →L[ℂ] Lp A p μ`), defined for any locally finite, inner-regular
  left-invariant Borel measure without local compactness, countability, or σ-finiteness
  hypotheses as the `Lp A p μ`-valued Bochner integral
  `h ⋆_α f = ∫ r, (ContinuousLinearMap.mul ℂ A (h r)).compLp (α.translateLp μ p r f) ∂μ`. The
  set-integral Fubini proof on `C_c(G, A)` for `1 ≤ p < ∞` (`CStarAction.convolutionLp_toLp_ae_eq`)
  uses `MeasureTheory.Lp.integral_ae_eq_integral_of_hasCompactSupport` from
  `TauCeti.MeasureTheory.Function.Lp.GroupConvolution`. Across `toL1FromCompletion` and
  `completionEquivL1`, multiplication in the completion corresponds to `convolutionLp` at `p = 1`.
* `CStarAction.twistedInvolutionL1`: the twisted involution on `Lp A 1 μ` as a conjugate-linear
  isometric equivalence, anti-multiplicative for `convolutionLp` at `p = 1`, and represented
  almost everywhere by `s ↦ (Measure.modularCharacter s : ℝ) • α s (star (f s⁻¹))` for any regular
  left-invariant measure (including `μ = 0`).

For the trivial action on `ℂ`, `convolutionLp` and `twistedInvolutionL1` specialize to
`MeasureTheory.Lp.convolutionL` and `star ∘ MeasureTheory.Lp.modularInversion`.

## References

* Dana P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs,
  vol. 134, American Mathematical Society (2007), Chapter 2 (§§2.3, 2.5).
* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §2.5.
* Bachir Bekka, Pierre de la Harpe, and Alain Valette, *Kazhdan's Property (T)*, New Mathematical
  Monographs, vol. 11, Cambridge University Press (2008), proof of Theorem G.3.1.
-/

public section

noncomputable section

open Filter Function MeasureTheory UniformSpace
open scoped ENNReal CompactlySupported

namespace TauCeti

namespace CStarAction

section Measurability

variable {G A : Type*} [Group G] [TopologicalSpace G] [R1Space G] [MeasurableSpace G]
  [BorelSpace G] [NonUnitalCStarAlgebra A] (α : CStarAction G A) {μ : Measure G}
  [μ.InnerRegularCompactLTTop]

/-- Evaluating a point-norm continuous C⋆-action along an a.e. finitely strongly measurable
coefficient function produces an a.e. strongly measurable function, without separability of `A` or
σ-finiteness of `μ`. -/
theorem aestronglyMeasurable_apply {f : G → A} (hf : AEFinStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun s => α s (f s)) μ :=
  hf.aestronglyMeasurable_apply_continuous α.continuous_orbit
    (fun s => (StarAlgEquiv.isometry (α s)).continuous) fun s => map_zero (α s)

end Measurability

section TranslateToLp

variable {G A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] (α : CStarAction G A) {μ : Measure G} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- On compactly supported continuous functions, `translateLp` agrees with `CStarAction.translate`.
-/
@[simp]
theorem translateLp_toLp [ContinuousMul G] [OpensMeasurableSpace G]
    [IsFiniteMeasureOnCompacts μ] (r : G) (f : C_c(G, A)) :
    α.translateLp μ p r (CompactlySupportedContinuousMap.toLp p μ ℂ f) =
      CompactlySupportedContinuousMap.toLp p μ ℂ (α.translate r f) := by
  refine Lp.ext ?_
  filter_upwards [α.coeFn_translateLp r (CompactlySupportedContinuousMap.toLp p μ ℂ f),
    (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
      (CompactlySupportedContinuousMap.coeFn_toLp (p := p) (μ := μ) ℂ f),
    CompactlySupportedContinuousMap.coeFn_toLp (p := p) (μ := μ) ℂ (α.translate r f)]
    with s h₁ h₂ h₃
  rw [h₁, h₂, h₃, translate_apply]

end TranslateToLp

namespace ConvolutionAlgebra

section CompletionEquiv

variable {G A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} {μ : Measure G}

/-- `ConvolutionAlgebra.toL1` realizes a compactly supported coefficient via
`CompactlySupportedContinuousMap.toLp`. -/
theorem toL1_eq_toLp [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
    (f : ConvolutionAlgebra α μ) :
    toL1 f = CompactlySupportedContinuousMap.toLp 1 μ ℂ f.ofConv :=
  Lp.ext ((coeFn_toL1 f).trans (CompactlySupportedContinuousMap.coeFn_toLp ℂ f.ofConv).symm)

@[simp]
theorem toL1_coefficientMul [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
    (a : A) (f : ConvolutionAlgebra α μ) :
    toL1 (coefficientMul a f) = (ContinuousLinearMap.mul ℂ A a).compLp (toL1 f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toL1 (coefficientMul a f),
    (ContinuousLinearMap.mul ℂ A a).coeFn_compLp (toL1 f), coeFn_toL1 f] with s h₁ h₂ h₃
  rw [h₁, ofConv_coefficientMul, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul,
    h₂, ContinuousLinearMap.mul_apply', h₃]

/-- `toL1FromCompletion` intertwines the completed coefficient multiplier
`(coefficientMul a).completion` with left multiplication by `a` on `Lp A 1 μ`, without requiring
local compactness or inner regularity. -/
@[simp]
theorem toL1FromCompletion_completion_coefficientMul [OpensMeasurableSpace G]
    [IsFiniteMeasureOnCompacts μ] (a : A) (x : Completion (ConvolutionAlgebra α μ)) :
    toL1FromCompletion α μ ((coefficientMul a).completion x) =
      (ContinuousLinearMap.mul ℂ A a).compLp (toL1FromCompletion α μ x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((toL1FromCompletion α μ).continuous.comp (coefficientMul a).completion.continuous)
      (((ContinuousLinearMap.mul ℂ A a).compLpL 1 μ).continuous.comp
        (toL1FromCompletion α μ).continuous)
  | ih f =>
    rw [ContinuousLinearMap.completion_apply_coe, toL1FromCompletion_coe, toL1FromCompletion_coe,
      toL1_coefficientMul]

@[simp]
theorem toL1_translateLIE [OpensMeasurableSpace G] [IsTopologicalGroup G] [MeasurableMul G]
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] (r : G) (f : ConvolutionAlgebra α μ) :
    toL1 (translateLIE r f) = α.translateLp μ 1 r (toL1 f) := by
  rw [toL1_eq_toLp, toL1_eq_toLp, ofConv_translateLIE, α.translateLp_toLp]

/-- `toL1FromCompletion` intertwines the completed twisted translation `(translateLIE r).completion`
with `CStarAction.translateLp`, without requiring local compactness or inner regularity. -/
theorem toL1FromCompletion_completion_translateLIE [OpensMeasurableSpace G]
    [IsTopologicalGroup G] [MeasurableMul G] [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (r : G) (x : Completion (ConvolutionAlgebra α μ)) :
    toL1FromCompletion α μ ((translateLIE r).completion x) =
      α.translateLp μ 1 r (toL1FromCompletion α μ x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((toL1FromCompletion α μ).continuous.comp (translateLIE r).completion.continuous)
      ((α.translateLp μ 1 r).continuous.comp (toL1FromCompletion α μ).continuous)
  | ih f =>
    rw [LinearIsometryEquiv.completion_apply_coe, toL1FromCompletion_coe, toL1FromCompletion_coe,
      toL1_translateLIE]

variable [R1Space G] [WeaklyLocallyCompactSpace G] [BorelSpace G]
  [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop]

/-- The compact-support convolution algebra has dense image in `Lp A 1 μ` for any measure finite
on compact sets and inner regular on sets of finite measure. -/
theorem denseRange_toL1 : DenseRange (toL1 (α := α) (μ := μ)) := by
  refine (CompactlySupportedContinuousMap.denseRange_toLp ENNReal.one_ne_top μ ℂ).mono ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨toConv f, toL1_eq_toLp (toConv f)⟩

theorem denseRange_toL1LI : DenseRange (toL1LI α μ) :=
  (funext toL1LI_apply : ⇑(toL1LI α μ) = ⇑(toL1 (α := α) (μ := μ))) ▸ denseRange_toL1

private theorem surjective_toL1FromCompletion :
    Function.Surjective (toL1FromCompletion α μ) := by
  have hcoe : ⇑(toL1FromCompletion α μ) = ⇑(toL1LI α μ).fromCompletion := funext fun x =>
    DFunLike.congr_fun ((toContinuousLinearMap_toL1FromCompletion (α := α) (μ := μ)).trans
      (toL1LI α μ).toContinuousLinearMap_fromCompletion.symm) x
  exact hcoe ▸ (toL1LI α μ).fromCompletion_surjective_of_denseRange denseRange_toL1LI

variable (α μ) in
/-- **Identification of the twisted `L¹` completion with Bochner `L¹`**: the canonical inclusion
`toL1` extends to a complex linear isometric equivalence between
`UniformSpace.Completion (ConvolutionAlgebra α μ)` and `Lp A 1 μ`. -/
def completionEquivL1 : Completion (ConvolutionAlgebra α μ) ≃ₗᵢ[ℂ] Lp A 1 μ :=
  LinearIsometryEquiv.ofSurjective (toL1FromCompletion α μ) surjective_toL1FromCompletion

/-- When `completionEquivL1` is defined, `toL1FromCompletion` agrees with it. -/
theorem toL1FromCompletion_eq_completionEquivL1 (x : Completion (ConvolutionAlgebra α μ)) :
    toL1FromCompletion α μ x = completionEquivL1 α μ x :=
  (congrFun (LinearIsometryEquiv.coe_ofSurjective (toL1FromCompletion α μ)
    surjective_toL1FromCompletion) x).symm

@[simp]
theorem completionEquivL1_coe (f : ConvolutionAlgebra α μ) :
    completionEquivL1 α μ f = toL1 f := by
  rw [← toL1FromCompletion_eq_completionEquivL1, toL1FromCompletion_coe]

@[simp]
theorem completionEquivL1_symm_toL1 (f : ConvolutionAlgebra α μ) :
    (completionEquivL1 α μ).symm (toL1 f) = f := by
  rw [← completionEquivL1_coe, LinearIsometryEquiv.symm_apply_apply]

@[simp]
theorem completionEquivL1_symm_toLp (f : C_c(G, A)) :
    (completionEquivL1 α μ).symm (CompactlySupportedContinuousMap.toLp 1 μ ℂ f) =
      ((toConv f : ConvolutionAlgebra α μ) : Completion (ConvolutionAlgebra α μ)) := by
  rw [← toL1_eq_toLp, completionEquivL1_symm_toL1]

variable (α) in
/-- Every class in `Lp A 1 μ` is the sum of an absolutely convergent series of compactly supported
convolution elements. -/
theorem exists_hasSum_toL1 (u : Lp A 1 μ) :
    ∃ φ : ℕ → ConvolutionAlgebra α μ,
      HasSum (fun n => toL1 (φ n)) u ∧ Summable fun n => ‖φ n‖ := by
  obtain ⟨φ, hφ_sum, hφ_norm, -⟩ :=
    Completion.exists_hasSum_coe_of_norm_lt ((completionEquivL1 α μ).symm u) (lt_add_one _)
  refine ⟨φ, ?_, hφ_norm⟩
  simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    completionEquivL1_coe, LinearIsometryEquiv.apply_symm_apply] using
    (completionEquivL1 α μ).toLinearIsometry.toContinuousLinearMap.hasSum hφ_sum

@[simp]
theorem completionEquivL1_completion_coefficientMul (a : A)
    (x : Completion (ConvolutionAlgebra α μ)) :
    completionEquivL1 α μ ((coefficientMul a).completion x) =
      (ContinuousLinearMap.mul ℂ A a).compLp (completionEquivL1 α μ x) := by
  simp only [← toL1FromCompletion_eq_completionEquivL1,
    toL1FromCompletion_completion_coefficientMul]

@[simp]
theorem completionEquivL1_symm_compLp_mul (a : A) (f : Lp A 1 μ) :
    (completionEquivL1 α μ).symm ((ContinuousLinearMap.mul ℂ A a).compLp f) =
      (coefficientMul a).completion ((completionEquivL1 α μ).symm f) := by
  apply (completionEquivL1 α μ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, completionEquivL1_completion_coefficientMul,
    LinearIsometryEquiv.apply_symm_apply]

end CompletionEquiv

section TranslateCompletion

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  {α : CStarAction G A} {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

theorem completionEquivL1_completion_translateLIE (r : G)
    (x : Completion (ConvolutionAlgebra α μ)) :
    completionEquivL1 α μ ((translateLIE r).completion x) =
      α.translateLp μ 1 r (completionEquivL1 α μ x) := by
  simp only [← toL1FromCompletion_eq_completionEquivL1, toL1FromCompletion_completion_translateLIE]

@[simp]
theorem completionEquivL1_symm_translateLp (r : G) (f : Lp A 1 μ) :
    (completionEquivL1 α μ).symm (α.translateLp μ 1 r f) =
      Completion.map (translateLIE r) ((completionEquivL1 α μ).symm f) := by
  apply (completionEquivL1 α μ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, ← LinearIsometryEquiv.coe_completion,
    completionEquivL1_completion_translateLIE, LinearIsometryEquiv.apply_symm_apply]

end TranslateCompletion

end ConvolutionAlgebra

section ConvolutionLp

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
private theorem norm_mul_compLp_translateLp_le (a : A) (y : G) (f : Lp A p μ) :
    ‖(ContinuousLinearMap.mul ℂ A a).compLp (α.translateLp μ p y f)‖ ≤ ‖a‖ * ‖f‖ :=
  calc
    ‖(ContinuousLinearMap.mul ℂ A a).compLp (α.translateLp μ p y f)‖
        ≤ ‖ContinuousLinearMap.mul ℂ A a‖ * ‖α.translateLp μ p y f‖ :=
      ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ ‖a‖ * ‖f‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_apply_le _ _ _)
        (norm_nonneg _)

/-- The integrand `y ↦ h y • α.translateLp μ p y f` of a twisted convolution is Bochner integrable
in `Lp A p μ` for `1 ≤ p < ∞`, with neither local compactness of `G`, separability of `A`, nor
σ-finiteness of `μ`. -/
theorem integrable_compLp_mul_translateLp (hp : p ≠ ∞) {h : G → A} (hh : Integrable h μ)
    (f : Lp A p μ) :
    Integrable (fun y => (ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f)) μ := by
  have hmeas : AEStronglyMeasurable
      (fun y => (ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f)) μ := by
    simpa only [Function.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compLpL₂_apply_apply] using
      hh.aefinStronglyMeasurable.aestronglyMeasurable_clm_apply
        ((((ContinuousLinearMap.mul ℂ A).compLpL₂ p μ).flip).continuous.comp
          (α.continuous_translateLp_apply hp f))
  exact (hh.norm.mul_const ‖f‖).mono' hmeas
    (.of_forall fun y => α.norm_mul_compLp_translateLp_le μ (h y) y f)

omit [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
private theorem norm_integral_mul_translateLp_le (h : Lp A 1 μ) (f : Lp A p μ) :
    ‖∫ y, (ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f) ∂μ‖ ≤ ‖h‖ * ‖f‖ := by
  rw [L1.norm_eq_integral_norm, ← integral_mul_const]
  exact norm_integral_le_of_norm_le ((L1.integrable_coeFn h).norm.mul_const _)
    (.of_forall fun y => α.norm_mul_compLp_translateLp_le μ (h y) y f)

variable (p) in
/-- **Twisted convolution** by an `L¹` coefficient kernel on `Lp A p μ` (`1 ≤ p < ∞`), defined as
the `Lp`-valued Bochner integral `h ⋆ f = ∫ y, h y • translateLp y f dμ(y)`. -/
def convolutionLp (hp : p ≠ ∞) : Lp A 1 μ →L[ℂ] Lp A p μ →L[ℂ] Lp A p μ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ
      (fun (h : Lp A 1 μ) (f : Lp A p μ) =>
        ∫ y, (ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f) ∂μ)
      (fun h₁ h₂ f => by
        rw [← integral_add (α.integrable_compLp_mul_translateLp μ hp (L1.integrable_coeFn h₁) f)
          (α.integrable_compLp_mul_translateLp μ hp (L1.integrable_coeFn h₂) f)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add h₁ h₂] with y hy
        rw [hy, Pi.add_apply, map_add, ContinuousLinearMap.add_compLp])
      (fun c h f => by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c h] with y hy
        rw [hy, Pi.smul_apply, map_smul, ContinuousLinearMap.smul_compLp])
      (fun h f₁ f₂ => by
        rw [← integral_add (α.integrable_compLp_mul_translateLp μ hp (L1.integrable_coeFn h) f₁)
          (α.integrable_compLp_mul_translateLp μ hp (L1.integrable_coeFn h) f₂)]
        refine integral_congr_ae (.of_forall fun y => ?_)
        simp only [map_add]
        exact map_add ((ContinuousLinearMap.mul ℂ A (h y)).compLpₗ p μ) _ _)
      (fun c h f => by
        rw [← integral_smul]
        refine integral_congr_ae (.of_forall fun y => ?_)
        simp only [map_smul]
        exact map_smul ((ContinuousLinearMap.mul ℂ A (h y)).compLpₗ p μ) c _))
    1 fun h f => by simpa using α.norm_integral_mul_translateLp_le μ h f

variable {α μ} {hp : p ≠ ∞}

/-- The defining `Lp`-valued Bochner integral for `convolutionLp`. -/
theorem convolutionLp_apply (h : Lp A 1 μ) (f : Lp A p μ) :
    α.convolutionLp μ p hp h f =
      ∫ y, (ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f) ∂μ :=
  (rfl)

/-- Twisted convolution of the `L¹` class of an integrable function `h` with `f`. -/
theorem convolutionLp_toL1 {h : G → A} (hh : Integrable h μ) (f : Lp A p μ) :
    α.convolutionLp μ p hp (hh.toL1 h) f =
      ∫ y, (ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f) ∂μ := by
  rw [convolutionLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [hh.coeFn_toL1] with y hy
  rw [hy]

/-- **Young's inequality** for twisted convolution: `‖h ⋆ f‖_p ≤ ‖h‖₁ * ‖f‖_p`. -/
theorem norm_convolutionLp_apply_le (h : Lp A 1 μ) (f : Lp A p μ) :
    ‖α.convolutionLp μ p hp h f‖ ≤ ‖h‖ * ‖f‖ :=
  α.norm_integral_mul_translateLp_le μ h f

/-- Twisted convolution has bilinear operator norm at most one, including zero algebras and the
zero measure. -/
theorem norm_convolutionLp_le : ‖α.convolutionLp μ p hp‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun h f => by
    simpa using α.norm_convolutionLp_apply_le h f

/-- On compactly supported continuous coefficient functions for `1 ≤ p < ∞`, `convolutionLp` is
represented almost everywhere by the pointwise twisted convolution integral
`s ↦ ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ`. -/
theorem convolutionLp_toLp_ae_eq (f g : C_c(G, A)) :
    α.convolutionLp μ p hp (CompactlySupportedContinuousMap.toLp 1 μ ℂ f)
        (CompactlySupportedContinuousMap.toLp p μ ℂ g) =ᵐ[μ]
      α.convolution μ f g := by
  set F : G → G → A := fun s r => f r * α r (g (r⁻¹ * s))
  have hFc : Continuous (uncurry F) :=
    (f.continuous.comp continuous_snd).mul
      (α.continuous_apply continuous_snd
        (g.continuous.comp (continuous_snd.inv.mul continuous_fst)))
  have hFsupp (s r : G) (hsr : F s r ≠ 0) : r ∈ tsupport f ∧ r⁻¹ * s ∈ tsupport g := by
    refine ⟨subset_tsupport _ (left_ne_zero_of_mul hsr), subset_tsupport _ fun hg0 => hsr ?_⟩
    simp [F, hg0]
  have hFs : HasCompactSupport (uncurry F) :=
    hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport hFsupp
  rw [α.convolutionLp_apply]
  refine (Lp.integral_ae_eq_integral_of_hasCompactSupport hp
    (α.integrable_compLp_mul_translateLp μ hp (L1.integrable_coeFn _) _)
    hFc hFs (((α.convolution μ f g).integrable (μ := μ)).congr
      (.of_forall (α.convolution_apply μ f g)))
    ?_).trans (.of_forall fun x => (α.convolution_apply μ f g x).symm)
  filter_upwards [CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ f] with r hr
  filter_upwards [(ContinuousLinearMap.mul ℂ A
        (CompactlySupportedContinuousMap.toLp 1 μ ℂ f r)).coeFn_compLp
      (α.translateLp μ p r (CompactlySupportedContinuousMap.toLp p μ ℂ g)),
    α.coeFn_translateLp r (CompactlySupportedContinuousMap.toLp p μ ℂ g),
    (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
      (CompactlySupportedContinuousMap.coeFn_toLp (p := p) (μ := μ) ℂ g)] with x h₁ h₂ h₃
  rw [h₁, ContinuousLinearMap.mul_apply', hr, h₂, h₃]

@[simp]
theorem convolutionLp_toLp (f g : C_c(G, A)) :
    α.convolutionLp μ p hp (CompactlySupportedContinuousMap.toLp 1 μ ℂ f)
        (CompactlySupportedContinuousMap.toLp p μ ℂ g) =
      CompactlySupportedContinuousMap.toLp p μ ℂ (α.convolution μ f g) :=
  Lp.ext ((α.convolutionLp_toLp_ae_eq f g).trans
    (CompactlySupportedContinuousMap.coeFn_toLp (p := p) ℂ (α.convolution μ f g)).symm)

/-- `ConvolutionAlgebra.toL1` turns the convolution product into `CStarAction.convolutionLp`
at `p = 1`. -/
@[simp]
theorem ConvolutionAlgebra.toL1_mul (f g : ConvolutionAlgebra α μ) :
    toL1 (f * g) = α.convolutionLp μ 1 ENNReal.one_ne_top (toL1 f) (toL1 g) := by
  rw [toL1_eq_toLp, toL1_eq_toLp, toL1_eq_toLp, ofConv_mul, α.convolutionLp_toLp]

/-- Left multiplication by `a ∈ A` commutes with twisted convolution in the first argument. -/
theorem mul_compLp_convolutionLp (a : A) (h : Lp A 1 μ) (f : Lp A p μ) :
    (ContinuousLinearMap.mul ℂ A a).compLp (α.convolutionLp μ p hp h f) =
      α.convolutionLp μ p hp ((ContinuousLinearMap.mul ℂ A a).compLp h) f := by
  let L : Lp A p μ →L[ℂ] Lp A p μ := (ContinuousLinearMap.mul ℂ A a).compLpL p μ
  have hcomm :=
    L.integral_comp_comm (α.integrable_compLp_mul_translateLp μ hp (L1.integrable_coeFn h) f)
  rw [← ContinuousLinearMap.compLpL_apply, convolutionLp_apply, ← hcomm, convolutionLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ A a).coeFn_compLp h] with y hy
  rw [ContinuousLinearMap.compLpL_apply, hy, ContinuousLinearMap.compLp_compLp]
  congr 1; ext b; simp [mul_assoc]

/-- Twisted left translation commutes with twisted convolution:
`translateLp g (h ⋆ f) = (translateLp g h) ⋆ f`. -/
theorem translateLp_convolutionLp (g : G) (h : Lp A 1 μ) (f : Lp A p μ) :
    α.translateLp μ p g (α.convolutionLp μ p hp h f) =
      α.convolutionLp μ p hp (α.translateLp μ 1 g h) f := by
  let L : Lp A p μ →L[ℂ] Lp A p μ :=
    (α.translateLp μ p g).toContinuousLinearEquiv.toContinuousLinearMap
  have hL (u : Lp A p μ) : L u = α.translateLp μ p g u := rfl
  have hcomm :=
    L.integral_comp_comm (α.integrable_compLp_mul_translateLp μ hp (L1.integrable_coeFn h) f)
  rw [← hL, convolutionLp_apply, ← hcomm, convolutionLp_apply, ← integral_mul_left_eq_self
    (fun y => (ContinuousLinearMap.mul ℂ A (α.translateLp μ 1 g h y)).compLp
      (α.translateLp μ p y f)) g]
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_mul_left μ g).quasiMeasurePreserving.ae
    (α.coeFn_translateLp g h)] with y hy
  rw [hL, hy, inv_mul_cancel_left, α.translateLp_compLp_mul, map_mul, LinearIsometryEquiv.coe_mul,
    Function.comp_apply]

/-- **Associativity of twisted convolution**: `(h ⋆ k) ⋆ f = h ⋆ (k ⋆ f)`. -/
theorem convolutionLp_assoc (h k : Lp A 1 μ) (f : Lp A p μ) :
    α.convolutionLp μ p hp (α.convolutionLp μ 1 ENNReal.one_ne_top h k) f =
      α.convolutionLp μ p hp h (α.convolutionLp μ p hp k f) := by
  have hint := ((α.convolutionLp μ p hp).flip f).integral_comp_comm
    (α.integrable_compLp_mul_translateLp μ ENNReal.one_ne_top (L1.integrable_coeFn h) k)
  simp only [ContinuousLinearMap.flip_apply, ← α.mul_compLp_convolutionLp,
    ← α.translateLp_convolutionLp] at hint
  rw [α.convolutionLp_apply (hp := ENNReal.one_ne_top) h k, ← hint]
  exact (α.convolutionLp_apply h _).symm

/-- For the trivial action on `ℂ`, `convolutionLp` agrees with `MeasureTheory.Lp.convolutionL`. -/
@[simp]
theorem convolutionLp_trivial :
    (trivial (G := G) (A := ℂ)).convolutionLp μ p hp = Lp.convolutionL μ p hp := by
  ext h f : 2
  rw [convolutionLp_apply, Lp.convolutionL_apply]
  refine integral_congr_ae (.of_forall fun y => ?_)
  dsimp only
  rw [translateLp_trivial]
  refine Lp.ext ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ (h y)).coeFn_compLp (Lp.leftTranslation μ p ℂ y f),
    Lp.coeFn_smul (h y) (Lp.leftTranslation μ p ℂ y f)] with s h₁ h₂
  simp [h₁, h₂]

end ConvolutionLp

section FromCompletionMul

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  {α : CStarAction G A} {μ : Measure G} [μ.IsMulLeftInvariant]
  [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- `toL1FromCompletion` intertwines the completion's multiplication with `convolutionLp`
at `p = 1`. -/
@[simp]
theorem ConvolutionAlgebra.toL1FromCompletion_mul (x y : Completion (ConvolutionAlgebra α μ)) :
    toL1FromCompletion α μ (x * y) =
      α.convolutionLp μ 1 ENNReal.one_ne_top
        (toL1FromCompletion α μ x) (toL1FromCompletion α μ y) := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f g => simp only [← Completion.coe_mul', toL1FromCompletion_coe, toL1_mul]

end FromCompletionMul

section CompletionMul

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  {α : CStarAction G A} {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

/-- `completionEquivL1` intertwines multiplication in the abstract `L¹` completion with
`CStarAction.convolutionLp` at `p = 1`. -/
@[simp]
theorem ConvolutionAlgebra.completionEquivL1_mul
    (x y : Completion (ConvolutionAlgebra α μ)) :
    completionEquivL1 α μ (x * y) =
      α.convolutionLp μ 1 ENNReal.one_ne_top
        (completionEquivL1 α μ x) (completionEquivL1 α μ y) := by
  simp only [← toL1FromCompletion_eq_completionEquivL1, toL1FromCompletion_mul]

@[simp]
theorem ConvolutionAlgebra.completionEquivL1_symm_convolutionLp (f g : Lp A 1 μ) :
    (completionEquivL1 α μ).symm (α.convolutionLp μ 1 ENNReal.one_ne_top f g) =
      (completionEquivL1 α μ).symm f * (completionEquivL1 α μ).symm g := by
  apply (completionEquivL1 α μ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, completionEquivL1_mul,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

end CompletionMul

section InvolutionL1

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
  [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

/-- **Twisted `L¹` involution** on `Lp A 1 μ`, transported from the isometric `⋆`-operation on
`Completion (ConvolutionAlgebra α μ)` across `completionEquivL1`. -/
def twistedInvolutionL1 : Lp A 1 μ ≃ₗᵢ⋆[ℂ] Lp A 1 μ :=
  ((ConvolutionAlgebra.completionEquivL1 α μ).symm.trans (starₗᵢ ℂ)).trans
    (ConvolutionAlgebra.completionEquivL1 α μ)

variable {μ}

section
variable {α}

@[simp]
theorem ConvolutionAlgebra.completionEquivL1_star (x : Completion (ConvolutionAlgebra α μ)) :
    completionEquivL1 α μ (star x) = α.twistedInvolutionL1 μ (completionEquivL1 α μ x) := by
  simp only [twistedInvolutionL1, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, starₗᵢ_apply]

@[simp]
theorem ConvolutionAlgebra.completionEquivL1_symm_twistedInvolutionL1 (f : Lp A 1 μ) :
    (completionEquivL1 α μ).symm (α.twistedInvolutionL1 μ f) =
      star ((completionEquivL1 α μ).symm f) := by
  simp only [twistedInvolutionL1, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, starₗᵢ_apply]

@[simp]
theorem ConvolutionAlgebra.toL1_star (f : ConvolutionAlgebra α μ) :
    toL1 (star f) = α.twistedInvolutionL1 μ (toL1 f) := by
  rw [← completionEquivL1_coe, Completion.coe_star, completionEquivL1_star, completionEquivL1_coe]

end

@[simp]
theorem twistedInvolutionL1_toLp (f : C_c(G, A)) :
    α.twistedInvolutionL1 μ (CompactlySupportedContinuousMap.toLp 1 μ ℂ f) =
      CompactlySupportedContinuousMap.toLp 1 μ ℂ (α.twistedInvolution f) := by
  simpa only [ConvolutionAlgebra.toL1_eq_toLp, ConvolutionAlgebra.ofConv_toConv,
    ConvolutionAlgebra.ofConv_star] using
    (ConvolutionAlgebra.toL1_star (α := α) (μ := μ) (ConvolutionAlgebra.toConv f)).symm

@[simp]
theorem twistedInvolutionL1_twistedInvolutionL1 (f : Lp A 1 μ) :
    α.twistedInvolutionL1 μ (α.twistedInvolutionL1 μ f) = f := by
  simp only [twistedInvolutionL1, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, starₗᵢ_apply, star_star,
    LinearIsometryEquiv.apply_symm_apply]

@[simp]
theorem twistedInvolutionL1_symm :
    (α.twistedInvolutionL1 μ).symm = α.twistedInvolutionL1 μ :=
  LinearIsometryEquiv.ext fun f =>
    (LinearIsometryEquiv.symm_apply_eq _).2 (α.twistedInvolutionL1_twistedInvolutionL1 f).symm

/-- The twisted `L¹` involution reverses twisted `L¹` convolution. -/
theorem twistedInvolutionL1_convolutionLp (f g : Lp A 1 μ) :
    α.twistedInvolutionL1 μ (α.convolutionLp μ 1 ENNReal.one_ne_top f g) =
      α.convolutionLp μ 1 ENNReal.one_ne_top
        (α.twistedInvolutionL1 μ g) (α.twistedInvolutionL1 μ f) := by
  apply (ConvolutionAlgebra.completionEquivL1 α μ).symm.injective
  simp only [ConvolutionAlgebra.completionEquivL1_symm_twistedInvolutionL1,
    ConvolutionAlgebra.completionEquivL1_symm_convolutionLp]
  exact star_mul ((ConvolutionAlgebra.completionEquivL1 α μ).symm f)
    ((ConvolutionAlgebra.completionEquivL1 α μ).symm g)

end InvolutionL1

section ActionPointwise

variable {G A : Type*} [Group G] [TopologicalSpace G] [R1Space G] [MeasurableSpace G]
  [BorelSpace G] [NonUnitalCStarAlgebra A] (α : CStarAction G A)

private theorem integrable_action_apply {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) : Integrable (fun s => α s (u s)) μ :=
  (L1.integrable_coeFn u).mono
    (α.aestronglyMeasurable_apply (L1.integrable_coeFn u).aefinStronglyMeasurable)
    (.of_forall fun s => (StarAlgEquiv.norm_map (α s) (u s)).le)

private def actionPointwiseL1 {μ : Measure G} [μ.InnerRegularCompactLTTop] :
    Lp A 1 μ →ₗᵢ[ℂ] Lp A 1 μ where
  toFun u := (α.integrable_action_apply u).toL1 _
  map_add' u v := by
    refine Lp.ext ?_
    filter_upwards [(α.integrable_action_apply (u + v)).coeFn_toL1,
      Lp.coeFn_add ((α.integrable_action_apply u).toL1 _)
        ((α.integrable_action_apply v).toL1 _),
      (α.integrable_action_apply u).coeFn_toL1,
      (α.integrable_action_apply v).coeFn_toL1,
      Lp.coeFn_add u v] with s h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₂, Pi.add_apply, h₃, h₄, h₅, Pi.add_apply, map_add]
  map_smul' c u := by
    simp only [RingHom.id_apply]
    refine Lp.ext ?_
    filter_upwards [(α.integrable_action_apply (c • u)).coeFn_toL1,
      Lp.coeFn_smul c ((α.integrable_action_apply u).toL1 _),
      (α.integrable_action_apply u).coeFn_toL1,
      Lp.coeFn_smul c u] with s h₁ h₂ h₃ h₄
    rw [h₁, h₂, Pi.smul_apply, h₃, h₄, Pi.smul_apply, map_smul]
  norm_map' u := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [(α.integrable_action_apply u).coeFn_toL1] with s hs
    rw [hs, StarAlgEquiv.norm_map]

private theorem coeFn_actionPointwiseL1 {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) :
    α.actionPointwiseL1 u =ᵐ[μ] fun s => α s (u s) :=
  (α.integrable_action_apply u).coeFn_toL1

end ActionPointwise

section RegularLeftInvariant

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) {μ : Measure G} [μ.Regular]

private theorem twistedInvolutionL1_eq_actionPointwiseL1 [μ.IsHaarMeasure] (f : Lp A 1 μ) :
    α.twistedInvolutionL1 μ f = α.actionPointwiseL1 (star (Lp.modularInversion μ 1 ℝ f)) := by
  have hc₁ : Continuous (α.twistedInvolutionL1 μ) := (α.twistedInvolutionL1 μ).continuous
  have hc₂ : Continuous fun u : Lp A 1 μ =>
      α.actionPointwiseL1 (star (Lp.modularInversion μ 1 ℝ u)) :=
    α.actionPointwiseL1.continuous.comp
      (continuous_star.comp (Lp.modularInversion μ 1 ℝ).continuous)
  refine congrFun ((ConvolutionAlgebra.denseRange_toL1 (α := α) (μ := μ)).equalizer hc₁ hc₂ ?_) f
  ext g : 1
  simp only [Function.comp_apply, ← ConvolutionAlgebra.toL1_star]
  refine Lp.ext ?_
  filter_upwards [ConvolutionAlgebra.coeFn_toL1 (star g),
    α.coeFn_actionPointwiseL1 (star (Lp.modularInversion μ 1 ℝ (ConvolutionAlgebra.toL1 g))),
    Lp.coeFn_star (Lp.modularInversion μ 1 ℝ (ConvolutionAlgebra.toL1 g)),
    Lp.coeFn_modularInversion (𝕜 := ℝ) (ConvolutionAlgebra.toL1 g),
    (Measure.quasiMeasurePreserving_inv_of_regular μ).ae (ConvolutionAlgebra.coeFn_toL1 g)]
    with s h₁ h₂ h₃ h₄ h₅
  rw [h₁, ConvolutionAlgebra.ofConv_star, twistedInvolution_apply, h₂, h₃, Pi.star_apply, h₄, h₅]
  simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, star_smul, star_trivial]
  rw [← map_smul, Complex.coe_smul]

/-- For a regular left-invariant measure (`μ = 0` included), the twisted `L¹` involution is
represented almost everywhere by `s ↦ (Measure.modularCharacter s : ℝ) • α s (star (f s⁻¹))`. -/
theorem coeFn_twistedInvolutionL1 [μ.IsMulLeftInvariant] (f : Lp A 1 μ) :
    α.twistedInvolutionL1 μ f =ᵐ[μ]
      fun s => (Measure.modularCharacter s : ℝ) • α s (star (f s⁻¹)) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp [Filter.EventuallyEq]
  · have : μ.IsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_regular
    have : μ.IsHaarMeasure := ⟨⟩
    rw [α.twistedInvolutionL1_eq_actionPointwiseL1 f]
    filter_upwards [α.coeFn_actionPointwiseL1 (star (Lp.modularInversion μ 1 ℝ f)),
      Lp.coeFn_star (Lp.modularInversion μ 1 ℝ f),
      Lp.coeFn_modularInversion (𝕜 := ℝ) f] with s h₁ h₂ h₃
    rw [h₁, h₂, Pi.star_apply, h₃]
    simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, star_smul, star_trivial]
    rw [← Complex.coe_smul, map_smul, Complex.coe_smul]

/-- For the trivial action and a regular Haar measure, `twistedInvolutionL1` is pointwise `star`
composed with `MeasureTheory.Lp.modularInversion`. -/
@[simp]
theorem twistedInvolutionL1_trivial [μ.IsHaarMeasure] (f : Lp A 1 μ) :
    (trivial (G := G) (A := A)).twistedInvolutionL1 μ f =
      star (Lp.modularInversion μ 1 ℂ f) := by
  refine Lp.ext ?_
  filter_upwards [(trivial (G := G) (A := A)).coeFn_twistedInvolutionL1 f,
    Lp.coeFn_star (Lp.modularInversion μ 1 ℂ f),
    Lp.coeFn_modularInversion (𝕜 := ℂ) f] with s h₁ h₂ h₃
  rw [h₁, trivial_apply, h₂, Pi.star_apply, h₃]
  simp [ENNReal.toReal_one, star_smul]

end RegularLeftInvariant

end CStarAction

end TauCeti
