/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Multiplier
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
public import TauCeti.MeasureTheory.Function.Lp.LocallyCompact
public import TauCeti.MeasureTheory.Function.Lp.Star
public import TauCeti.Topology.Algebra.UniformRing
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular
import TauCeti.MeasureTheory.Group.Convolution.Support
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Realizing the twisted `L¹` Banach ⋆-algebra in Bochner `L¹`

Let `α : CStarAction G A` be a point-norm continuous action of a topological group `G` on a
possibly nonunital complex C⋆-algebra `A`. In
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed`, the compact-support convolution algebra
`CStarAction.ConvolutionAlgebra α μ` carries the `L¹` seminorm pulled back along
`ConvolutionAlgebra.toL1 : ConvolutionAlgebra α μ →ₗ[ℂ] Lp A 1 μ`, and its abstract completion
`UniformSpace.Completion (ConvolutionAlgebra α μ)` is the twisted `L¹` Banach ⋆-algebra.

When `G` is locally compact and `μ` is finite on compact sets and inner regular on sets of finite
measure (`IsFiniteMeasureOnCompacts μ` and `μ.InnerRegularCompactLTTop`), compactly supported
continuous functions are dense in `Lp A 1 μ`. Consequently `toL1` has dense range and extends to a
linear isometric equivalence
`ConvolutionAlgebra.completionEquivL1 α μ : Completion (ConvolutionAlgebra α μ) ≃ₗᵢ[ℂ] Lp A 1 μ`.
This holds without separability of `A`, second countability of `G`, σ-finiteness of `μ`, unitality
of `A`, or full support of `μ`, including zero algebras and the zero measure.

On `Lp A 1 μ` itself we construct the concrete dynamical operations and show that they match those
of `Completion (ConvolutionAlgebra α μ)` across `completionEquivL1`:

* `CStarAction.translateLp`: twisted left translation `(r • f)(s) = α r (f (r⁻¹ * s))` on
  `Lp A p μ`, jointly continuous on `G × Lp A 1 μ`.
* `CStarAction.convolutionL1`: twisted convolution on `Lp A 1 μ`, defined without countability or
  σ-finiteness hypotheses as the `Lp A 1 μ`-valued Bochner integral
  `f ⋆_α g = ∫ r, (ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g) ∂μ`. On
  compactly supported continuous coefficients it is represented almost everywhere by the pointwise
  twisted convolution integral, so `completionEquivL1` intertwines multiplication in the completion
  with `convolutionL1`.
* `CStarAction.twistedInvolutionL1`: the twisted involution on `Lp A 1 μ` as a conjugate-linear
  isometric equivalence, anti-multiplicative for `convolutionL1`, and represented almost everywhere
  by `s ↦ (Measure.modularCharacter s : ℝ) • α s (star (f s⁻¹))` for a regular Haar measure.

For the trivial action on `ℂ`, `convolutionL1` and `twistedInvolutionL1` specialize to the scalar
group convolution `MeasureTheory.Lp.convolutionL` and `star ∘ MeasureTheory.Lp.modularInversion`.

## References

* Dana P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs,
  vol. 134, American Mathematical Society (2007), Chapter 2 (§§2.3, 2.5).
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

section TranslateLp

variable {G A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] (α : CStarAction G A) (μ : Measure G) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Postcomposition on `Lp A p μ` with the isometric automorphism `α r`. -/
private def compActionLp (r : G) : Lp A p μ ≃ₗᵢ[ℂ] Lp A p μ :=
  have hle (t : G) (v : Lp A p μ) : ‖(α.toContinuousLinearMap t).compLp v‖ ≤ ‖v‖ := by
    have hnorm : ‖α.toContinuousLinearMap t‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
        simp [StarAlgEquiv.norm_map]
    exact ((α.toContinuousLinearMap t).norm_compLp_le v).trans
      (mul_le_of_le_one_left (norm_nonneg v) hnorm)
  have hinv (t : G) (u : Lp A p μ) :
      (α.toContinuousLinearMap t⁻¹).compLp ((α.toContinuousLinearMap t).compLp u) = u := by
    refine Lp.ext ?_
    filter_upwards [(α.toContinuousLinearMap t⁻¹).coeFn_compLp
        ((α.toContinuousLinearMap t).compLp u),
      (α.toContinuousLinearMap t).coeFn_compLp u] with s hs₁ hs₂
    rw [hs₁, hs₂, toContinuousLinearMap_apply, toContinuousLinearMap_apply, inv_apply_apply]
  { toLinearEquiv :=
      LinearEquiv.ofLinearMap ((α.toContinuousLinearMap r).compLpₗ p μ)
        ((α.toContinuousLinearMap r⁻¹).compLpₗ p μ)
        (LinearMap.ext fun u => by simpa using hinv r⁻¹ u)
        (LinearMap.ext (hinv r))
    norm_map' := fun u => by
      simp only [LinearEquiv.coe_ofLinearMap, ContinuousLinearMap.compLpₗ_apply]
      refine le_antisymm (hle r u) ?_
      have h := hle r⁻¹ ((α.toContinuousLinearMap r).compLp u)
      rwa [hinv r u] at h }

private theorem coeFn_compActionLp (r : G) (u : Lp A p μ) :
    α.compActionLp μ p r u =ᵐ[μ] fun s => α r (u s) := by
  filter_upwards [(α.toContinuousLinearMap r).coeFn_compLp u] with s hs
  exact hs.trans (α.toContinuousLinearMap_apply r (u s))

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Twisted left translation `(r • f)(s) = α r (f (r⁻¹ * s))` on `Lp A p μ` for a left-invariant
measure `μ`, bundled as a group homomorphism into linear isometric equivalences. -/
def translateLp : G →* (Lp A p μ ≃ₗᵢ[ℂ] Lp A p μ) where
  toFun r := (Lp.leftTranslation μ p ℂ r).trans (α.compActionLp μ p r)
  map_one' := by
    ext f : 1
    refine Lp.ext ?_
    filter_upwards [α.coeFn_compActionLp μ p 1 (Lp.leftTranslation μ p ℂ 1 f),
      Lp.coeFn_leftTranslation (𝕜 := ℂ) 1 f] with s hs₁ hs₂
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.coe_one, id_eq]
    rw [hs₁, hs₂, inv_one, one_mul, one_apply]
  map_mul' r t := by
    ext f : 1
    refine Lp.ext ?_
    filter_upwards [α.coeFn_compActionLp μ p (r * t) (Lp.leftTranslation μ p ℂ (r * t) f),
      Lp.coeFn_leftTranslation (𝕜 := ℂ) (r * t) f,
      α.coeFn_compActionLp μ p r
        (Lp.leftTranslation μ p ℂ r (α.compActionLp μ p t (Lp.leftTranslation μ p ℂ t f))),
      Lp.coeFn_leftTranslation (𝕜 := ℂ) r
        (α.compActionLp μ p t (Lp.leftTranslation μ p ℂ t f)),
      (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
        (α.coeFn_compActionLp μ p t (Lp.leftTranslation μ p ℂ t f)),
      (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
        (Lp.coeFn_leftTranslation (𝕜 := ℂ) t f)] with s h₁ h₂ h₃ h₄ h₅ h₆
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.coe_mul, Function.comp_apply]
    have h₅' : (α.compActionLp μ p t (Lp.leftTranslation μ p ℂ t f) : G → A) (r⁻¹ * s) =
        α t ((Lp.leftTranslation μ p ℂ t f : G → A) (r⁻¹ * s)) := h₅
    have h₆' : (Lp.leftTranslation μ p ℂ t f : G → A) (r⁻¹ * s) = f (t⁻¹ * (r⁻¹ * s)) := h₆
    rw [h₁, h₂, h₃, h₄, h₅', h₆', mul_inv_rev, mul_assoc, α.mul_apply]

variable {μ p}

/-- Twisted left translation on `Lp A p μ` is almost everywhere `s ↦ α r (f (r⁻¹ * s))`. -/
theorem coeFn_translateLp (r : G) (f : Lp A p μ) :
    α.translateLp μ p r f =ᵐ[μ] fun s => α r (f (r⁻¹ * s)) := by
  filter_upwards [α.coeFn_compActionLp μ p r (Lp.leftTranslation μ p ℂ r f),
    Lp.coeFn_leftTranslation (𝕜 := ℂ) r f] with s hs₁ hs₂
  exact hs₁.trans (congrArg (α r) hs₂)

@[simp]
theorem translateLp_symm (r : G) :
    (α.translateLp μ p r).symm = α.translateLp μ p r⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- For the trivial action, twisted left translation on `Lp A p μ` is ordinary left translation. -/
@[simp]
theorem trivial_translateLp (r : G) :
    (trivial (G := G) (A := A)).translateLp μ p r = Lp.leftTranslation μ p ℂ r := by
  ext f : 1
  refine Lp.ext ?_
  filter_upwards [(trivial (G := G) (A := A)).coeFn_translateLp r f,
    Lp.coeFn_leftTranslation (𝕜 := ℂ) r f] with s hs₁ hs₂
  rw [hs₁, trivial_apply, hs₂]

/-- Twisted left translation commutes with left multiplication by coefficients up to the action
twist. -/
theorem translateLp_compLp_mul (r : G) (a : A) (f : Lp A p μ) :
    α.translateLp μ p r ((ContinuousLinearMap.mul ℂ A a).compLp f) =
      (ContinuousLinearMap.mul ℂ A (α r a)).compLp (α.translateLp μ p r f) := by
  refine Lp.ext ?_
  filter_upwards [α.coeFn_translateLp r ((ContinuousLinearMap.mul ℂ A a).compLp f),
    (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
      ((ContinuousLinearMap.mul ℂ A a).coeFn_compLp f),
    (ContinuousLinearMap.mul ℂ A (α r a)).coeFn_compLp (α.translateLp μ p r f),
    α.coeFn_translateLp r f] with s h₁ h₂ h₃ h₄
  have h₂' : ((ContinuousLinearMap.mul ℂ A a).compLp f : G → A) (r⁻¹ * s) = a * f (r⁻¹ * s) := h₂
  rw [h₁, h₂', map_mul, h₃, ContinuousLinearMap.mul_apply', h₄]

/-- On compactly supported continuous functions, `translateLp` agrees with `CStarAction.translate`.
-/
@[simp]
theorem translateLp_toLp [IsTopologicalGroup G] [OpensMeasurableSpace G]
    [IsFiniteMeasureOnCompacts μ] (r : G) (f : C_c(G, A)) :
    α.translateLp μ p r (CompactlySupportedContinuousMap.toLp p μ ℂ f) =
      CompactlySupportedContinuousMap.toLp p μ ℂ (α.translate r f) := by
  refine Lp.ext ?_
  filter_upwards [α.coeFn_translateLp r (CompactlySupportedContinuousMap.toLp p μ ℂ f),
    (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
      (CompactlySupportedContinuousMap.coeFn_toLp (p := p) (μ := μ) ℂ f),
    CompactlySupportedContinuousMap.coeFn_toLp (p := p) (μ := μ) ℂ (α.translate r f)]
    with s h₁ h₂ h₃
  have h₂' : (CompactlySupportedContinuousMap.toLp p μ ℂ f : G → A) (r⁻¹ * s) = f (r⁻¹ * s) := h₂
  rw [h₁, h₂', h₃, translate_apply]

end TranslateLp

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

@[simp]
theorem toL1_translateLIE [OpensMeasurableSpace G] [IsTopologicalGroup G] [MeasurableMul G]
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] (r : G) (f : ConvolutionAlgebra α μ) :
    toL1 (translateLIE r f) = α.translateLp μ 1 r (toL1 f) := by
  rw [toL1_eq_toLp, toL1_eq_toLp, ofConv_translateLIE, α.translateLp_toLp]

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

variable (α μ) in
/-- **Identification of the twisted `L¹` completion with Bochner `L¹`**: the canonical inclusion
`toL1` extends to a complex linear isometric equivalence between
`UniformSpace.Completion (ConvolutionAlgebra α μ)` and `Lp A 1 μ`. -/
def completionEquivL1 : Completion (ConvolutionAlgebra α μ) ≃ₗᵢ[ℂ] Lp A 1 μ :=
  (LinearEquiv.refl ℂ (ConvolutionAlgebra α μ)).extendOfIsometry
    Completion.toComplₗᵢ.toLinearMap (toL1 (α := α) (μ := μ))
    Completion.denseRange_coe denseRange_toL1 fun f => by
      simp [← toL1LI_apply]

@[simp]
theorem completionEquivL1_coe (f : ConvolutionAlgebra α μ) :
    completionEquivL1 α μ f = toL1 f :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

@[simp]
theorem completionEquivL1_symm_toL1 (f : ConvolutionAlgebra α μ) :
    (completionEquivL1 α μ).symm (toL1 f) = f :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ f

end CompletionEquiv

end ConvolutionAlgebra

section ConvolutionL1

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

/-- Twisted left translation on `Lp A 1 μ` is jointly continuous on `G × Lp A 1 μ`. -/
@[fun_prop]
theorem continuous_translateLp :
    Continuous fun q : G × Lp A 1 μ => α.translateLp μ 1 q.1 q.2 := by
  refine continuous_prod_of_dense_continuous_lipschitzWith' _ 1
    (ConvolutionAlgebra.denseRange_toL1 (α := α) (μ := μ))
    (fun r => (α.translateLp μ 1 r).isometry.lipschitzWith) ?_
  rintro _ ⟨f, rfl⟩
  have h : (fun r => α.translateLp μ 1 r (ConvolutionAlgebra.toL1 f)) =
      fun r => ConvolutionAlgebra.toL1LI α μ (ConvolutionAlgebra.translateLIE r f) := by
    ext r : 1
    simp
  rw [h]
  exact (ConvolutionAlgebra.toL1LI α μ).continuous.comp
    (ConvolutionAlgebra.continuous_translateLIE f)

/-- Every orbit of twisted left translation in `Lp A 1 μ` is norm-continuous. -/
@[fun_prop]
theorem continuous_translateLp_apply (f : Lp A 1 μ) :
    Continuous fun r : G => α.translateLp μ 1 r f :=
  α.continuous_translateLp.comp (continuous_id.prodMk continuous_const)

variable {α} in
theorem ConvolutionAlgebra.completionEquivL1_translate (r : G)
    (x : Completion (ConvolutionAlgebra α μ)) :
    completionEquivL1 α μ ((translateLIE r).completion x) =
      α.translateLp μ 1 r (completionEquivL1 α μ x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((completionEquivL1 α μ).continuous.comp (translateLIE r).completion.continuous)
      ((α.translateLp μ 1 r).continuous.comp (completionEquivL1 α μ).continuous)
  | ih f =>
    rw [LinearIsometryEquiv.completion_apply_coe, completionEquivL1_coe, completionEquivL1_coe,
      toL1_translateLIE]

variable {α} in
@[simp]
theorem ConvolutionAlgebra.completionEquivL1_map_translateLIE (r : G)
    (x : Completion (ConvolutionAlgebra α μ)) :
    completionEquivL1 α μ (Completion.map (translateLIE r) x) =
      α.translateLp μ 1 r (completionEquivL1 α μ x) := by
  simpa only [LinearIsometryEquiv.coe_completion] using
    completionEquivL1_translate (α := α) r x

/-- The `Lp A 1 μ`-valued integrand `r ↦ (f r) • (r • g)` of a twisted convolution is Bochner
integrable, with neither separability of `A` nor σ-finiteness of `μ`. -/
theorem integrable_mul_translateLp {f : G → A} (hf : Integrable f μ) (g : Lp A 1 μ) :
    Integrable (fun r => (ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g)) μ := by
  let B : Lp A 1 μ →L[ℂ] A →L[ℂ] Lp A 1 μ := ((ContinuousLinearMap.mul ℂ A).compLpL₂ 1 μ).flip
  have hmeas : AEStronglyMeasurable
      (fun r => B (α.translateLp μ 1 r g) (f r)) μ :=
    hf.aefinStronglyMeasurable.aestronglyMeasurable_clm_apply
      (B.continuous.comp (α.continuous_translateLp_apply g))
  refine (hf.norm.mul_const ‖g‖).mono' hmeas (.of_forall fun r => ?_)
  calc
    ‖(ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g)‖ ≤
        ‖ContinuousLinearMap.mul ℂ A (f r)‖ * ‖α.translateLp μ 1 r g‖ :=
      ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ ‖f r‖ * ‖g‖ := by
      rw [LinearIsometryEquiv.norm_map]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg g)
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun b => norm_mul_le _ _

omit [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] in
private theorem norm_integral_mul_translateLp_le (f g : Lp A 1 μ) :
    ‖∫ r, (ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g) ∂μ‖ ≤ ‖f‖ * ‖g‖ := by
  rw [L1.norm_eq_integral_norm f, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.mul_const _)
    (.of_forall fun r => ?_)
  calc
    ‖(ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g)‖ ≤
        ‖ContinuousLinearMap.mul ℂ A (f r)‖ * ‖α.translateLp μ 1 r g‖ :=
      ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ ‖f r‖ * ‖g‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun b => norm_mul_le _ _)
        (norm_nonneg g)

variable (μ) in
/-- **Twisted `L¹` convolution** for a C⋆-dynamical system, defined as the continuous bilinear map
`Lp A 1 μ →L[ℂ] Lp A 1 μ →L[ℂ] Lp A 1 μ` sending `(f, g)` to the `Lp A 1 μ`-valued Bochner integral
`∫ r, (f r) • (α.translateLp μ 1 r g) ∂μ`. -/
def convolutionL1 : Lp A 1 μ →L[ℂ] Lp A 1 μ →L[ℂ] Lp A 1 μ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ
      (fun (f g : Lp A 1 μ) =>
        ∫ r, (ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g) ∂μ)
      (fun f₁ f₂ g => by
        rw [← integral_add (α.integrable_mul_translateLp (L1.integrable_coeFn f₁) g)
          (α.integrable_mul_translateLp (L1.integrable_coeFn f₂) g)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f₁ f₂] with r hr
        rw [hr, Pi.add_apply, map_add, ContinuousLinearMap.add_compLp])
      (fun c f g => by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with r hr
        rw [hr, Pi.smul_apply, map_smul, ContinuousLinearMap.smul_compLp])
      (fun f g₁ g₂ => by
        rw [← integral_add (α.integrable_mul_translateLp (L1.integrable_coeFn f) g₁)
          (α.integrable_mul_translateLp (L1.integrable_coeFn f) g₂)]
        refine integral_congr_ae (.of_forall fun r => ?_)
        dsimp only
        rw [map_add, ← ContinuousLinearMap.compLpL₂_apply_apply (p := 1) (μ := μ), map_add,
          ContinuousLinearMap.compLpL₂_apply_apply, ContinuousLinearMap.compLpL₂_apply_apply])
      (fun c f g => by
        rw [← integral_smul]
        refine integral_congr_ae (.of_forall fun r => ?_)
        dsimp only
        rw [map_smul, ← ContinuousLinearMap.compLpL₂_apply_apply (p := 1) (μ := μ), map_smul,
          ContinuousLinearMap.compLpL₂_apply_apply]))
    1 fun f g => by simpa using α.norm_integral_mul_translateLp_le f g

/-- The defining `Lp A 1 μ`-valued Bochner integral for twisted `L¹` convolution. -/
theorem convolutionL1_apply (f g : Lp A 1 μ) :
    α.convolutionL1 μ f g =
      ∫ r, (ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g) ∂μ :=
  (rfl)

/-- Twisted `L¹` convolution of the `L¹` class of an integrable function `f` with `g`. -/
theorem convolutionL1_integrable_toL1 {f : G → A} (hf : Integrable f μ) (g : Lp A 1 μ) :
    α.convolutionL1 μ (hf.toL1 f) g =
      ∫ r, (ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g) ∂μ := by
  rw [convolutionL1_apply]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL1] with r hr
  rw [hr]

/-- **Submultiplicativity of twisted `L¹` convolution**: `‖f ⋆_α g‖₁ ≤ ‖f‖₁ * ‖g‖₁`. -/
theorem norm_convolutionL1_apply_le (f g : Lp A 1 μ) :
    ‖α.convolutionL1 μ f g‖ ≤ ‖f‖ * ‖g‖ :=
  α.norm_integral_mul_translateLp_le f g

/-- Twisted `L¹` convolution has operator norm at most `1` as a bilinear map, including zero
algebras and the zero measure. -/
theorem norm_convolutionL1_le : ‖α.convolutionL1 μ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun f g => by
    simpa using α.norm_convolutionL1_apply_le f g

/-- On compactly supported continuous coefficient functions, `convolutionL1` is represented almost
everywhere by the pointwise twisted convolution integral `s ↦ ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ`. -/
theorem convolutionL1_toLp_ae_eq (f g : C_c(G, A)) :
    α.convolutionL1 μ (CompactlySupportedContinuousMap.toLp 1 μ ℂ f)
        (CompactlySupportedContinuousMap.toLp 1 μ ℂ g) =ᵐ[μ]
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
  refine (L1.integrable_coeFn _).ae_eq_of_forall_setIntegral_eq _ _
    (α.convolution μ f g).integrable fun s _ _ => ?_
  let T : Lp A 1 μ →L[ℂ] A :=
    (L1.integralCLM' (μ := μ.restrict s) ℂ).comp (LpToLpRestrictCLM G A ℂ μ 1 s)
  have hT (u : Lp A 1 μ) : T u = ∫ x in s, u x ∂μ := by
    rw [ContinuousLinearMap.comp_apply, ← L1.integral_eq', L1.integral_eq_integral]
    exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℂ s u)
  have hinner (r : G) :
      ∫ x in s, ((ContinuousLinearMap.mul ℂ A (f r)).compLp
        (α.translateLp μ 1 r (CompactlySupportedContinuousMap.toLp 1 μ ℂ g)) : G → A) x ∂μ =
      ∫ x in s, F x r ∂μ := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [(ContinuousLinearMap.mul ℂ A (f r)).coeFn_compLp
        (α.translateLp μ 1 r (CompactlySupportedContinuousMap.toLp 1 μ ℂ g)),
      α.coeFn_translateLp r (CompactlySupportedContinuousMap.toLp 1 μ ℂ g),
      (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
        (CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ g)] with x h₁ h₂ h₃
    have h₃' : (CompactlySupportedContinuousMap.toLp 1 μ ℂ g : G → A) (r⁻¹ * x) = g (r⁻¹ * x) := h₃
    rw [h₁, ContinuousLinearMap.mul_apply', h₂, h₃']
  have hf_toLp : CompactlySupportedContinuousMap.toLp 1 μ ℂ f = f.integrable.toL1 f :=
    Lp.ext ((CompactlySupportedContinuousMap.coeFn_toLp ℂ f).trans f.integrable.coeFn_toL1.symm)
  rw [← hT, hf_toLp, α.convolutionL1_integrable_toL1 f.integrable,
    ← T.integral_comp_comm (α.integrable_mul_translateLp f.integrable _)]
  simp_rw [hT, hinner, convolution_apply]
  exact integral_integral_swap_of_hasCompactSupport (μ := μ) (ν := μ.restrict s)
    (f := fun r x => F x r) (hFc.comp continuous_swap)
    (hFs.comp_homeomorph (Homeomorph.prodComm G G))

@[simp]
theorem convolutionL1_toLp (f g : C_c(G, A)) :
    α.convolutionL1 μ (CompactlySupportedContinuousMap.toLp 1 μ ℂ f)
        (CompactlySupportedContinuousMap.toLp 1 μ ℂ g) =
      CompactlySupportedContinuousMap.toLp 1 μ ℂ (α.convolution μ f g) :=
  Lp.ext ((α.convolutionL1_toLp_ae_eq f g).trans
    (CompactlySupportedContinuousMap.coeFn_toLp ℂ (α.convolution μ f g)).symm)

variable {α} in
/-- `ConvolutionAlgebra.toL1` turns the convolution product into `CStarAction.convolutionL1`. -/
@[simp]
theorem ConvolutionAlgebra.toL1_mul (f g : ConvolutionAlgebra α μ) :
    toL1 (f * g) = α.convolutionL1 μ (toL1 f) (toL1 g) := by
  rw [toL1_eq_toLp, toL1_eq_toLp, toL1_eq_toLp, ofConv_mul, α.convolutionL1_toLp]

variable {α} in
/-- `completionEquivL1` intertwines multiplication in the abstract `L¹` completion with
`CStarAction.convolutionL1` on `Lp A 1 μ`. -/
@[simp]
theorem ConvolutionAlgebra.completionEquivL1_mul
    (x y : Completion (ConvolutionAlgebra α μ)) :
    completionEquivL1 α μ (x * y) =
      α.convolutionL1 μ (completionEquivL1 α μ x) (completionEquivL1 α μ y) := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f g =>
    rw [← Completion.coe_mul', completionEquivL1_coe, completionEquivL1_coe,
      completionEquivL1_coe, toL1_mul]

variable {α} in
@[simp]
theorem ConvolutionAlgebra.completionEquivL1_symm_convolutionL1 (f g : Lp A 1 μ) :
    (completionEquivL1 α μ).symm (α.convolutionL1 μ f g) =
      (completionEquivL1 α μ).symm f * (completionEquivL1 α μ).symm g := by
  apply (completionEquivL1 α μ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, completionEquivL1_mul,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Twisted `L¹` convolution is associative on `Lp A 1 μ`. -/
theorem convolutionL1_assoc (f g h : Lp A 1 μ) :
    α.convolutionL1 μ (α.convolutionL1 μ f g) h =
      α.convolutionL1 μ f (α.convolutionL1 μ g h) := by
  apply (ConvolutionAlgebra.completionEquivL1 α μ).symm.injective
  simp [mul_assoc]

/-- Twisted left translation is a left multiplier of twisted `L¹` convolution. -/
theorem translateLp_convolutionL1 (r : G) (f g : Lp A 1 μ) :
    α.translateLp μ 1 r (α.convolutionL1 μ f g) =
      α.convolutionL1 μ (α.translateLp μ 1 r f) g := by
  have hD := ConvolutionAlgebra.denseRange_toL1 (α := α) (μ := μ)
  refine congrFun (Continuous.ext_on (hD.prod hD)
    ((α.translateLp μ 1 r).continuous.comp (α.convolutionL1 μ).continuous₂)
    ((α.convolutionL1 μ).continuous₂.comp
      (((α.translateLp μ 1 r).continuous.comp continuous_fst).prodMk continuous_snd)) ?_) (f, g)
  rintro ⟨_, _⟩ ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  simp [← ConvolutionAlgebra.toL1_translateLIE, ← ConvolutionAlgebra.toL1_mul,
    ConvolutionAlgebra.translateLIE_apply_mul]

/-- Pointwise left coefficient multiplication is a left multiplier of twisted `L¹` convolution. -/
theorem compLp_mul_convolutionL1 (a : A) (f g : Lp A 1 μ) :
    (ContinuousLinearMap.mul ℂ A a).compLp (α.convolutionL1 μ f g) =
      α.convolutionL1 μ ((ContinuousLinearMap.mul ℂ A a).compLp f) g := by
  have hL : Continuous fun u : Lp A 1 μ => (ContinuousLinearMap.mul ℂ A a).compLp u :=
    ((ContinuousLinearMap.mul ℂ A a).compLpL 1 μ).continuous
  have hD := ConvolutionAlgebra.denseRange_toL1 (α := α) (μ := μ)
  refine congrFun (Continuous.ext_on (hD.prod hD)
    (hL.comp (α.convolutionL1 μ).continuous₂)
    ((α.convolutionL1 μ).continuous₂.comp ((hL.comp continuous_fst).prodMk continuous_snd)) ?_)
    (f, g)
  rintro ⟨_, _⟩ ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  simp [← ConvolutionAlgebra.toL1_coefficientMul, ← ConvolutionAlgebra.toL1_mul,
    ConvolutionAlgebra.coefficientMul_apply_mul]

/-- For the trivial action on `ℂ`, `convolutionL1` coincides with the scalar group convolution
`MeasureTheory.Lp.convolutionL`. -/
@[simp]
theorem trivial_convolutionL1 (f g : Lp ℂ 1 μ) :
    (trivial (G := G) (A := ℂ)).convolutionL1 μ f g =
      Lp.convolutionL μ 1 ENNReal.one_ne_top f g := by
  rw [convolutionL1_apply, Lp.convolutionL_apply]
  refine integral_congr_ae (.of_forall fun r => ?_)
  dsimp only
  rw [trivial_translateLp]
  refine Lp.ext ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ (f r)).coeFn_compLp (Lp.leftTranslation μ 1 ℂ r g),
    Lp.coeFn_smul (f r) (Lp.leftTranslation μ 1 ℂ r g)] with s hs₁ hs₂
  rw [hs₁, ContinuousLinearMap.mul_apply', hs₂, Pi.smul_apply, smul_eq_mul]

end ConvolutionL1

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
theorem twistedInvolutionL1_convolutionL1 (f g : Lp A 1 μ) :
    α.twistedInvolutionL1 μ (α.convolutionL1 μ f g) =
      α.convolutionL1 μ (α.twistedInvolutionL1 μ g) (α.twistedInvolutionL1 μ f) := by
  have hD := ConvolutionAlgebra.denseRange_toL1 (α := α) (μ := μ)
  refine congrFun (Continuous.ext_on (hD.prod hD)
    (f := fun p : Lp A 1 μ × Lp A 1 μ => α.twistedInvolutionL1 μ (α.convolutionL1 μ p.1 p.2))
    (g := fun p : Lp A 1 μ × Lp A 1 μ =>
      α.convolutionL1 μ (α.twistedInvolutionL1 μ p.2) (α.twistedInvolutionL1 μ p.1))
    (by fun_prop) (by fun_prop) ?_) (f, g)
  rintro ⟨_, _⟩ ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  simp only [← ConvolutionAlgebra.toL1_mul, ← ConvolutionAlgebra.toL1_star, star_mul]

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
    change ‖(α.integrable_action_apply u).toL1 _‖ = ‖u‖
    rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm u]
    refine integral_congr_ae ?_
    filter_upwards [(α.integrable_action_apply u).coeFn_toL1] with s hs
    rw [hs, StarAlgEquiv.norm_map]

private theorem coeFn_actionPointwiseL1 {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) :
    α.actionPointwiseL1 u =ᵐ[μ] fun s => α s (u s) :=
  (α.integrable_action_apply u).coeFn_toL1

end ActionPointwise

section RegularHaar

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]

private theorem twistedInvolutionL1_eq_actionPointwiseL1 (f : Lp A 1 μ) :
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
  have h₅' : (ConvolutionAlgebra.toL1 g : G → A) s⁻¹ = g.ofConv s⁻¹ := h₅
  rw [h₁, ConvolutionAlgebra.ofConv_star, twistedInvolution_apply, h₂, h₃, Pi.star_apply, h₄, h₅']
  simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, star_smul, star_trivial]
  rw [← map_smul, Complex.coe_smul]

/-- For a regular Haar measure, the twisted `L¹` involution is represented almost everywhere by
`s ↦ (Measure.modularCharacter s : ℝ) • α s (star (f s⁻¹))`. -/
theorem coeFn_twistedInvolutionL1 (f : Lp A 1 μ) :
    α.twistedInvolutionL1 μ f =ᵐ[μ]
      fun s => (Measure.modularCharacter s : ℝ) • α s (star (f s⁻¹)) := by
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
theorem trivial_twistedInvolutionL1 (f : Lp A 1 μ) :
    (trivial (G := G) (A := A)).twistedInvolutionL1 μ f =
      star (Lp.modularInversion μ 1 ℂ f) := by
  refine Lp.ext ?_
  filter_upwards [(trivial (G := G) (A := A)).coeFn_twistedInvolutionL1 f,
    Lp.coeFn_star (Lp.modularInversion μ 1 ℂ f),
    Lp.coeFn_modularInversion (𝕜 := ℂ) f] with s h₁ h₂ h₃
  rw [h₁, trivial_apply, h₂, Pi.star_apply, h₃]
  simp [ENNReal.toReal_one, star_smul]

end RegularHaar

end CStarAction

end TauCeti
