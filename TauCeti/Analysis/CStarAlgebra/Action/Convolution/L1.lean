/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Multiplier
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.MeasureTheory.Function.Lp.CompactlySupported
public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
public import TauCeti.MeasureTheory.Function.Lp.Star
public import TauCeti.Topology.Algebra.UniformRing
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.CStarAlgebra.Hom
import TauCeti.MeasureTheory.Function.Lp.LinearIsometry
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular
import TauCeti.MeasureTheory.Group.Convolution.Support

/-!
# Realizing the twisted `L¹` Banach ⋆-algebra in Bochner `L¹`

Let `α : CStarAction G A` be a point-norm continuous action of a topological group `G` on a
possibly nonunital complex C⋆-algebra `A`. In
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed`, the compact-support convolution algebra
`CStarAction.ConvolutionAlgebra α μ` carries the `L¹` seminorm pulled back along
`ConvolutionAlgebra.toL1 : ConvolutionAlgebra α μ →ₗ[ℂ] Lp A 1 μ`, and its abstract completion
`UniformSpace.Completion (ConvolutionAlgebra α μ)` is the twisted `L¹` Banach ⋆-algebra.

When `G` is weakly locally compact and `μ` is finite on compact sets and inner regular on sets of
finite measure (`IsFiniteMeasureOnCompacts μ` and `μ.InnerRegularCompactLTTop`), compactly supported
continuous functions are dense in `Lp A 1 μ`. Consequently `toL1` has dense range and extends to a
linear isometric equivalence
`ConvolutionAlgebra.completionEquivL1 α μ : Completion (ConvolutionAlgebra α μ) ≃ₗᵢ[ℂ] Lp A 1 μ`.
This holds without separability of `A`, second countability of `G`, σ-finiteness of `μ`, unitality
of `A`, or full support of `μ`, including zero algebras and the zero measure.

On `Lp A p μ` and `Lp A 1 μ` we construct the concrete dynamical operations and show that they match
those of `Completion (ConvolutionAlgebra α μ)` across `completionEquivL1`:

* `CStarAction.translateLp`: twisted left translation `(r • f)(s) = α r (f (r⁻¹ * s))` on
  `Lp A p μ`, jointly continuous on `G × Lp A p μ` for `1 ≤ p < ∞` whenever `μ` is locally finite,
  inner regular on finite-measure sets, and left invariant (without local compactness).
* `CStarAction.convolutionL1`: twisted convolution on `Lp A 1 μ`, defined for any locally finite,
  inner-regular left-invariant Borel measure without local compactness, countability, or
  σ-finiteness hypotheses as the `Lp A 1 μ`-valued Bochner integral
  `f ⋆_α g = ∫ r, (ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g) ∂μ`. Both the
  vector-valued integral construction and the set-integral Fubini proof on `C_c(G, A)`
  (`CStarAction.convolutionL1_toLp_ae_eq`) closely adapt the scalar group-convolution formalization
  `MeasureTheory.Lp.convolutionL` and `MeasureTheory.Lp.convolutionL_toL1_ae_eq` in
  `TauCeti.MeasureTheory.Function.Lp.GroupConvolution`. On locally compact `G`, `completionEquivL1`
  intertwines multiplication in the completion with `convolutionL1`.
* `CStarAction.twistedInvolutionL1`: the twisted involution on `Lp A 1 μ` as a conjugate-linear
  isometric equivalence, anti-multiplicative for `convolutionL1`, and represented almost everywhere
  by `s ↦ (Measure.modularCharacter s : ℝ) • α s (star (f s⁻¹))` for a regular Haar measure.

For the trivial action on `ℂ`, `convolutionL1` and `twistedInvolutionL1` specialize to
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

section TranslateLp

variable {G A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] (α : CStarAction G A) (μ : Measure G) (p : ℝ≥0∞) [Fact (1 ≤ p)]
  [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Twisted left translation `(r • f)(s) = α r (f (r⁻¹ * s))` on `Lp A p μ` for a left-invariant
measure `μ`, bundled as a group homomorphism into linear isometric equivalences. -/
def translateLp : G →* (Lp A p μ ≃ₗᵢ[ℂ] Lp A p μ) where
  toFun r := (Lp.leftTranslation μ p ℂ r).trans ((α r).toLinearIsometryEquiv.compLpₗᵢ p μ)
  map_one' := by
    ext f : 1
    refine Lp.ext ?_
    filter_upwards [(α 1).toLinearIsometryEquiv.coeFn_compLpₗᵢ (Lp.leftTranslation μ p ℂ 1 f),
      Lp.coeFn_leftTranslation (𝕜 := ℂ) 1 f] with s hs₁ hs₂
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.coe_one, id_eq,
      StarAlgEquiv.coe_toLinearIsometryEquiv] at hs₁ ⊢
    rw [hs₁, hs₂, inv_one, one_mul, one_apply]
  map_mul' r t := by
    ext f : 1
    refine Lp.ext ?_
    filter_upwards
      [(α (r * t)).toLinearIsometryEquiv.coeFn_compLpₗᵢ (Lp.leftTranslation μ p ℂ (r * t) f),
      Lp.coeFn_leftTranslation (𝕜 := ℂ) (r * t) f,
      (α r).toLinearIsometryEquiv.coeFn_compLpₗᵢ
        (Lp.leftTranslation μ p ℂ r
          ((α t).toLinearIsometryEquiv.compLpₗᵢ p μ (Lp.leftTranslation μ p ℂ t f))),
      Lp.coeFn_leftTranslation (𝕜 := ℂ) r
        ((α t).toLinearIsometryEquiv.compLpₗᵢ p μ (Lp.leftTranslation μ p ℂ t f)),
      (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
        ((α t).toLinearIsometryEquiv.coeFn_compLpₗᵢ (Lp.leftTranslation μ p ℂ t f)),
      (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
        (Lp.coeFn_leftTranslation (𝕜 := ℂ) t f)] with s h₁ h₂ h₃ h₄ h₅ h₆
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.coe_mul, Function.comp_apply,
      StarAlgEquiv.coe_toLinearIsometryEquiv] at h₁ h₃ h₅ ⊢
    rw [h₁, h₂, h₃, h₄, h₅, h₆, mul_inv_rev, mul_assoc, α.mul_apply]

variable {μ p}

/-- Twisted left translation on `Lp A p μ` is almost everywhere `s ↦ α r (f (r⁻¹ * s))`. -/
theorem coeFn_translateLp (r : G) (f : Lp A p μ) :
    α.translateLp μ p r f =ᵐ[μ] fun s => α r (f (r⁻¹ * s)) := by
  filter_upwards [(α r).toLinearIsometryEquiv.coeFn_compLpₗᵢ (Lp.leftTranslation μ p ℂ r f),
    Lp.coeFn_leftTranslation (𝕜 := ℂ) r f] with s hs₁ hs₂
  rw [StarAlgEquiv.coe_toLinearIsometryEquiv] at hs₁
  exact hs₁.trans (congrArg (α r) hs₂)

theorem translateLp_symm (r : G) :
    (α.translateLp μ p r).symm = α.translateLp μ p r⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- For the trivial action, twisted left translation on `Lp A p μ` is ordinary left translation. -/
@[simp]
theorem translateLp_trivial (r : G) :
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
  simp only [ContinuousLinearMap.mul_apply'] at h₂
  rw [h₁, h₂, map_mul, h₃, ContinuousLinearMap.mul_apply', h₄]

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

end TranslateLp

section ContinuousTranslateLp

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) {μ : Measure G} [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Twisted left translation on `Lp A p μ` is jointly continuous on `G × Lp A p μ` for `p < ∞`. -/
@[fun_prop]
theorem continuous_translateLp (hp : p ≠ ∞) :
    Continuous fun q : G × Lp A p μ => α.translateLp μ p q.1 q.2 := by
  have : Fact (p ≠ ∞) := ⟨hp⟩
  have hdef : (fun q : G × Lp A p μ => α.translateLp μ p q.1 q.2) =
      fun q => (α q.1).toLinearIsometryEquiv.compLpₗᵢ p μ (DomMulAct.mk q.1⁻¹ • q.2) := by
    ext q : 1
    simp [translateLp, Lp.leftTranslation_apply]
  rw [hdef]
  exact (LinearIsometryEquiv.continuous_compLpₗᵢ hp
    (e := fun r => (α r).toLinearIsometryEquiv) fun a => by
      simp_rw [StarAlgEquiv.coe_toLinearIsometryEquiv]
      exact α.continuous_orbit a).comp
    (continuous_fst.prodMk ((DomMulAct.continuous_mk.comp continuous_fst.inv).smul continuous_snd))

/-- Every orbit of twisted left translation in `Lp A p μ` is norm-continuous for `p < ∞`. -/
@[fun_prop]
theorem continuous_translateLp_apply (hp : p ≠ ∞) (f : Lp A p μ) :
    Continuous fun r : G => α.translateLp μ p r f :=
  (α.continuous_translateLp hp).comp (continuous_id.prodMk continuous_const)

end ContinuousTranslateLp

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

@[simp]
theorem completionEquivL1_symm_toLp (f : C_c(G, A)) :
    (completionEquivL1 α μ).symm (CompactlySupportedContinuousMap.toLp 1 μ ℂ f) =
      ((toConv f : ConvolutionAlgebra α μ) : Completion (ConvolutionAlgebra α μ)) := by
  rw [← toL1_eq_toLp, completionEquivL1_symm_toL1]

@[simp]
theorem completionEquivL1_completion_coefficientMul (a : A)
    (x : Completion (ConvolutionAlgebra α μ)) :
    completionEquivL1 α μ ((coefficientMul a).completion x) =
      (ContinuousLinearMap.mul ℂ A a).compLp (completionEquivL1 α μ x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((completionEquivL1 α μ).continuous.comp (coefficientMul a).completion.continuous)
      (((ContinuousLinearMap.mul ℂ A a).compLpL 1 μ).continuous.comp
        (completionEquivL1 α μ).continuous)
  | ih f =>
    rw [ContinuousLinearMap.completion_apply_coe, completionEquivL1_coe, completionEquivL1_coe,
      toL1_coefficientMul]

@[simp]
theorem completionEquivL1_map_coefficientMul (a : A)
    (x : Completion (ConvolutionAlgebra α μ)) :
    completionEquivL1 α μ (Completion.map (coefficientMul a) x) =
      (ContinuousLinearMap.mul ℂ A a).compLp (completionEquivL1 α μ x) := by
  rw [← ContinuousLinearMap.coe_completion, completionEquivL1_completion_coefficientMul]

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
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((completionEquivL1 α μ).continuous.comp (translateLIE r).completion.continuous)
      ((α.translateLp μ 1 r).continuous.comp (completionEquivL1 α μ).continuous)
  | ih f =>
    rw [LinearIsometryEquiv.completion_apply_coe, completionEquivL1_coe, completionEquivL1_coe,
      toL1_translateLIE]

@[simp]
theorem completionEquivL1_map_translateLIE (r : G)
    (x : Completion (ConvolutionAlgebra α μ)) :
    completionEquivL1 α μ (Completion.map (translateLIE r) x) =
      α.translateLp μ 1 r (completionEquivL1 α μ x) := by
  simpa only [LinearIsometryEquiv.coe_completion] using
    completionEquivL1_completion_translateLIE (α := α) r x

@[simp]
theorem completionEquivL1_symm_translateLp (r : G) (f : Lp A 1 μ) :
    (completionEquivL1 α μ).symm (α.translateLp μ 1 r f) =
      Completion.map (translateLIE r) ((completionEquivL1 α μ).symm f) := by
  apply (completionEquivL1 α μ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, completionEquivL1_map_translateLIE,
    LinearIsometryEquiv.apply_symm_apply]

end TranslateCompletion

end ConvolutionAlgebra

section ConvolutionL1

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) {μ : Measure G} [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

omit [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
private theorem norm_compLp_mul_translateLp_le (a : A) (r : G) (g : Lp A 1 μ) :
    ‖(ContinuousLinearMap.mul ℂ A a).compLp (α.translateLp μ 1 r g)‖ ≤ ‖a‖ * ‖g‖ := by
  calc
    ‖(ContinuousLinearMap.mul ℂ A a).compLp (α.translateLp μ 1 r g)‖ ≤
        ‖ContinuousLinearMap.mul ℂ A a‖ * ‖α.translateLp μ 1 r g‖ :=
      ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ ‖a‖ * ‖g‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_apply_le ℂ A a)
        (norm_nonneg g)

/-- The `Lp A 1 μ`-valued integrand `r ↦ (f r) • (r • g)` of a twisted convolution is Bochner
integrable, with neither local compactness of `G`, separability of `A`, nor σ-finiteness of `μ`. -/
theorem integrable_mul_translateLp {f : G → A} (hf : Integrable f μ) (g : Lp A 1 μ) :
    Integrable (fun r => (ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g)) μ := by
  let B : Lp A 1 μ →L[ℂ] A →L[ℂ] Lp A 1 μ := ((ContinuousLinearMap.mul ℂ A).compLpL₂ 1 μ).flip
  have hmeas : AEStronglyMeasurable
      (fun r => B (α.translateLp μ 1 r g) (f r)) μ :=
    hf.aefinStronglyMeasurable.aestronglyMeasurable_clm_apply
      (B.continuous.comp (α.continuous_translateLp_apply ENNReal.one_ne_top g))
  exact (hf.norm.mul_const ‖g‖).mono' hmeas
    (.of_forall fun r => α.norm_compLp_mul_translateLp_le (f r) r g)

omit [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
private theorem norm_integral_mul_translateLp_le (f g : Lp A 1 μ) :
    ‖∫ r, (ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g) ∂μ‖ ≤ ‖f‖ * ‖g‖ := by
  rw [L1.norm_eq_integral_norm f, ← integral_mul_const]
  exact norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.mul_const _)
    (.of_forall fun r => α.norm_compLp_mul_translateLp_le (f r) r g)

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
theorem convolutionL1_toL1 {f : G → A} (hf : Integrable f μ) (g : Lp A 1 μ) :
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
    (α.convolution μ f g).integrable fun s _ hμs => ?_
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
    rw [h₁, ContinuousLinearMap.mul_apply', h₂, h₃]
  rw [← Set.setIntegralLp_apply (𝕜 := ℂ) s hμs, α.convolutionL1_apply,
    ← (Set.setIntegralLp (𝕜 := ℂ) s hμs).integral_comp_comm
      (α.integrable_mul_translateLp (L1.integrable_coeFn _) _)]
  simp_rw [Set.setIntegralLp_apply, convolution_apply]
  refine (integral_congr_ae ?_).trans
    (integral_integral_swap_of_hasCompactSupport (μ := μ) (ν := μ.restrict s)
      (f := fun r x => F x r) (hFc.comp continuous_swap)
      (hFs.comp_homeomorph (Homeomorph.prodComm G G)))
  filter_upwards [CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ f] with r hr
  rw [hr, hinner r]

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

/-- Pointwise left coefficient multiplication is a left multiplier of twisted `L¹` convolution. -/
theorem compLp_mul_convolutionL1 (a : A) (f g : Lp A 1 μ) :
    (ContinuousLinearMap.mul ℂ A a).compLp (α.convolutionL1 μ f g) =
      α.convolutionL1 μ ((ContinuousLinearMap.mul ℂ A a).compLp f) g := by
  have hmul (b : A) (u : Lp A 1 μ) :
      (ContinuousLinearMap.mul ℂ A a).compLp ((ContinuousLinearMap.mul ℂ A b).compLp u) =
        (ContinuousLinearMap.mul ℂ A (a * b)).compLp u := by
    refine Lp.ext ?_
    filter_upwards [(ContinuousLinearMap.mul ℂ A a).coeFn_compLp
        ((ContinuousLinearMap.mul ℂ A b).compLp u),
      (ContinuousLinearMap.mul ℂ A b).coeFn_compLp u,
      (ContinuousLinearMap.mul ℂ A (a * b)).coeFn_compLp u] with s h₁ h₂ h₃
    rw [h₁, h₂, h₃, ContinuousLinearMap.mul_apply', ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.mul_apply', mul_assoc]
  let L : Lp A 1 μ →L[ℂ] Lp A 1 μ := (ContinuousLinearMap.mul ℂ A).compLpL₂ 1 μ a
  calc
    (ContinuousLinearMap.mul ℂ A a).compLp (α.convolutionL1 μ f g) =
        ∫ r, L ((ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g)) ∂μ := by
      simpa only [L, convolutionL1_apply, ContinuousLinearMap.compLpL₂_apply_apply] using
        (L.integral_comp_comm (α.integrable_mul_translateLp (L1.integrable_coeFn f) g)).symm
    _ = α.convolutionL1 μ ((ContinuousLinearMap.mul ℂ A a).compLp f) g := by
      rw [convolutionL1_apply]
      refine integral_congr_ae ?_
      filter_upwards [(ContinuousLinearMap.mul ℂ A a).coeFn_compLp f] with r hr
      rw [ContinuousLinearMap.compLpL₂_apply_apply, hmul, hr, ContinuousLinearMap.mul_apply']

/-- Twisted left translation is a left multiplier of twisted `L¹` convolution. -/
theorem translateLp_convolutionL1 (r : G) (f g : Lp A 1 μ) :
    α.translateLp μ 1 r (α.convolutionL1 μ f g) =
      α.convolutionL1 μ (α.translateLp μ 1 r f) g := by
  let L : Lp A 1 μ →L[ℂ] Lp A 1 μ := (α.translateLp μ 1 r).toContinuousLinearEquiv
  calc
    α.translateLp μ 1 r (α.convolutionL1 μ f g) =
        ∫ s, L ((ContinuousLinearMap.mul ℂ A (f s)).compLp (α.translateLp μ 1 s g)) ∂μ := by
      simpa only [L, convolutionL1_apply, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
        (L.integral_comp_comm (α.integrable_mul_translateLp (L1.integrable_coeFn f) g)).symm
    _ = ∫ s, (ContinuousLinearMap.mul ℂ A (α r (f (r⁻¹ * (r * s))))).compLp
          (α.translateLp μ 1 (r * s) g) ∂μ := by
      refine integral_congr_ae (.of_forall fun s => ?_)
      have hmul : α.translateLp μ 1 r (α.translateLp μ 1 s g) = α.translateLp μ 1 (r * s) g := by
        rw [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]
      simp only [L, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        α.translateLp_compLp_mul, hmul, inv_mul_cancel_left]
    _ = ∫ t, (ContinuousLinearMap.mul ℂ A (α r (f (r⁻¹ * t)))).compLp
          (α.translateLp μ 1 t g) ∂μ :=
      integral_mul_left_eq_self
        (fun t => (ContinuousLinearMap.mul ℂ A (α r (f (r⁻¹ * t)))).compLp (α.translateLp μ 1 t g))
        r
    _ = α.convolutionL1 μ (α.translateLp μ 1 r f) g := by
      rw [convolutionL1_apply]
      refine integral_congr_ae ?_
      filter_upwards [α.coeFn_translateLp r f] with t ht
      rw [ht]

/-- Twisted `L¹` convolution is associative on `Lp A 1 μ`. -/
theorem convolutionL1_assoc (f g h : Lp A 1 μ) :
    α.convolutionL1 μ (α.convolutionL1 μ f g) h =
      α.convolutionL1 μ f (α.convolutionL1 μ g h) := by
  let R : Lp A 1 μ →L[ℂ] Lp A 1 μ := (α.convolutionL1 μ).flip h
  calc
    α.convolutionL1 μ (α.convolutionL1 μ f g) h =
        ∫ r, R ((ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g)) ∂μ := by
      simpa only [R, convolutionL1_apply, ContinuousLinearMap.flip_apply] using
        (R.integral_comp_comm (α.integrable_mul_translateLp (L1.integrable_coeFn f) g)).symm
    _ = α.convolutionL1 μ f (α.convolutionL1 μ g h) := by
      rw [convolutionL1_apply]
      refine integral_congr_ae (.of_forall fun r => ?_)
      simp only [R, ContinuousLinearMap.flip_apply, ← α.compLp_mul_convolutionL1,
        ← α.translateLp_convolutionL1]

/-- For the trivial action on `ℂ`, `convolutionL1` coincides with the scalar group convolution
`MeasureTheory.Lp.convolutionL`. -/
@[simp]
theorem convolutionL1_trivial (f g : Lp ℂ 1 μ) :
    (trivial (G := G) (A := ℂ)).convolutionL1 μ f g =
      Lp.convolutionL μ 1 ENNReal.one_ne_top f g := by
  rw [convolutionL1_apply, Lp.convolutionL_apply]
  refine integral_congr_ae (.of_forall fun r => ?_)
  dsimp only
  rw [translateLp_trivial]
  refine Lp.ext ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ (f r)).coeFn_compLp (Lp.leftTranslation μ 1 ℂ r g),
    Lp.coeFn_smul (f r) (Lp.leftTranslation μ 1 ℂ r g)] with s hs₁ hs₂
  rw [hs₁, ContinuousLinearMap.mul_apply', hs₂, Pi.smul_apply, smul_eq_mul]

end ConvolutionL1

section CompletionMul

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  {α : CStarAction G A} {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

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

@[simp]
theorem ConvolutionAlgebra.completionEquivL1_symm_convolutionL1 (f g : Lp A 1 μ) :
    (completionEquivL1 α μ).symm (α.convolutionL1 μ f g) =
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
theorem twistedInvolutionL1_convolutionL1 (f g : Lp A 1 μ) :
    α.twistedInvolutionL1 μ (α.convolutionL1 μ f g) =
      α.convolutionL1 μ (α.twistedInvolutionL1 μ g) (α.twistedInvolutionL1 μ f) := by
  apply (ConvolutionAlgebra.completionEquivL1 α μ).symm.injective
  simp only [ConvolutionAlgebra.completionEquivL1_symm_twistedInvolutionL1,
    ConvolutionAlgebra.completionEquivL1_symm_convolutionL1]
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
  rw [h₁, ConvolutionAlgebra.ofConv_star, twistedInvolution_apply, h₂, h₃, Pi.star_apply, h₄, h₅]
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
theorem twistedInvolutionL1_trivial (f : Lp A 1 μ) :
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
