/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Functoriality
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Translate
public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# The Bochner `L¹` realization of the twisted convolution algebra

Let `α` be a point-norm continuous action of a topological group `G` on a possibly nonunital
C⋆-algebra `A`, and let `μ` be a measure on `G`. In
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed` the compact-support convolution algebra
`ConvolutionAlgebra α μ` carries the `L¹` seminorm induced along the linear isometry
`ConvolutionAlgebra.toL1LI : ConvolutionAlgebra α μ →ₗᵢ[ℂ] Lp A 1 μ`, and its completion
`UniformSpace.Completion (ConvolutionAlgebra α μ)` is the abstract twisted `L¹` Banach ⋆-algebra.
This file identifies that completion isometrically with the Bochner space `Lp A 1 μ` and develops
the twisted `L¹` translation, convolution, and involution directly on `Lp`.

First, `G` acts isometrically on `Lp A p μ` (`1 ≤ p ≤ ∞`) in two ways: pointwise in the
coefficient algebra by `CStarAction.actionLp`, `(r • u) s = α r (u s)`, and, when `μ` is left
invariant, by the twisted left translation `CStarAction.translateLp`,
`(r • u) s = α r (u (r⁻¹ * s))`. For `p < ∞` and a locally finite Borel measure that is inner
regular on finite-measure sets, every twisted-translation orbit `r ↦ translateLp r u` is norm
continuous in `Lp A p μ`. No separability, second countability, or σ-finiteness is needed.

Using strong continuity of `translateLp`, an integrable kernel `h ∈ Lp A 1 μ` acts on `Lp A p μ`
(`1 ≤ p < ∞`) by the `Lp`-valued Bochner integral

```text
h ⋆ f = ∫ y, h y • translateLp y f dμ(y),
```

bundled as the continuous bilinear map `CStarAction.convolutionLp` of norm at most one. As in
`MeasureTheory.Lp.convolutionL`, associativity and equivariance under coefficient multiplication
and twisted left translation follow directly from passing continuous linear maps through the
`Lp`-valued integral, without a product-measure Fubini theorem. For the trivial action on `ℂ`,
`translateLp` and `convolutionLp` reduce to `MeasureTheory.Lp.leftTranslation` and
`MeasureTheory.Lp.convolutionL`.

Extending `ConvolutionAlgebra.toL1LI` to the completion gives the linear isometry
`ConvolutionAlgebra.toL1FromCompletion`, which intertwines the abstract completion product with
`convolutionLp`. When `G` is weakly locally compact and `R₁` and `μ` is regular, compactly
supported continuous functions are dense in `Lp A 1 μ`
(`MeasureTheory.Lp.dense_setOf_continuous_hasCompactSupport`), upgrading `toL1FromCompletion` to
the linear isometric equivalence `ConvolutionAlgebra.completionEquivLp`. On a locally compact group
with a regular Haar measure, this equivalence transports the completion's star to the
conjugate-linear isometric involution `CStarAction.twistedInvolutionLp`, represented almost
everywhere by `s ↦ c(s) • α s (star (u s⁻¹))`, and approximation by absolutely summable series of
compactly supported continuous functions extends the pointwise formula
`(f ⋆ g) s = ∫ r, f r * α r (g (r⁻¹ * s)) dμ` to arbitrary Bochner-integrable functions `f` and `g`
almost everywhere, still without countability or σ-finiteness assumptions.

## Main definitions

* `TauCeti.CStarAction.actionLp`: the pointwise isometric action `(r • u) s = α r (u s)` of `G` on
  `Lp A p μ`.
* `TauCeti.CStarAction.translateLp`: the twisted left translation `(r • u) s = α r (u (r⁻¹ * s))`
  on `Lp A p μ`.
* `TauCeti.CStarAction.convolutionLp`: twisted convolution `Lp A 1 μ →L[ℂ] Lp A p μ →L[ℂ] Lp A p μ`
  for `1 ≤ p < ∞`, defined as an `Lp`-valued Bochner integral.
* `TauCeti.CStarAction.ConvolutionAlgebra.toL1FromCompletion`: the linear isometry from
  `Completion (ConvolutionAlgebra α μ)` into `Lp A 1 μ`.
* `TauCeti.CStarAction.ConvolutionAlgebra.completionEquivLp`: the linear isometric equivalence
  `Completion (ConvolutionAlgebra α μ) ≃ₗᵢ[ℂ] Lp A 1 μ` for a regular measure on a weakly locally
  compact `R₁` group.
* `TauCeti.CStarAction.twistedInvolutionLp`: the twisted conjugate-linear isometric involution
  `u ↦ (s ↦ c(s) • α s (star (u s⁻¹)))` on `Lp A 1 μ` for a regular Haar measure.
* `TauCeti.CStarAction.Hom.mapLp`: the contractive `Lp` map `Lp A p μ →L[ℂ] Lp B p μ` induced by an
  equivariant homomorphism `Hom α β`.

## Main results

* `TauCeti.CStarAction.continuous_translateLp_apply`: twisted left translation on `Lp A p μ` is
  strongly continuous for `p < ∞`.
* `TauCeti.CStarAction.convolutionLp_assoc`: `(h ⋆ k) ⋆ f = h ⋆ (k ⋆ f)`.
* `TauCeti.CStarAction.trivial_convolutionLp`: for the trivial action on `ℂ`, `convolutionLp`
  agrees with `MeasureTheory.Lp.convolutionL`.
* `TauCeti.CStarAction.ConvolutionAlgebra.completionEquivLp_mul`,
  `TauCeti.CStarAction.ConvolutionAlgebra.completionEquivLp_star`: `completionEquivLp` intertwines
  the completion's Banach ⋆-algebra operations with `convolutionLp` and `twistedInvolutionLp`.
* `TauCeti.CStarAction.coeFn_twistedInvolutionLp`: `twistedInvolutionLp` is represented almost
  everywhere by `s ↦ c(s) • α s (star (u s⁻¹))`.
* `TauCeti.CStarAction.ae_integrable_convolution_integrand`,
  `TauCeti.CStarAction.convolutionLp_toL1_ae_eq`: for any integrable `f, g : G → A` on a locally
  compact group with a regular Haar measure, `r ↦ f r * α r (g (r⁻¹ * s))` is integrable for
  almost every `s`, and its integral represents `convolutionLp` almost everywhere.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §§2.5, 3.2.
-/

public section

noncomputable section

open Filter Function MeasureTheory Topology UniformSpace
open scoped CompactlySupported CStarAlgebra ENNReal NNReal

namespace TauCeti.CStarAction

/-! ### Pointwise action and twisted left translation on `Lᵖ` -/

section ActionLp

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [MeasurableSpace G] (α : CStarAction G A) (μ : Measure G) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Pointwise application `(r • u) s = α r (u s)` of a C⋆-action on `Lp A p μ`, as a group
homomorphism into linear isometric equivalences. -/
def actionLp : G →* (Lp A p μ ≃ₗᵢ[ℂ] Lp A p μ) where
  toFun r :=
    { toFun := (α.toContinuousLinearMap r).compLpₗ p μ
      invFun := (α.toContinuousLinearMap r⁻¹).compLpₗ p μ
      left_inv u := by
        refine Lp.ext ?_
        filter_upwards [(α.toContinuousLinearMap r⁻¹).coeFn_compLp
            ((α.toContinuousLinearMap r).compLp u),
          (α.toContinuousLinearMap r).coeFn_compLp u] with s h₁ h₂
        simp [h₁, h₂]
      right_inv u := by
        refine Lp.ext ?_
        filter_upwards [(α.toContinuousLinearMap r).coeFn_compLp
            ((α.toContinuousLinearMap r⁻¹).compLp u),
          (α.toContinuousLinearMap r⁻¹).coeFn_compLp u] with s h₁ h₂
        simp [h₁, h₂]
      map_add' := map_add _
      map_smul' := map_smul _
      norm_map' u := by
        have hle (g : G) (v : Lp A p μ) : ‖(α.toContinuousLinearMap g).compLp v‖ ≤ ‖v‖ := by
          refine ((α.toContinuousLinearMap g).norm_compLp_le v).trans ?_
          have hnorm : ‖α.toContinuousLinearMap g‖ ≤ 1 :=
            ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
              simp [StarAlgEquiv.norm_map]
          simpa using mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)
        refine le_antisymm (hle r u) ?_
        have hu : (α.toContinuousLinearMap r⁻¹).compLp
            ((α.toContinuousLinearMap r).compLp u) = u := by
          refine Lp.ext ?_
          filter_upwards [(α.toContinuousLinearMap r⁻¹).coeFn_compLp
              ((α.toContinuousLinearMap r).compLp u),
            (α.toContinuousLinearMap r).coeFn_compLp u] with s h₁ h₂
          simp [h₁, h₂]
        simpa [hu] using hle r⁻¹ ((α.toContinuousLinearMap r).compLp u) }
  map_one' := by
    ext1 u
    refine Lp.ext ?_
    filter_upwards [(α.toContinuousLinearMap 1).coeFn_compLp u] with s hs
    simpa using hs
  map_mul' r t := by
    ext1 u
    refine Lp.ext ?_
    filter_upwards [(α.toContinuousLinearMap (r * t)).coeFn_compLp u,
      (α.toContinuousLinearMap r).coeFn_compLp ((α.toContinuousLinearMap t).compLp u),
      (α.toContinuousLinearMap t).coeFn_compLp u] with s h₁ h₂ h₃
    simp [h₁, h₂, h₃, mul_apply]

variable {μ p}

/-- `actionLp` acts by composing `Lp` classes with `α r`. -/
theorem actionLp_apply (r : G) (u : Lp A p μ) :
    α.actionLp μ p r u = (α.toContinuousLinearMap r).compLp u :=
  (rfl)

/-- Pointwise almost-everywhere formula for `actionLp`. -/
theorem coeFn_actionLp (r : G) (u : Lp A p μ) :
    α.actionLp μ p r u =ᵐ[μ] fun s => α r (u s) := by
  filter_upwards [(α.toContinuousLinearMap r).coeFn_compLp u] with s hs
  rw [actionLp_apply]
  simpa using hs

/-- The inverse of `actionLp` at `r` is `actionLp` at `r⁻¹`. -/
@[simp]
theorem actionLp_symm (r : G) :
    (α.actionLp μ p r).symm = α.actionLp μ p r⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- The trivial C⋆-action acts trivially on `Lp`. -/
@[simp]
theorem trivial_actionLp (r : G) :
    (trivial (G := G) (A := A)).actionLp μ p r = 1 := by
  ext1 u
  refine Lp.ext ?_
  filter_upwards [(trivial (G := G) (A := A)).coeFn_actionLp r u] with s hs
  simpa using hs

/-- `actionLp` maps an indicator constant class by applying `α r` to its constant value. -/
theorem actionLp_indicatorConstLp (r : G) {s : Set G} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (c : A) :
    α.actionLp μ p r (indicatorConstLp p hs hμs c) = indicatorConstLp p hs hμs (α r c) := by
  refine Lp.ext ?_
  filter_upwards [α.coeFn_actionLp r (indicatorConstLp p hs hμs c),
    indicatorConstLp_coeFn (p := p) (μ := μ) (hs := hs) (hμs := hμs) (c := c),
    indicatorConstLp_coeFn (p := p) (μ := μ) (hs := hs) (hμs := hμs) (c := α r c)]
    with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  by_cases hx : x ∈ s <;> simp [hx]

/-- For `p < ∞`, every orbit `r ↦ α.actionLp μ p r u` is norm continuous in `Lp A p μ`. -/
theorem continuous_actionLp_apply (hp : p ≠ ∞) (u : Lp A p μ) :
    Continuous fun r => α.actionLp μ p r u := by
  refine Lp.induction hp (motive := fun v => Continuous fun r => α.actionLp μ p r v) ?_ ?_ ?_ u
  · intro c s hs hμs
    have hcont : Continuous fun r => indicatorConstLp (μ := μ) p hs hμs.ne (α r c) := by
      refine continuous_iff_continuousAt.2 fun r₀ => tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have hsub (r : G) :
          ‖indicatorConstLp (μ := μ) p hs hμs.ne (α r c) -
              indicatorConstLp (μ := μ) p hs hμs.ne (α r₀ c)‖ ≤
            ‖α r c - α r₀ c‖ * μ.real s ^ (1 / p.toReal) := by
        rw [indicatorConstLp_sub]
        exact norm_indicatorConstLp_le
      have horbit : Continuous fun r => α r c := by fun_prop
      have ht :
          Tendsto (fun r => ‖α r c - α r₀ c‖ * μ.real s ^ (1 / p.toReal)) (𝓝 r₀) (𝓝 0) := by
        simpa only [sub_self, norm_zero, zero_mul] using
          (((horbit.tendsto r₀).sub_const (α r₀ c)).norm).mul_const (μ.real s ^ (1 / p.toReal))
      exact squeeze_zero (fun _ => norm_nonneg _) hsub ht
    simpa only [Lp.simpleFunc.coe_indicatorConst, α.actionLp_indicatorConstLp] using hcont
  · intro f g hf hg _ hcf hcg
    simp_rw [map_add]
    exact Continuous.add hcf hcg
  · refine isClosed_iff_nhds.2 fun v hv =>
      continuous_iff_continuousAt.2 fun r₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨w, hw, hwc⟩ := hv (Metric.ball v (ε / 3)) (Metric.ball_mem_nhds v (by positivity))
    have hvw : dist v w < ε / 3 := by simpa [dist_comm] using hw
    filter_upwards [Metric.tendsto_nhds.1 (hwc.continuousAt (x := r₀)) (ε / 3) (by positivity)]
      with r hr
    calc
      dist (α.actionLp μ p r v) (α.actionLp μ p r₀ v)
          ≤ dist (α.actionLp μ p r v) (α.actionLp μ p r w) +
              dist (α.actionLp μ p r w) (α.actionLp μ p r₀ w) +
              dist (α.actionLp μ p r₀ w) (α.actionLp μ p r₀ v) :=
        dist_triangle4 _ _ _ _
      _ = dist v w + dist (α.actionLp μ p r w) (α.actionLp μ p r₀ w) + dist w v := by
        rw [(α.actionLp μ p r).isometry.dist_eq, (α.actionLp μ p r₀).isometry.dist_eq]
      _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_comm w v]
        linarith [hr]
      _ = ε := by ring

/-- For `p < ∞`, `actionLp` is jointly continuous on `G × Lp A p μ`. -/
@[fun_prop]
theorem continuous_actionLp (hp : p ≠ ∞) :
    Continuous fun q : G × Lp A p μ => α.actionLp μ p q.1 q.2 :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun r => (α.actionLp μ p r).isometry.lipschitzWith) (α.continuous_actionLp_apply hp)

end ActionLp

section TranslateLp

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [MeasurableSpace G] [MeasurableMul G] (α : CStarAction G A) (μ : Measure G)
  [μ.IsMulLeftInvariant] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Pointwise coefficient action and group left translation commute on `Lp A p μ`. -/
theorem actionLp_leftTranslation (r t : G) (u : Lp A p μ) :
    α.actionLp μ p r (Lp.leftTranslation μ p ℂ t u) =
      Lp.leftTranslation μ p ℂ t (α.actionLp μ p r u) := by
  refine Lp.ext ?_
  filter_upwards [α.coeFn_actionLp r (Lp.leftTranslation μ p ℂ t u),
    Lp.coeFn_leftTranslation (𝕜 := ℂ) t u,
    Lp.coeFn_leftTranslation (𝕜 := ℂ) t (α.actionLp μ p r u),
    (measurePreserving_mul_left μ t⁻¹).quasiMeasurePreserving.ae (α.coeFn_actionLp r u)]
    with s h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

/-- Twisted left translation `(r • u) s = α r (u (r⁻¹ * s))` on `Lp A p μ`, as a group
homomorphism into linear isometric equivalences. -/
def translateLp : G →* (Lp A p μ ≃ₗᵢ[ℂ] Lp A p μ) where
  toFun r := α.actionLp μ p r * Lp.leftTranslation μ p ℂ r
  map_one' := by simp
  map_mul' r t := by
    ext1 u
    simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply,
      α.actionLp_leftTranslation μ p t r]

variable {μ p}

/-- `translateLp` applies left translation followed by the pointwise C⋆-action. -/
theorem translateLp_apply (r : G) (u : Lp A p μ) :
    α.translateLp μ p r u = α.actionLp μ p r (Lp.leftTranslation μ p ℂ r u) :=
  (rfl)

/-- Pointwise almost-everywhere formula for `translateLp`:
`(α.translateLp μ p r u) s = α r (u (r⁻¹ * s))`. -/
theorem coeFn_translateLp (r : G) (u : Lp A p μ) :
    α.translateLp μ p r u =ᵐ[μ] fun s => α r (u (r⁻¹ * s)) := by
  filter_upwards [α.coeFn_actionLp r (Lp.leftTranslation μ p ℂ r u),
    Lp.coeFn_leftTranslation (𝕜 := ℂ) r u] with s h₁ h₂
  rw [translateLp_apply, h₁, h₂]

/-- The inverse of twisted left translation by `r` is twisted left translation by `r⁻¹`. -/
@[simp]
theorem translateLp_symm (r : G) :
    (α.translateLp μ p r).symm = α.translateLp μ p r⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- For the trivial C⋆-action, `translateLp` is untwisted left translation `Lp.leftTranslation`. -/
@[simp]
theorem trivial_translateLp (r : G) :
    (trivial (G := G) (A := A)).translateLp μ p r = Lp.leftTranslation μ p ℂ r := by
  ext1 u
  simp [translateLp_apply]

/-- Twisted left translation and left coefficient multiplication satisfy covariance on `Lp`. -/
theorem translateLp_mul_compLp (r : G) (a : A) (u : Lp A p μ) :
    α.translateLp μ p r ((ContinuousLinearMap.mul ℂ A a).compLp u) =
      (ContinuousLinearMap.mul ℂ A (α r a)).compLp (α.translateLp μ p r u) := by
  refine Lp.ext ?_
  filter_upwards [α.coeFn_translateLp r ((ContinuousLinearMap.mul ℂ A a).compLp u),
    (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
      ((ContinuousLinearMap.mul ℂ A a).coeFn_compLp u),
    (ContinuousLinearMap.mul ℂ A (α r a)).coeFn_compLp (α.translateLp μ p r u),
    α.coeFn_translateLp r u] with s h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄, map_mul]

/-- On compactly supported coefficients, `translateLp` agrees with `CStarAction.translate`. -/
theorem translateLp_toL1 [ContinuousMul G] [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
    (r : G) (f : ConvolutionAlgebra α μ) :
    α.translateLp μ 1 r (ConvolutionAlgebra.toL1 f) =
      ConvolutionAlgebra.toL1 (α := α) (μ := μ) (.toConv (α.translate r f.ofConv)) := by
  refine Lp.ext ?_
  filter_upwards [α.coeFn_translateLp r (ConvolutionAlgebra.toL1 f),
    (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
      (ConvolutionAlgebra.coeFn_toL1 f),
    ConvolutionAlgebra.coeFn_toL1 (α := α) (μ := μ) (.toConv (α.translate r f.ofConv))]
    with s h₁ h₂ h₃
  simp [h₁, h₂, h₃]

/-- For `p < ∞`, twisted left translation on `Lp A p μ` is strongly continuous: every orbit
`r ↦ α.translateLp μ p r u` is norm continuous. -/
theorem continuous_translateLp_apply [IsTopologicalGroup G] [BorelSpace G]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] (hp : p ≠ ∞) (u : Lp A p μ) :
    Continuous fun r => α.translateLp μ p r u := by
  simp_rw [translateLp_apply]
  exact (α.continuous_actionLp hp).comp
    (continuous_id.prodMk (Lp.continuous_leftTranslation_apply hp u))

end TranslateLp

/-! ### Twisted Bochner `L¹` convolution on `Lᵖ` -/

section ConvolutionLp

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The integrand `y ↦ h y • α.translateLp μ p y f` of a twisted convolution is Bochner integrable
in `Lp A p μ` for `1 ≤ p < ∞`. -/
theorem integrable_mul_translateLp (hp : p ≠ ∞) {h : G → A} (hh : Integrable h μ)
    (f : Lp A p μ) :
    Integrable (fun y => (ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f)) μ := by
  have hmeas : AEStronglyMeasurable
      (fun y => (((ContinuousLinearMap.mul ℂ A).compLpL₂ p μ).flip
        (α.translateLp μ p y f)) (h y)) μ :=
    hh.aefinStronglyMeasurable.aestronglyMeasurable_clm_apply
      ((((ContinuousLinearMap.mul ℂ A).compLpL₂ p μ).flip).continuous.comp
        (α.continuous_translateLp_apply hp f))
  refine (hh.norm.mul_const ‖f‖).mono' hmeas (.of_forall fun y => ?_)
  calc
    ‖(ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f)‖
        ≤ ‖ContinuousLinearMap.mul ℂ A (h y)‖ * ‖α.translateLp μ p y f‖ :=
      ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ ‖h y‖ * ‖f‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_apply_le _ _ _)
        (norm_nonneg _)

omit [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
private theorem norm_integral_mul_translateLp_le (h : Lp A 1 μ) (f : Lp A p μ) :
    ‖∫ y, (ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f) ∂μ‖ ≤ ‖h‖ * ‖f‖ := by
  rw [L1.norm_eq_integral_norm, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((L1.integrable_coeFn h).norm.mul_const _)
    (.of_forall fun y => ?_)
  calc
    ‖(ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f)‖
        ≤ ‖ContinuousLinearMap.mul ℂ A (h y)‖ * ‖α.translateLp μ p y f‖ :=
      ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ ‖h y‖ * ‖f‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_apply_le _ _ _)
        (norm_nonneg _)

variable (p) in
/-- **Twisted convolution** by an `L¹` coefficient kernel on `Lp A p μ` (`1 ≤ p < ∞`), defined as
the `Lp`-valued Bochner integral `h ⋆ f = ∫ y, h y • translateLp y f dμ(y)`. -/
def convolutionLp (hp : p ≠ ∞) : Lp A 1 μ →L[ℂ] Lp A p μ →L[ℂ] Lp A p μ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ
      (fun (h : Lp A 1 μ) (f : Lp A p μ) =>
        ∫ y, (ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f) ∂μ)
      (fun h₁ h₂ f => by
        rw [← integral_add (α.integrable_mul_translateLp μ hp (L1.integrable_coeFn h₁) f)
          (α.integrable_mul_translateLp μ hp (L1.integrable_coeFn h₂) f)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add h₁ h₂] with y hy
        rw [hy, Pi.add_apply, map_add, ContinuousLinearMap.add_compLp])
      (fun c h f => by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c h] with y hy
        rw [hy, Pi.smul_apply, map_smul, ContinuousLinearMap.smul_compLp])
      (fun h f₁ f₂ => by
        rw [← integral_add (α.integrable_mul_translateLp μ hp (L1.integrable_coeFn h) f₁)
          (α.integrable_mul_translateLp μ hp (L1.integrable_coeFn h) f₂)]
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

/-- Twisted convolution has bilinear operator norm at most one. -/
theorem norm_convolutionLp_le : ‖α.convolutionLp μ p hp‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun h f => by
    simpa using α.norm_convolutionLp_apply_le h f

/-- Left multiplication by a coefficient `a ∈ A` commutes with twisted convolution in the first
argument. -/
theorem mul_compLp_convolutionLp (a : A) (h : Lp A 1 μ) (f : Lp A p μ) :
    (ContinuousLinearMap.mul ℂ A a).compLp (α.convolutionLp μ p hp h f) =
      α.convolutionLp μ p hp ((ContinuousLinearMap.mul ℂ A a).compLp h) f := by
  let L : Lp A p μ →L[ℂ] Lp A p μ := (ContinuousLinearMap.mul ℂ A a).compLpL p μ
  have hL (u : Lp A p μ) : L u = (ContinuousLinearMap.mul ℂ A a).compLp u := rfl
  have hcomm := L.integral_comp_comm
    (α.integrable_mul_translateLp μ hp (L1.integrable_coeFn h) f)
  rw [← hL, convolutionLp_apply, ← hcomm, convolutionLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ A a).coeFn_compLp h] with y hy
  rw [hL, hy]
  refine Lp.ext ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ A a).coeFn_compLp
      ((ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f)),
    (ContinuousLinearMap.mul ℂ A (h y)).coeFn_compLp (α.translateLp μ p y f),
    (ContinuousLinearMap.mul ℂ A (a * h y)).coeFn_compLp (α.translateLp μ p y f)]
    with s h₁ h₂ h₃
  simp [h₁, h₂, h₃, mul_assoc]

/-- Twisted left translation commutes with twisted convolution:
`translateLp g (h ⋆ f) = (translateLp g h) ⋆ f`. -/
theorem translateLp_convolutionLp (g : G) (h : Lp A 1 μ) (f : Lp A p μ) :
    α.translateLp μ p g (α.convolutionLp μ p hp h f) =
      α.convolutionLp μ p hp (α.translateLp μ 1 g h) f := by
  let L : Lp A p μ →L[ℂ] Lp A p μ :=
    (α.translateLp μ p g).toContinuousLinearEquiv.toContinuousLinearMap
  have hL (u : Lp A p μ) : L u = α.translateLp μ p g u := rfl
  have hcomm := L.integral_comp_comm
    (α.integrable_mul_translateLp μ hp (L1.integrable_coeFn h) f)
  rw [← hL, convolutionLp_apply, ← hcomm, convolutionLp_apply, ← integral_mul_left_eq_self
    (fun y => (ContinuousLinearMap.mul ℂ A (α.translateLp μ 1 g h y)).compLp
      (α.translateLp μ p y f)) g]
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_mul_left μ g).quasiMeasurePreserving.ae
    (α.coeFn_translateLp g h)] with y hy
  rw [hL, hy, inv_mul_cancel_left, α.translateLp_mul_compLp, map_mul, LinearIsometryEquiv.coe_mul,
    Function.comp_apply]

/-- **Associativity of twisted convolution**: `(h ⋆ k) ⋆ f = h ⋆ (k ⋆ f)`. -/
theorem convolutionLp_assoc (h k : Lp A 1 μ) (f : Lp A p μ) :
    α.convolutionLp μ p hp (α.convolutionLp μ 1 ENNReal.one_ne_top h k) f =
      α.convolutionLp μ p hp h (α.convolutionLp μ p hp k f) := by
  have hint := ((α.convolutionLp μ p hp).flip f).integral_comp_comm
    (α.integrable_mul_translateLp μ ENNReal.one_ne_top (L1.integrable_coeFn h) k)
  simp only [ContinuousLinearMap.flip_apply, ← α.mul_compLp_convolutionLp,
    ← α.translateLp_convolutionLp] at hint
  rw [α.convolutionLp_apply (hp := ENNReal.one_ne_top) h k, ← hint]
  exact (α.convolutionLp_apply h _).symm

/-- **Scalar trivial-action comparison**: for the trivial action on `ℂ`, twisted convolution
`convolutionLp` agrees with scalar group convolution `MeasureTheory.Lp.convolutionL`. -/
@[simp]
theorem trivial_convolutionLp :
    (trivial (G := G) (A := ℂ)).convolutionLp μ p hp = Lp.convolutionL μ p hp := by
  ext h f : 2
  rw [convolutionLp_apply, Lp.convolutionL_apply]
  refine integral_congr_ae (.of_forall fun y => ?_)
  dsimp only
  rw [trivial_translateLp]
  refine Lp.ext ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ (h y)).coeFn_compLp (Lp.leftTranslation μ p ℂ y f),
    Lp.coeFn_smul (h y) (Lp.leftTranslation μ p ℂ y f)] with s h₁ h₂
  simp [h₁, h₂]

/-- On compactly supported continuous coefficient functions, `convolutionLp` is represented almost
everywhere by the pointwise twisted convolution `s ↦ ∫ r, f r * α r (g (r⁻¹ * s)) dμ`. -/
theorem convolutionLp_toL1_cc_ae_eq (f g : C_c(G, A)) :
    α.convolutionLp μ 1 ENNReal.one_ne_top (f.integrable.toL1 f) (g.integrable.toL1 g) =ᵐ[μ]
      α.convolution μ f g := by
  have hfi : Integrable (f : G → A) μ := f.integrable
  have hgi : Integrable (g : G → A) μ := g.integrable
  have hint : Integrable (α.convolution μ f g : G → A) μ := (α.convolution μ f g).integrable
  refine (L1.integrable_coeFn _).ae_eq_of_forall_setIntegral_eq _ _ hint fun s _ _ => ?_
  let T : Lp A 1 μ →L[ℂ] A :=
    (L1.integralCLM' (μ := μ.restrict s) ℂ).comp (LpToLpRestrictCLM G A ℂ μ 1 s)
  have hT (u : Lp A 1 μ) : T u = ∫ x in s, u x ∂μ := by
    rw [ContinuousLinearMap.comp_apply, ← L1.integral_eq', L1.integral_eq_integral]
    exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℂ s u)
  have hL (r : G) :
      ∫ x in s, ((ContinuousLinearMap.mul ℂ A (f r)).compLp
        (α.translateLp μ 1 r (hgi.toL1 g))) x ∂μ =
      ∫ x in s, f r * α r (g (r⁻¹ * x)) ∂μ := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [(ContinuousLinearMap.mul ℂ A (f r)).coeFn_compLp
        (α.translateLp μ 1 r (hgi.toL1 g)),
      α.coeFn_translateLp r (hgi.toL1 g),
      (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae hgi.coeFn_toL1]
      with x h₁ h₂ h₃
    rw [h₁, ContinuousLinearMap.mul_apply', h₂, h₃]
  rw [← hT, α.convolutionLp_toL1 hfi,
    ← T.integral_comp_comm (α.integrable_mul_translateLp μ ENNReal.one_ne_top hfi _)]
  simp_rw [hT, hL, α.convolution_apply]
  let F : G → G → A := fun x r => f r * α r (g (r⁻¹ * x))
  have hFc : Continuous (uncurry F) := by
    rw [uncurry_def]
    fun_prop
  have hFs : HasCompactSupport (uncurry F) :=
    hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport
      fun x r hxr =>
        ⟨subset_tsupport _ (mem_support.2 (left_ne_zero_of_mul hxr)),
          subset_tsupport _ (mem_support.2 fun hg =>
            right_ne_zero_of_mul hxr (by simp [hg]))⟩
  exact integral_integral_swap_of_hasCompactSupport (f := fun r x => F x r)
    (hFc.comp continuous_swap) (hFs.comp_homeomorph (Homeomorph.prodComm G G))

/-- On `ConvolutionAlgebra α μ`, `toL1` intertwines twisted multiplication with
`convolutionLp`. -/
theorem convolutionLp_toL1_ofConv (f g : ConvolutionAlgebra α μ) :
    α.convolutionLp μ 1 ENNReal.one_ne_top (ConvolutionAlgebra.toL1 f)
        (ConvolutionAlgebra.toL1 g) =
      ConvolutionAlgebra.toL1 (f * g) := by
  have hf : ConvolutionAlgebra.toL1 f = f.ofConv.integrable.toL1 f.ofConv :=
    Lp.ext <| (ConvolutionAlgebra.coeFn_toL1 f).trans f.ofConv.integrable.coeFn_toL1.symm
  have hg : ConvolutionAlgebra.toL1 g = g.ofConv.integrable.toL1 g.ofConv :=
    Lp.ext <| (ConvolutionAlgebra.coeFn_toL1 g).trans g.ofConv.integrable.coeFn_toL1.symm
  rw [hf, hg]
  refine Lp.ext ((α.convolutionLp_toL1_cc_ae_eq f.ofConv g.ofConv).trans ?_)
  simpa only [ConvolutionAlgebra.ofConv_mul] using (ConvolutionAlgebra.coeFn_toL1 (f * g)).symm

end ConvolutionLp

/-! ### Isometric identification of the `L¹` completion with Bochner `L¹` -/

namespace ConvolutionAlgebra

variable {G A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A]

section FromCompletion

variable [OpensMeasurableSpace G] (α : CStarAction G A) (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ]

/-- The linear isometry from the `L¹` completion `Completion (ConvolutionAlgebra α μ)` into the
Bochner space `Lp A 1 μ`, extending `ConvolutionAlgebra.toL1LI`. -/
def toL1FromCompletion : Completion (ConvolutionAlgebra α μ) →ₗᵢ[ℂ] Lp A 1 μ :=
  (toL1LI α μ).fromCompletion

variable {α μ}

/-- `toL1` on `toConv f` is the Bochner `L¹` class of `f : C_c(G, A)`. -/
@[simp]
theorem toL1_toConv (f : C_c(G, A)) :
    toL1 (toConv f : ConvolutionAlgebra α μ) = f.integrable.toL1 f :=
  Lp.ext <| (coeFn_toL1 (toConv f)).trans f.integrable.coeFn_toL1.symm

/-- `toL1` preserves norms. -/
@[simp]
theorem norm_toL1 (f : ConvolutionAlgebra α μ) : ‖toL1 f‖ = ‖f‖ := by
  rw [← toL1LI_apply, LinearIsometry.norm_map]

/-- On compactly supported elements, `toL1FromCompletion` agrees with `toL1`. -/
@[simp]
theorem toL1FromCompletion_coe (f : ConvolutionAlgebra α μ) :
    toL1FromCompletion α μ f = toL1 f :=
  ((toL1LI α μ).fromCompletion_apply_coe f).trans (toL1LI_apply f)

/-- `toL1FromCompletion` as a continuous linear map is the completion extension of `toL1LI`. -/
@[simp]
theorem toContinuousLinearMap_toL1FromCompletion :
    (toL1FromCompletion α μ).toContinuousLinearMap =
      (toL1LI α μ).toContinuousLinearMap.fromCompletion :=
  (rfl)

/-- `toL1FromCompletion` intertwines the completion's multiplication with `convolutionLp`. -/
theorem toL1FromCompletion_mul [IsTopologicalGroup G] [BorelSpace G] [μ.IsMulLeftInvariant]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (x y : Completion (ConvolutionAlgebra α μ)) :
    toL1FromCompletion α μ (x * y) =
      α.convolutionLp μ 1 ENNReal.one_ne_top (toL1FromCompletion α μ x)
        (toL1FromCompletion α μ y) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((toL1FromCompletion α μ).continuous.comp
        (continuous_mul.comp (continuous_id.prodMk continuous_const)))
      (((α.convolutionLp μ 1 ENNReal.one_ne_top).flip (toL1FromCompletion α μ y)).continuous.comp
        (toL1FromCompletion α μ).continuous)
  | ih f =>
    induction y using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        ((toL1FromCompletion α μ).continuous.comp
          (continuous_mul.comp (continuous_const.prodMk continuous_id)))
        ((α.convolutionLp μ 1 ENNReal.one_ne_top (toL1FromCompletion α μ f)).continuous.comp
          (toL1FromCompletion α μ).continuous)
    | ih g =>
      simp only [← Completion.coe_mul', toL1FromCompletion_coe, α.convolutionLp_toL1_ofConv]

end FromCompletion

section CompletionEquivLp

variable [R1Space G] [WeaklyLocallyCompactSpace G] [BorelSpace G]
  (α : CStarAction G A) (μ : Measure G) [μ.Regular]

/-- For a regular measure on a weakly locally compact `R₁` group, `toL1` has dense range in
`Lp A 1 μ`. -/
theorem denseRange_toL1 : DenseRange (toL1 (α := α) (μ := μ)) := by
  refine (Lp.dense_setOf_continuous_hasCompactSupport (E := A) (μ := μ)
    ENNReal.one_ne_top).mono ?_
  rintro u ⟨f, hfc, hfs, hu⟩
  refine ⟨toConv ⟨⟨f, hfc⟩, hfs⟩, Lp.ext ?_⟩
  exact (coeFn_toL1 _).trans hu.symm

/-- For a regular measure on a weakly locally compact `R₁` group, `toL1FromCompletion` is
surjective onto `Lp A 1 μ`. -/
theorem surjective_toL1FromCompletion : Function.Surjective (toL1FromCompletion α μ) := by
  rw [← Set.range_eq_univ]
  have hd : DenseRange (toL1FromCompletion α μ) :=
    (denseRange_toL1 α μ).mono (by
      rintro _ ⟨f, rfl⟩
      exact ⟨f, toL1FromCompletion_coe f⟩)
  exact (toL1FromCompletion α μ).isometry.isClosedEmbedding.isClosed_range.closure_eq ▸
    hd.closure_eq

/-- **Bochner `L¹` realization of the twisted `L¹` completion**: for a regular measure on a weakly
locally compact `R₁` group, `Completion (ConvolutionAlgebra α μ)` is linearly isometric to
`Lp A 1 μ`. -/
def completionEquivLp : Completion (ConvolutionAlgebra α μ) ≃ₗᵢ[ℂ] Lp A 1 μ :=
  LinearIsometryEquiv.ofSurjective (toL1FromCompletion α μ) (surjective_toL1FromCompletion α μ)

variable {α μ}

/-- The forward map of `completionEquivLp` is `toL1FromCompletion`. -/
theorem coe_completionEquivLp :
    ⇑(completionEquivLp α μ) = toL1FromCompletion α μ :=
  LinearIsometryEquiv.coe_ofSurjective _ _

/-- Applying `completionEquivLp` agrees with `toL1FromCompletion`. -/
theorem completionEquivLp_apply (x : Completion (ConvolutionAlgebra α μ)) :
    completionEquivLp α μ x = toL1FromCompletion α μ x :=
  (rfl)

/-- On compactly supported elements, `completionEquivLp` is `toL1`. -/
@[simp]
theorem completionEquivLp_coe (f : ConvolutionAlgebra α μ) :
    completionEquivLp α μ f = toL1 f :=
  toL1FromCompletion_coe f

/-- The inverse of `completionEquivLp` sends `toL1 f` back to the completion class of `f`. -/
@[simp]
theorem completionEquivLp_symm_toL1 (f : ConvolutionAlgebra α μ) :
    (completionEquivLp α μ).symm (toL1 f) = f :=
  (completionEquivLp α μ).symm_apply_eq.2 (completionEquivLp_coe f).symm

/-- The inverse of `completionEquivLp` sends the `L¹` class of `f : C_c(G, A)` to `toConv f`. -/
@[simp]
theorem completionEquivLp_symm_toL1_cc (f : C_c(G, A)) :
    (completionEquivLp α μ).symm (f.integrable.toL1 f) = (toConv f : ConvolutionAlgebra α μ) := by
  rw [← toL1_toConv, completionEquivLp_symm_toL1]

/-- `completionEquivLp` transports multiplication on the completion to `convolutionLp`. -/
theorem completionEquivLp_mul [IsTopologicalGroup G] [μ.IsMulLeftInvariant]
    (x y : Completion (ConvolutionAlgebra α μ)) :
    completionEquivLp α μ (x * y) =
      α.convolutionLp μ 1 ENNReal.one_ne_top (completionEquivLp α μ x)
        (completionEquivLp α μ y) := by
  simp only [completionEquivLp_apply, toL1FromCompletion_mul]

/-- The inverse of `completionEquivLp` turns `convolutionLp` into the completion's product. -/
theorem completionEquivLp_symm_convolutionLp [IsTopologicalGroup G] [μ.IsMulLeftInvariant]
    (u v : Lp A 1 μ) :
    (completionEquivLp α μ).symm (α.convolutionLp μ 1 ENNReal.one_ne_top u v) =
      (completionEquivLp α μ).symm u * (completionEquivLp α μ).symm v :=
  (completionEquivLp α μ).injective <| by
    simp [completionEquivLp_mul]

variable (α) in
/-- Every class in `Lp A 1 μ` is the sum of an absolutely convergent series of compactly supported
convolution elements. -/
theorem exists_hasSum_toL1 (u : Lp A 1 μ) :
    ∃ φ : ℕ → ConvolutionAlgebra α μ,
      HasSum (fun n => toL1 (φ n)) u ∧ Summable fun n => ‖φ n‖ := by
  choose h hh using fun n : ℕ =>
    Metric.denseRange_iff.1 (denseRange_toL1 α μ) u ((1 / 2 : ℝ) ^ n) (by positivity)
  let φ : ℕ → ConvolutionAlgebra α μ := fun
    | 0 => h 0
    | n + 1 => h (n + 1) - h n
  have hsum_eq (n : ℕ) : ∑ k ∈ Finset.range (n + 1), φ k = h n := by
    induction n with
    | zero => simp [φ]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [φ]
  have hnorm_summable : Summable fun n => ‖φ n‖ := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (summable_geometric_two.mul_left (3 / 2 : ℝ))
    have hdist : ‖φ (n + 1)‖ = dist (toL1 (h (n + 1))) (toL1 (h n)) := by
      simp [φ, dist_eq_norm, ← map_sub]
    calc
      ‖φ (n + 1)‖ ≤ dist (toL1 (h (n + 1))) u + dist u (toL1 (h n)) :=
        hdist ▸ dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) ^ (n + 1) + (1 / 2 : ℝ) ^ n := by
        rw [dist_comm (toL1 (h (n + 1))) u]
        exact add_le_add (hh (n + 1)).le (hh n).le
      _ = 3 / 2 * (1 / 2 : ℝ) ^ n := by ring
  have hL1_summable : Summable fun n => toL1 (φ n) :=
    .of_norm (by simpa only [norm_toL1] using hnorm_summable)
  have htendsto : Tendsto (fun n => toL1 (h n)) atTop (𝓝 u) :=
    tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun _ => dist_nonneg)
      (fun n => (dist_comm (toL1 (h n)) u).le.trans (hh n).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num))
  have hpartial : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), toL1 (φ k)) atTop (𝓝 u) := by
    simpa only [← map_sum, hsum_eq] using htendsto
  have hu : ∑' n, toL1 (φ n) = u :=
    tendsto_nhds_unique (hL1_summable.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
      hpartial
  exact ⟨φ, hu ▸ hL1_summable.hasSum, hnorm_summable⟩

end CompletionEquivLp

end ConvolutionAlgebra

/-! ### Twisted involution and pointwise `L¹` convolution on locally compact groups -/

section HaarRegular

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- The **twisted involution** `u ↦ (s ↦ c(s) • α s (star (u s⁻¹)))` on `Lp A 1 μ` for a regular
Haar measure `μ`, as a conjugate-linear isometric equivalence. -/
def twistedInvolutionLp : Lp A 1 μ ≃ₗᵢ⋆[ℂ] Lp A 1 μ where
  toFun u := ConvolutionAlgebra.completionEquivLp α μ
    (star ((ConvolutionAlgebra.completionEquivLp α μ).symm u))
  invFun u := ConvolutionAlgebra.completionEquivLp α μ
    (star ((ConvolutionAlgebra.completionEquivLp α μ).symm u))
  left_inv u := by simp
  right_inv u := by simp
  map_add' u v := by simp [star_add]
  map_smul' c u := by simp [star_smul]
  norm_map' u := by simp

variable {α μ}

/-- `twistedInvolutionLp` transports the star operation of `Completion (ConvolutionAlgebra α μ)`
along `completionEquivLp`. -/
theorem twistedInvolutionLp_apply (u : Lp A 1 μ) :
    α.twistedInvolutionLp μ u =
      ConvolutionAlgebra.completionEquivLp α μ
        (star ((ConvolutionAlgebra.completionEquivLp α μ).symm u)) :=
  (rfl)

/-- Applying `twistedInvolutionLp` twice recovers the original `L¹` class. -/
@[simp]
theorem twistedInvolutionLp_twistedInvolutionLp (u : Lp A 1 μ) :
    α.twistedInvolutionLp μ (α.twistedInvolutionLp μ u) = u :=
  (α.twistedInvolutionLp μ).left_inv u

/-- `twistedInvolutionLp` is its own inverse. -/
@[simp]
theorem twistedInvolutionLp_symm :
    (α.twistedInvolutionLp μ).symm = α.twistedInvolutionLp μ :=
  (rfl)

/-- `completionEquivLp` intertwines the completion's star with `twistedInvolutionLp`. -/
@[simp]
theorem ConvolutionAlgebra.completionEquivLp_star (x : Completion (ConvolutionAlgebra α μ)) :
    ConvolutionAlgebra.completionEquivLp α μ (star x) =
      α.twistedInvolutionLp μ (ConvolutionAlgebra.completionEquivLp α μ x) := by
  rw [twistedInvolutionLp_apply, LinearIsometryEquiv.symm_apply_apply]

/-- The inverse of `completionEquivLp` intertwines `twistedInvolutionLp` with star. -/
@[simp]
theorem ConvolutionAlgebra.completionEquivLp_symm_twistedInvolutionLp (u : Lp A 1 μ) :
    (ConvolutionAlgebra.completionEquivLp α μ).symm (α.twistedInvolutionLp μ u) =
      star ((ConvolutionAlgebra.completionEquivLp α μ).symm u) := by
  rw [twistedInvolutionLp_apply, LinearIsometryEquiv.symm_apply_apply]

/-- On compactly supported convolution elements, `twistedInvolutionLp` agrees with the
compact-support star operation. -/
@[simp]
theorem twistedInvolutionLp_toL1_ofConv (f : ConvolutionAlgebra α μ) :
    α.twistedInvolutionLp μ (ConvolutionAlgebra.toL1 f) = ConvolutionAlgebra.toL1 (star f) := by
  rw [← ConvolutionAlgebra.completionEquivLp_coe, ← ConvolutionAlgebra.completionEquivLp_star,
    ← Completion.coe_star, ConvolutionAlgebra.completionEquivLp_coe]

/-- On `C_c(G, A)`, `twistedInvolutionLp` agrees with `CStarAction.twistedInvolution`. -/
theorem twistedInvolutionLp_toL1_cc (f : C_c(G, A)) :
    α.twistedInvolutionLp μ (f.integrable.toL1 f) =
      (α.twistedInvolution f).integrable.toL1 (α.twistedInvolution f) := by
  rw [← ConvolutionAlgebra.toL1_toConv (α := α) (μ := μ), twistedInvolutionLp_toL1_ofConv,
    ← ConvolutionAlgebra.toConv_twistedInvolution, ConvolutionAlgebra.toL1_toConv]

/-- `twistedInvolutionLp` reverses twisted `L¹` convolution:
`(u ⋆ v)* = v* ⋆ u*`. -/
theorem twistedInvolutionLp_convolutionLp (u v : Lp A 1 μ) :
    α.twistedInvolutionLp μ (α.convolutionLp μ 1 ENNReal.one_ne_top u v) =
      α.convolutionLp μ 1 ENNReal.one_ne_top (α.twistedInvolutionLp μ v)
        (α.twistedInvolutionLp μ u) := by
  obtain ⟨x, rfl⟩ := (ConvolutionAlgebra.completionEquivLp α μ).surjective u
  obtain ⟨y, rfl⟩ := (ConvolutionAlgebra.completionEquivLp α μ).surjective v
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((α.twistedInvolutionLp μ).continuous.comp
        (((α.convolutionLp μ 1 ENNReal.one_ne_top).flip _).continuous.comp
          (ConvolutionAlgebra.completionEquivLp α μ).continuous))
      ((α.convolutionLp μ 1 ENNReal.one_ne_top _).continuous.comp
        ((α.twistedInvolutionLp μ).continuous.comp
          (ConvolutionAlgebra.completionEquivLp α μ).continuous))
  | ih f =>
    induction y using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        ((α.twistedInvolutionLp μ).continuous.comp
          ((α.convolutionLp μ 1 ENNReal.one_ne_top _).continuous.comp
            (ConvolutionAlgebra.completionEquivLp α μ).continuous))
        (((α.convolutionLp μ 1 ENNReal.one_ne_top).flip _).continuous.comp
          ((α.twistedInvolutionLp μ).continuous.comp
            (ConvolutionAlgebra.completionEquivLp α μ).continuous))
    | ih g =>
      simp only [ConvolutionAlgebra.completionEquivLp_coe, α.convolutionLp_toL1_ofConv,
        twistedInvolutionLp_toL1_ofConv, star_mul]

omit [LocallyCompactSpace G] [μ.Regular] in
/-- An absolutely norm-summable series in `ConvolutionAlgebra α μ` whose `L¹` classes sum to `u`
converges pointwise almost everywhere, with summable norms, to `u`. -/
private theorem ae_hasSum_ofConv_of_hasSum_toL1 {ι : Type*} [Countable ι]
    {φ : ι → ConvolutionAlgebra α μ} {u : Lp A 1 μ}
    (hsum : HasSum (fun i => ConvolutionAlgebra.toL1 (φ i)) u)
    (hnorm : Summable fun i => ‖φ i‖) :
    ∀ᵐ r ∂μ, HasSum (fun i => (φ i).ofConv r) (u r) ∧ Summable fun i => ‖(φ i).ofConv r‖ := by
  have heNorm : ∑' i, ‖ConvolutionAlgebra.toL1 (φ i)‖ₑ ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 <| by
      simpa only [coe_nnNorm, ConvolutionAlgebra.norm_toL1] using hnorm
  filter_upwards [hsum.tsum_eq ▸ Lp.hasSum_coeFn_tsum heNorm,
    summable_norm_of_tsum_eLpNorm_ne_top le_rfl (by simpa [Lp.eNorm_def] using heNorm),
    ae_all_iff.2 fun i => (ConvolutionAlgebra.coeFn_toL1 (φ i)).mono fun _ h => h]
    with r hr hnr hcoe
  exact ⟨by simpa only [hcoe] using hr, by simpa only [hcoe] using hnr⟩

/-- **Pointwise almost-everywhere formula for `twistedInvolutionLp`**: for every `u ∈ Lp A 1 μ`,
`(α.twistedInvolutionLp μ u) s = c(s) • α s (star (u s⁻¹))` almost everywhere, where `c` is the
modular character. -/
theorem coeFn_twistedInvolutionLp (u : Lp A 1 μ) :
    α.twistedInvolutionLp μ u =ᵐ[μ]
      fun s => ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star (u s⁻¹)) := by
  obtain ⟨φ, hφ_sum, hφ_norm⟩ := ConvolutionAlgebra.exists_hasSum_toL1 α u
  have hstar_sum :
      HasSum (fun n => ConvolutionAlgebra.toL1 (star (φ n))) (α.twistedInvolutionLp μ u) := by
    simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      twistedInvolutionLp_toL1_ofConv] using
      (α.twistedInvolutionLp μ).toLinearIsometry.toContinuousLinearMap.hasSum hφ_sum
  have hstar_norm : Summable fun n => ‖star (φ n)‖ := by
    simpa only [ConvolutionAlgebra.norm_star] using hφ_norm
  filter_upwards [(Measure.quasiMeasurePreserving_inv_of_regular μ).ae
      (α.ae_hasSum_ofConv_of_hasSum_toL1 hφ_sum hφ_norm),
    α.ae_hasSum_ofConv_of_hasSum_toL1 hstar_sum hstar_norm] with s ⟨hu_inv, _⟩ ⟨hst, _⟩
  let ψ : A →+ A :=
    { toFun a := ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star a)
      map_zero' := by simp
      map_add' a b := by simp [smul_add] }
  have hψ_cont : Continuous ψ :=
    continuous_const.smul ((StarAlgEquiv.isometry (α s)).continuous.comp continuous_star)
  exact hst.unique (by simpa [ψ, Function.comp_def] using hu_inv.map ψ hψ_cont)

/-- For the trivial C⋆-action on `ℂ`, `twistedInvolutionLp` is conjugate modular inversion
`star (Lp.modularInversion μ 1 ℂ u)`. -/
@[simp]
theorem trivial_twistedInvolutionLp (u : Lp ℂ 1 μ) :
    (trivial (G := G) (A := ℂ)).twistedInvolutionLp μ u =
      star (Lp.modularInversion μ 1 ℂ u) := by
  refine Lp.ext ?_
  filter_upwards [(trivial (G := G) (A := ℂ)).coeFn_twistedInvolutionLp u,
    Lp.coeFn_star (Lp.modularInversion μ 1 ℂ u),
    Lp.coeFn_modularInversion (𝕜 := ℂ) u] with s h₁ h₂ h₃
  rw [h₁, h₂, Pi.star_apply, h₃]
  simp [Complex.real_smul]

omit [LocallyCompactSpace G] [μ.Regular] in
/-- The scalar norm convolution of two compactly supported coefficient functions has `L¹` norm equal
to the product of their `L¹` norms. -/
private theorem eLpNorm_integral_norm_convolution_eq (f g : ConvolutionAlgebra α μ) :
    eLpNorm (fun s => ∫ r, ‖f.ofConv r‖ * ‖g.ofConv (r⁻¹ * s)‖ ∂μ) 1 μ =
      ENNReal.ofReal (‖f‖ * ‖g‖) := by
  let W : G → ℝ := fun s => ∫ r, ‖f.ofConv r‖ * ‖g.ofConv (r⁻¹ * s)‖ ∂μ
  have hsupp : ∀ s r, ‖f.ofConv r‖ * ‖g.ofConv (r⁻¹ * s)‖ ≠ 0 →
      r ∈ tsupport f.ofConv ∧ r⁻¹ * s ∈ tsupport g.ofConv :=
    fun s r hsr =>
      ⟨subset_tsupport _ (mem_support.2 fun h₁ => hsr (by simp [h₁])),
        subset_tsupport _ (mem_support.2 fun h₂ => hsr (by simp [h₂]))⟩
  have hcont : Continuous (uncurry fun s r => ‖f.ofConv r‖ * ‖g.ofConv (r⁻¹ * s)‖) := by
    rw [uncurry_def]
    fun_prop
  have hWc : Continuous W :=
    continuous_integral_of_compact_support μ f.ofConv.hasCompactSupport hcont
      fun s r h => (hsupp s r h).1
  have hWs : HasCompactSupport W :=
    hasCompactSupport_integral_of_inv_mul_mem μ f.ofConv.hasCompactSupport
      g.ofConv.hasCompactSupport hsupp
  have hWi : Integrable W μ := hWc.integrable_of_hasCompactSupport hWs
  have hW_nonneg (s : G) : 0 ≤ W s :=
    integral_nonneg fun r => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [(memLp_one_iff_integrable.2 hWi).eLpNorm_eq_integral_rpow_norm one_ne_zero
    ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, Real.rpow_one, inv_one, Real.norm_of_nonneg (hW_nonneg _)]
  congr 1
  calc
    ∫ s, W s ∂μ = ∫ r, ∫ s, ‖f.ofConv r‖ * ‖g.ofConv (r⁻¹ * s)‖ ∂μ ∂μ :=
      integral_integral_swap_of_hasCompactSupport hcont
        (hasCompactSupport_uncurry_of_inv_mul_mem f.ofConv.hasCompactSupport
          g.ofConv.hasCompactSupport hsupp)
    _ = ∫ r, ‖f.ofConv r‖ * ∫ s, ‖g.ofConv s‖ ∂μ ∂μ := by
      congr 1 with r
      rw [integral_const_mul, integral_mul_left_eq_self (fun s => ‖g.ofConv s‖) r⁻¹]
    _ = ‖f‖ * ‖g‖ := by
      rw [integral_mul_const, ConvolutionAlgebra.norm_eq_integral_norm,
        ConvolutionAlgebra.norm_eq_integral_norm]

omit [LocallyCompactSpace G] [μ.Regular] in
/-- For norm-summable compact-support series `φ` and `ψ`, the `L¹` norms of the pairwise twisted
convolution integrands are summable at almost every `s`. -/
private theorem ae_summable_integral_norm_of_summable
    {φ ψ : ℕ → ConvolutionAlgebra α μ} (hφ : Summable fun m => ‖φ m‖)
    (hψ : Summable fun n => ‖ψ n‖) :
    ∀ᵐ s ∂μ, Summable fun p : ℕ × ℕ =>
      ∫ r, ‖(φ p.1).ofConv r * α r ((ψ p.2).ofConv (r⁻¹ * s))‖ ∂μ := by
  have hprod : Summable fun p : ℕ × ℕ => ‖φ p.1‖ * ‖ψ p.2‖ :=
    Summable.mul_of_nonneg (f := fun m => ‖φ m‖) (g := fun n => ‖ψ n‖) hφ hψ
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  let W : ℕ × ℕ → G → ℝ := fun p s =>
    ∫ r, ‖(φ p.1).ofConv r‖ * ‖(ψ p.2).ofConv (r⁻¹ * s)‖ ∂μ
  have hW_tsum : ∑' p : ℕ × ℕ, eLpNorm (W p) 1 μ ≠ ∞ := by
    simp_rw [W, α.eLpNorm_integral_norm_convolution_eq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      hprod]
    exact ENNReal.ofReal_ne_top
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top le_rfl hW_tsum] with s hsW
  refine .of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun p => ?_) hsW
  refine (integral_mono (α.integrable_integrand (φ p.1).ofConv (ψ p.2).ofConv μ s).norm ?_
    fun r => ?_).trans (le_abs_self (W p s))
  · have hcont : Continuous fun r => ‖(φ p.1).ofConv r‖ * ‖(ψ p.2).ofConv (r⁻¹ * s)‖ := by
      fun_prop
    exact hcont.integrable_of_hasCompactSupport
      ((φ p.1).ofConv.hasCompactSupport.mono' fun r hr =>
        subset_tsupport _ (mem_support.2 fun h₁ => hr (by simp [h₁])))
  · simpa [StarAlgEquiv.norm_map] using
      norm_mul_le ((φ p.1).ofConv r) (α r ((ψ p.2).ofConv (r⁻¹ * s)))

/-- For norm-summable compact-support approximations of `u` and `v`, the pairwise compact-support
products sum pointwise almost everywhere to `convolutionLp u v`. -/
private theorem ae_hasSum_ofConv_mul_of_hasSum_toL1
    {φ ψ : ℕ → ConvolutionAlgebra α μ} {u v : Lp A 1 μ}
    (hφ_sum : HasSum (fun m => ConvolutionAlgebra.toL1 (φ m)) u)
    (hφ_norm : Summable fun m => ‖φ m‖)
    (hψ_sum : HasSum (fun n => ConvolutionAlgebra.toL1 (ψ n)) v)
    (hψ_norm : Summable fun n => ‖ψ n‖) :
    ∀ᵐ s ∂μ, HasSum (fun p : ℕ × ℕ => (φ p.1 * ψ p.2).ofConv s)
      (α.convolutionLp μ 1 ENNReal.one_ne_top u v s) := by
  have hx_sum : HasSum (fun m => (φ m : Completion (ConvolutionAlgebra α μ)))
      ((ConvolutionAlgebra.completionEquivLp α μ).symm u) := by
    simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      ConvolutionAlgebra.completionEquivLp_symm_toL1] using
      (ConvolutionAlgebra.completionEquivLp α μ).symm.toLinearIsometry.toContinuousLinearMap.hasSum
        hφ_sum
  have hy_sum : HasSum (fun n => (ψ n : Completion (ConvolutionAlgebra α μ)))
      ((ConvolutionAlgebra.completionEquivLp α μ).symm v) := by
    simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      ConvolutionAlgebra.completionEquivLp_symm_toL1] using
      (ConvolutionAlgebra.completionEquivLp α μ).symm.toLinearIsometry.toContinuousLinearMap.hasSum
        hψ_sum
  have hxy_norm : Summable fun p : ℕ × ℕ => ‖(φ p.1 * ψ p.2 : ConvolutionAlgebra α μ)‖ :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_mul_le _ _)
      (Summable.mul_of_nonneg (f := fun m => ‖φ m‖) (g := fun n => ‖ψ n‖) hφ_norm hψ_norm
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
  have hxy_summable : Summable fun p : ℕ × ℕ =>
      ((φ p.1 * ψ p.2 : ConvolutionAlgebra α μ) : Completion (ConvolutionAlgebra α μ)) :=
    .of_norm (by simpa only [Completion.norm_coe] using hxy_norm)
  have hxy_sum : HasSum (fun p : ℕ × ℕ =>
      ((φ p.1 * ψ p.2 : ConvolutionAlgebra α μ) : Completion (ConvolutionAlgebra α μ)))
      ((ConvolutionAlgebra.completionEquivLp α μ).symm u *
        (ConvolutionAlgebra.completionEquivLp α μ).symm v) := by
    simpa only [Completion.coe_mul'] using hx_sum.mul hy_sum
      (by simpa only [← Completion.coe_mul'] using hxy_summable)
  have huv_sum : HasSum (fun p : ℕ × ℕ => ConvolutionAlgebra.toL1 (φ p.1 * ψ p.2))
      (α.convolutionLp μ 1 ENNReal.one_ne_top u v) := by
    simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      ConvolutionAlgebra.completionEquivLp_coe,
      ← ConvolutionAlgebra.completionEquivLp_symm_convolutionLp,
      LinearIsometryEquiv.apply_symm_apply] using
      (ConvolutionAlgebra.completionEquivLp α μ).toLinearIsometry.toContinuousLinearMap.hasSum
        hxy_sum
  exact (α.ae_hasSum_ofConv_of_hasSum_toL1 huv_sum hxy_norm).mono fun _ hs => hs.1

/-- Helper giving both almost-everywhere integrability of the twisted convolution integrand and
almost-everywhere agreement with `convolutionLp` for arbitrary Bochner-integrable functions. -/
private theorem ae_integrable_and_convolutionLp_toL1_ae_eq {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ ∧
      α.convolutionLp μ 1 ENNReal.one_ne_top (hf.toL1 f) (hg.toL1 g) s =
        ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ := by
  obtain ⟨φ, hφ_sum, hφ_norm⟩ := ConvolutionAlgebra.exists_hasSum_toL1 α (hf.toL1 f)
  obtain ⟨ψ, hψ_sum, hψ_norm⟩ := ConvolutionAlgebra.exists_hasSum_toL1 α (hg.toL1 g)
  have hae_f : ∀ᵐ r ∂μ, HasSum (fun m => (φ m).ofConv r) (f r) ∧
      Summable fun m => ‖(φ m).ofConv r‖ := by
    filter_upwards [α.ae_hasSum_ofConv_of_hasSum_toL1 hφ_sum hφ_norm, hf.coeFn_toL1]
      with r ⟨hr, hnr⟩ hfu
    exact ⟨hfu ▸ hr, hnr⟩
  have hae_g : ∀ᵐ t ∂μ, HasSum (fun n => (ψ n).ofConv t) (g t) ∧
      Summable fun n => ‖(ψ n).ofConv t‖ := by
    filter_upwards [α.ae_hasSum_ofConv_of_hasSum_toL1 hψ_sum hψ_norm, hg.coeFn_toL1]
      with t ⟨ht, hnt⟩ hgv
    exact ⟨hgv ▸ ht, hnt⟩
  filter_upwards [α.ae_summable_integral_norm_of_summable hφ_norm hψ_norm,
    α.ae_hasSum_ofConv_mul_of_hasSum_toL1 hφ_sum hφ_norm hψ_sum hψ_norm] with s hh_sum_int hsuv
  let h : ℕ × ℕ → G → A := fun p r => (φ p.1).ofConv r * α r ((ψ p.2).ofConv (r⁻¹ * s))
  have hh_int (p : ℕ × ℕ) : Integrable (h p) μ :=
    α.integrable_integrand (φ p.1).ofConv (ψ p.2).ofConv μ s
  have hae_h : ∀ᵐ r ∂μ, ∑' p : ℕ × ℕ, h p r = f r * α r (g (r⁻¹ * s)) := by
    filter_upwards [hae_f, (Measure.quasiMeasurePreserving_inv_mul_of_regular μ s).ae hae_g]
      with r ⟨hfr, hfnorm⟩ ⟨hgr, hgnorm⟩
    have hαg_sum : HasSum (fun n => α r ((ψ n).ofConv (r⁻¹ * s))) (α r (g (r⁻¹ * s))) := by
      simpa only [toContinuousLinearMap_apply] using (α.toContinuousLinearMap r).hasSum hgr
    have hαg_norm : Summable fun n => ‖α r ((ψ n).ofConv (r⁻¹ * s))‖ := by
      simpa only [StarAlgEquiv.norm_map] using hgnorm
    have hmul_summable : Summable fun p : ℕ × ℕ => h p r :=
      .of_norm <| .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_mul_le _ _)
        (Summable.mul_of_nonneg (f := fun m => ‖(φ m).ofConv r‖)
          (g := fun n => ‖α r ((ψ n).ofConv (r⁻¹ * s))‖) hfnorm hαg_norm
          (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    exact (hfr.mul hαg_sum hmul_summable).tsum_eq
  have heNorm_h : ∑' p : ℕ × ℕ, ‖(hh_int p).toL1 (h p)‖ₑ ≠ ∞ := by
    refine ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 ?_
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hh_sum_int
    rw [coe_nnNorm, L1.norm_eq_integral_norm]
    exact integral_mono_ae (L1.integrable_coeFn _).norm (hh_int p).norm
      (((hh_int p).coeFn_toL1.fun_comp norm).le)
  have hint_tsum : Integrable (fun r => ∑' p : ℕ × ℕ, h p r) μ := by
    refine (L1.integrable_coeFn (∑' p : ℕ × ℕ, (hh_int p).toL1 (h p))).congr ?_
    filter_upwards [Lp.hasSum_coeFn_tsum heNorm_h,
      ae_all_iff.2 fun p : ℕ × ℕ => ((hh_int p).coeFn_toL1).mono fun _ h => h] with r hr hcoe
    exact hr.tsum_eq.symm.trans (tsum_congr fun p => hcoe p)
  refine ⟨hint_tsum.congr hae_h, ?_⟩
  have hint_sum := hasSum_integral_of_summable_integral_norm hh_int hh_sum_int
  have hh_eq (p : ℕ × ℕ) : ∫ r, h p r ∂μ = (φ p.1 * ψ p.2).ofConv s := by
    simp [h, ConvolutionAlgebra.ofConv_mul, α.convolution_apply]
  have hconv_eq : ∫ r, (∑' p : ℕ × ℕ, h p r) ∂μ = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ :=
    integral_congr_ae hae_h
  simp_rw [hh_eq, hconv_eq] at hint_sum
  exact hsuv.unique hint_sum

/-- **Almost-everywhere integrability of the twisted convolution integrand**: for any
Bochner-integrable `f, g : G → A` on a locally compact group with a regular Haar measure,
`r ↦ f r * α r (g (r⁻¹ * s))` is Bochner-integrable for almost every `s : G`. Neither second
countability of `G` nor σ-finiteness of `μ` is needed. -/
theorem ae_integrable_convolution_integrand {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
  (α.ae_integrable_and_convolutionLp_toL1_ae_eq hf hg).mono fun _ hs => hs.1

/-- **Pointwise formula for twisted `L¹` convolution**: for any Bochner-integrable `f, g : G → A`
on a locally compact group with a regular Haar measure, `convolutionLp` of their `L¹` classes is
represented almost everywhere by `s ↦ ∫ r, f r * α r (g (r⁻¹ * s)) dμ`. -/
theorem convolutionLp_toL1_ae_eq {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    α.convolutionLp μ 1 ENNReal.one_ne_top (hf.toL1 f) (hg.toL1 g) =ᵐ[μ]
      fun s => ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ :=
  (α.ae_integrable_and_convolutionLp_toL1_ae_eq hf hg).mono fun _ hs => hs.2

/-- For arbitrary `u, v ∈ Lp A 1 μ` on a locally compact group with a regular Haar measure,
`convolutionLp` is represented almost everywhere by `s ↦ ∫ r, u r * α r (v (r⁻¹ * s)) dμ`. -/
theorem coeFn_convolutionLp (u v : Lp A 1 μ) :
    α.convolutionLp μ 1 ENNReal.one_ne_top u v =ᵐ[μ]
      fun s => ∫ r, u r * α r (v (r⁻¹ * s)) ∂μ := by
  have hu : (L1.integrable_coeFn u).toL1 u = u := Lp.ext (L1.integrable_coeFn u).coeFn_toL1
  have hv : (L1.integrable_coeFn v).toL1 v = v := Lp.ext (L1.integrable_coeFn v).coeFn_toL1
  have h := α.convolutionLp_toL1_ae_eq (L1.integrable_coeFn u) (L1.integrable_coeFn v)
  rwa [hu, hv] at h

end HaarRegular

/-! ### Equivariant functoriality on Bochner `Lᵖ` -/

namespace Hom

variable {G A B C : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}

/-- An equivariant C⋆-algebra homomorphism viewed as a continuous complex linear map. -/
private def toCLM (φ : Hom α β) : A →L[ℂ] B where
  toFun := φ
  map_add' := map_add φ
  map_smul' := map_smul φ
  cont := map_continuous φ

section MapLp

variable [MeasurableSpace G] (μ : Measure G) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Pointwise application of an equivariant C⋆-algebra homomorphism `φ : Hom α β` on `Lp A p μ`,
as a contractive continuous linear map `Lp A p μ →L[ℂ] Lp B p μ`. -/
def mapLp (φ : Hom α β) : Lp A p μ →L[ℂ] Lp B p μ :=
  φ.toCLM.compLpL p μ

variable {μ p}

/-- Pointwise almost-everywhere formula for `Hom.mapLp`. -/
theorem coeFn_mapLp (φ : Hom α β) (u : Lp A p μ) :
    φ.mapLp μ p u =ᵐ[μ] fun s => φ (u s) :=
  φ.toCLM.coeFn_compLpL u

/-- `Hom.mapLp` is a contraction: `‖φ.mapLp μ p‖ ≤ 1`. -/
theorem norm_mapLp_le (φ : Hom α β) : ‖φ.mapLp μ p‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  refine (φ.toCLM.norm_compLp_le u).trans ?_
  have hnorm : ‖φ.toCLM‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
      simpa [toCLM] using NonUnitalStarAlgHom.norm_apply_le φ a
  simpa using mul_le_mul_of_nonneg_right hnorm (norm_nonneg u)

/-- The identity equivariant homomorphism induces the identity on `Lp A p μ`. -/
@[simp]
theorem mapLp_id : (Hom.id α).mapLp μ p = ContinuousLinearMap.id ℂ (Lp A p μ) := by
  ext1 u
  refine Lp.ext ?_
  filter_upwards [(Hom.id α).coeFn_mapLp u] with s hs
  simpa using hs

/-- `Hom.mapLp` preserves composition of equivariant homomorphisms. -/
@[simp]
theorem mapLp_comp (ψ : Hom β γ) (φ : Hom α β) :
    (ψ.comp φ).mapLp μ p = (ψ.mapLp μ p).comp (φ.mapLp μ p) := by
  ext1 u
  refine Lp.ext ?_
  filter_upwards [(ψ.comp φ).coeFn_mapLp u, ψ.coeFn_mapLp (φ.mapLp μ p u), φ.coeFn_mapLp u]
    with s h₁ h₂ h₃
  simp [h₁, h₂, h₃]

/-- `Hom.mapLp` intertwines twisted left translation `translateLp`. -/
theorem mapLp_translateLp [MeasurableMul G] [μ.IsMulLeftInvariant] (φ : Hom α β) (r : G)
    (u : Lp A p μ) :
    φ.mapLp μ p (α.translateLp μ p r u) = β.translateLp μ p r (φ.mapLp μ p u) := by
  refine Lp.ext ?_
  filter_upwards [φ.coeFn_mapLp (α.translateLp μ p r u), α.coeFn_translateLp r u,
    β.coeFn_translateLp r (φ.mapLp μ p u),
    (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae (φ.coeFn_mapLp u)]
    with s h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

/-- `Hom.mapLp` intertwines twisted Bochner convolution `convolutionLp`. -/
theorem mapLp_convolutionLp [IsTopologicalGroup G] [BorelSpace G] [μ.IsMulLeftInvariant]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] (hp : p ≠ ∞) (φ : Hom α β)
    (h : Lp A 1 μ) (f : Lp A p μ) :
    φ.mapLp μ p (α.convolutionLp μ p hp h f) =
      β.convolutionLp μ p hp (φ.mapLp μ 1 h) (φ.mapLp μ p f) := by
  rw [α.convolutionLp_apply,
    ← (φ.mapLp μ p).integral_comp_comm
      (α.integrable_mul_translateLp μ hp (L1.integrable_coeFn h) f),
    β.convolutionLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [φ.coeFn_mapLp h] with y hy
  rw [hy, ← φ.mapLp_translateLp y f]
  refine Lp.ext ?_
  filter_upwards [φ.coeFn_mapLp
      ((ContinuousLinearMap.mul ℂ A (h y)).compLp (α.translateLp μ p y f)),
    (ContinuousLinearMap.mul ℂ A (h y)).coeFn_compLp (α.translateLp μ p y f),
    (ContinuousLinearMap.mul ℂ B (φ (h y))).coeFn_compLp
      (φ.mapLp μ p (α.translateLp μ p y f)),
    φ.coeFn_mapLp (α.translateLp μ p y f)] with s h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

end MapLp

/-- `toL1` intertwines `Hom.convolutionMap` with `Hom.mapLp`. -/
theorem toL1_convolutionMap [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (φ : Hom α β) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (f : ConvolutionAlgebra α μ) :
    ConvolutionAlgebra.toL1 (φ.convolutionMap μ f) =
      φ.mapLp μ 1 (ConvolutionAlgebra.toL1 f) := by
  refine Lp.ext ?_
  filter_upwards [ConvolutionAlgebra.coeFn_toL1 (φ.convolutionMap μ f),
    φ.coeFn_mapLp (ConvolutionAlgebra.toL1 f),
    ConvolutionAlgebra.coeFn_toL1 f] with s h₁ h₂ h₃
  simp [h₁, h₂, h₃]

/-- `toL1FromCompletion` intertwines `Hom.convolutionMapL1` with `Hom.mapLp`. -/
theorem toL1FromCompletion_convolutionMapL1 [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (φ : Hom α β) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (x : Completion (ConvolutionAlgebra α μ)) :
    ConvolutionAlgebra.toL1FromCompletion β μ (φ.convolutionMapL1 μ x) =
      φ.mapLp μ 1 (ConvolutionAlgebra.toL1FromCompletion α μ x) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp [φ.toL1_convolutionMap μ f]

end Hom

end TauCeti.CStarAction
