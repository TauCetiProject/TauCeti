/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Functoriality
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Translate
public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.Analysis.Normed.Group.Completion
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# The Bochner `L¹` realization of the twisted convolution algebra

Let `α` be a point-norm continuous action of a topological group `G` on a possibly nonunital
C⋆-algebra `A`, and let `μ` be a measure on `G`. This file identifies the completion
`UniformSpace.Completion (ConvolutionAlgebra α μ)` isometrically with the Bochner space `Lp A 1 μ`
and develops the twisted `Lᵖ` action, left translation, convolution, involution, and equivariant
functoriality directly on `Lp`, without separability, second countability, or σ-finiteness.

Pointwise coefficient action `CStarAction.actionLp` and, for left-invariant `μ`, twisted left
translation `CStarAction.translateLp` act isometrically on `Lp A p μ` (`1 ≤ p ≤ ∞`) and are
jointly continuous for `p < ∞` under inner regularity. Integrating `y ↦ h y • translateLp y f`
defines the contractive bilinear map `CStarAction.convolutionLp` (`1 ≤ p < ∞`), whose
associativity and equivariance follow by commuting continuous linear maps past the `Lp`-valued
Bochner integral, as in `MeasureTheory.Lp.convolutionL`. For the trivial action on `ℂ`,
`translateLp` and `convolutionLp` reduce to `MeasureTheory.Lp.leftTranslation` and
`MeasureTheory.Lp.convolutionL`.

Extending `ConvolutionAlgebra.toL1LI` gives `ConvolutionAlgebra.toL1FromCompletion`, which becomes
a linear isometric equivalence `ConvolutionAlgebra.completionEquivLp` via
`MeasureTheory.Lp.dense_setOf_continuous_hasCompactSupport` on a weakly locally compact `R₁` group
with regular `μ`. On a locally compact group with regular left-invariant `μ`, this transports the
completion's star to the conjugate-linear isometric involution `CStarAction.twistedInvolutionLp`.
Pointwise almost-everywhere integral formulas are proved in
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.Bochner.Pointwise`.

## Main definitions

* `TauCeti.CStarAction.actionLp`: pointwise isometric action `(r • u) s = α r (u s)` on `Lp A p μ`.
* `TauCeti.CStarAction.translateLp`: twisted left translation `(r • u) s = α r (u (r⁻¹ * s))`.
* `TauCeti.CStarAction.convolutionLp`: twisted convolution `Lp A 1 μ →L[ℂ] Lp A p μ →L[ℂ] Lp A p μ`.
* `TauCeti.CStarAction.ConvolutionAlgebra.toL1FromCompletion`: linear isometry into `Lp A 1 μ`.
* `TauCeti.CStarAction.ConvolutionAlgebra.completionEquivLp`: linear isometric equivalence
  `Completion (ConvolutionAlgebra α μ) ≃ₗᵢ[ℂ] Lp A 1 μ`.
* `TauCeti.CStarAction.twistedInvolutionLp`: twisted conjugate-linear isometric involution on
  `Lp A 1 μ`.
* `TauCeti.CStarAction.Hom.mapLp`: contractive map `Lp A p μ →L[ℂ] Lp B p μ` of an equivariant
  homomorphism.

## Main results

* `TauCeti.CStarAction.continuous_translateLp`: twisted left translation is jointly continuous.
* `TauCeti.CStarAction.convolutionLp_assoc`: `(h ⋆ k) ⋆ f = h ⋆ (k ⋆ f)`.
* `TauCeti.CStarAction.convolutionLp_trivial`: reduction to `MeasureTheory.Lp.convolutionL`.
* `TauCeti.CStarAction.ConvolutionAlgebra.completionEquivLp_mul`,
  `TauCeti.CStarAction.ConvolutionAlgebra.completionEquivLp_star`: isometric Banach ⋆-algebra
  intertwining with `convolutionLp` and `twistedInvolutionLp`.

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
def actionLp : G →* (Lp A p μ ≃ₗᵢ[ℂ] Lp A p μ) := by
  have hcomp (r t : G) :
      (α.toContinuousLinearMap r).comp (α.toContinuousLinearMap t) =
        α.toContinuousLinearMap (r * t) := by ext a; simp [mul_apply]
  have hone : α.toContinuousLinearMap 1 = ContinuousLinearMap.id ℂ A := by ext a; simp
  have hle (g : G) (u : Lp A p μ) : ‖(α.toContinuousLinearMap g).compLp u‖ ≤ ‖u‖ := by
    refine ((α.toContinuousLinearMap g).norm_compLp_le u).trans ?_
    have hnorm : ‖α.toContinuousLinearMap g‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by simp [StarAlgEquiv.norm_map]
    simpa using mul_le_mul_of_nonneg_right hnorm (norm_nonneg u)
  exact
    { toFun r := LinearIsometryEquiv.ofBounds
        { toFun := (α.toContinuousLinearMap r).compLpₗ p μ
          invFun := (α.toContinuousLinearMap r⁻¹).compLpₗ p μ
          left_inv u := by simp [← ContinuousLinearMap.comp_compLp, hcomp, hone]
          right_inv u := by simp [← ContinuousLinearMap.comp_compLp, hcomp, hone]
          map_add' := map_add _
          map_smul' := map_smul _ }
        (hle r) (hle r⁻¹)
      map_one' := by ext1 u; simp [LinearIsometryEquiv.ofBounds, hone]
      map_mul' r t := by
        ext1 u; simp [LinearIsometryEquiv.ofBounds, ← ContinuousLinearMap.comp_compLp, hcomp] }

variable {μ p}

/-- `actionLp` acts by composing `Lp` classes with `α r`. -/
theorem actionLp_apply (r : G) (u : Lp A p μ) :
    α.actionLp μ p r u = (α.toContinuousLinearMap r).compLp u := by
  simp [actionLp, LinearIsometryEquiv.ofBounds]

/-- Pointwise almost-everywhere formula for `actionLp`. -/
theorem coeFn_actionLp (r : G) (u : Lp A p μ) :
    α.actionLp μ p r u =ᵐ[μ] fun s => α r (u s) := by
  filter_upwards [(α.toContinuousLinearMap r).coeFn_compLp u] with s hs
  rw [actionLp_apply]
  simpa using hs

/-- The inverse of `actionLp` at `r` is `actionLp` at `r⁻¹`. -/
@[simp]
theorem actionLp_symm (r : G) : (α.actionLp μ p r).symm = α.actionLp μ p r⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- The trivial C⋆-action acts trivially on `Lp`. -/
@[simp]
theorem actionLp_trivial (r : G) : (trivial (G := G) (A := A)).actionLp μ p r = 1 := by
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

/-- For `p < ∞`, `actionLp` is jointly continuous on `G × Lp A p μ`. -/
@[fun_prop]
theorem continuous_actionLp (hp : p ≠ ∞) :
    Continuous fun q : G × Lp A p μ => α.actionLp μ p q.1 q.2 := by
  refine continuous_prod_of_dense_continuous_lipschitzWith' _ 1 (Lp.simpleFunc.dense hp)
    (fun r => (α.actionLp μ p r).isometry.lipschitzWith) fun u hu => ?_
  refine Lp.simpleFunc.induction (one_pos.trans_le Fact.out).ne' hp
    (P := fun v : Lp.simpleFunc A p μ => Continuous fun r => α.actionLp μ p r (v : Lp A p μ))
    ?_ ?_ ⟨u, hu⟩
  · intro c s hs hμs
    have hcont : Continuous fun r => indicatorConstLp (μ := μ) p hs hμs.ne (α r c) := by
      refine continuous_iff_continuousAt.2 fun r₀ => tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have horbit : Continuous fun r => α r c := by fun_prop
      refine squeeze_zero (g := fun r => ‖α r c - α r₀ c‖ * μ.real s ^ (1 / p.toReal))
        (fun _ => norm_nonneg _)
        (fun r => by rw [indicatorConstLp_sub]; exact norm_indicatorConstLp_le) ?_
      simpa only [sub_self, norm_zero, zero_mul] using
        (((horbit.tendsto r₀).sub_const (α r₀ c)).norm).mul_const (μ.real s ^ (1 / p.toReal))
    simpa only [Lp.simpleFunc.coe_indicatorConst, α.actionLp_indicatorConstLp] using hcont
  · intro f g hf hg _ hcf hcg
    simpa only [Pi.add_def, AddSubgroup.coe_add, map_add] using hcf.add hcg

/-- For `p < ∞`, every orbit `r ↦ α.actionLp μ p r u` is norm continuous in `Lp A p μ`. -/
theorem continuous_actionLp_apply (hp : p ≠ ∞) (u : Lp A p μ) :
    Continuous fun r => α.actionLp μ p r u :=
  (α.continuous_actionLp hp).comp (continuous_id.prodMk continuous_const)

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

/-- Pointwise almost-everywhere formula `(α.translateLp μ p r u) s = α r (u (r⁻¹ * s))`. -/
theorem coeFn_translateLp (r : G) (u : Lp A p μ) :
    α.translateLp μ p r u =ᵐ[μ] fun s => α r (u (r⁻¹ * s)) := by
  filter_upwards [α.coeFn_actionLp r (Lp.leftTranslation μ p ℂ r u),
    Lp.coeFn_leftTranslation (𝕜 := ℂ) r u] with s h₁ h₂
  rw [translateLp_apply, h₁, h₂]

/-- The inverse of twisted left translation by `r` is twisted left translation by `r⁻¹`. -/
@[simp]
theorem translateLp_symm (r : G) : (α.translateLp μ p r).symm = α.translateLp μ p r⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- For the trivial C⋆-action, `translateLp` is untwisted left translation `Lp.leftTranslation`. -/
@[simp]
theorem translateLp_trivial (r : G) :
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

/-- On `C_c(G, A)`, `translateLp` agrees with `CStarAction.translate`. -/
@[simp]
theorem translateLp_toL1 [ContinuousMul G] [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
    (r : G) (f : C_c(G, A)) :
    α.translateLp μ 1 r (f.integrable.toL1 f) =
      (α.translate r f).integrable.toL1 (α.translate r f) := by
  refine Lp.ext ?_
  filter_upwards [α.coeFn_translateLp r (f.integrable.toL1 f),
    (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae f.integrable.coeFn_toL1,
    (α.translate r f).integrable.coeFn_toL1] with s h₁ h₂ h₃
  rw [h₁, h₂, h₃, translate_apply]

/-- On `ConvolutionAlgebra α μ`, `translateLp` agrees with `CStarAction.translate`. -/
theorem ConvolutionAlgebra.translateLp_toL1 [ContinuousMul G] [OpensMeasurableSpace G]
    [IsFiniteMeasureOnCompacts μ] (r : G) (f : ConvolutionAlgebra α μ) :
    α.translateLp μ 1 r (ConvolutionAlgebra.toL1 f) =
      ConvolutionAlgebra.toL1 (α := α) (μ := μ) (.toConv (α.translate r f.ofConv)) := by
  rw [ConvolutionAlgebra.toL1_apply, ConvolutionAlgebra.toL1_toConv, α.translateLp_toL1]

/-- For `p < ∞`, twisted left translation on `Lp A p μ` is strongly continuous. -/
theorem continuous_translateLp_apply [IsTopologicalGroup G] [BorelSpace G]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] (hp : p ≠ ∞) (u : Lp A p μ) :
    Continuous fun r => α.translateLp μ p r u := by
  simp_rw [translateLp_apply]
  exact (α.continuous_actionLp hp).comp
    (continuous_id.prodMk (Lp.continuous_leftTranslation_apply hp u))

/-- For `p < ∞`, twisted left translation is jointly continuous on `G × Lp A p μ`. -/
@[fun_prop]
theorem continuous_translateLp [IsTopologicalGroup G] [BorelSpace G]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] (hp : p ≠ ∞) :
    Continuous fun q : G × Lp A p μ => α.translateLp μ p q.1 q.2 :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun r => (α.translateLp μ p r).isometry.lipschitzWith) (α.continuous_translateLp_apply hp)

end TranslateLp

/-! ### Twisted Bochner `L¹` convolution on `Lᵖ` -/

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
in `Lp A p μ` for `1 ≤ p < ∞`. -/
theorem integrable_mul_translateLp (hp : p ≠ ∞) {h : G → A} (hh : Integrable h μ)
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

/-- Left multiplication by `a ∈ A` commutes with twisted convolution in the first argument. -/
theorem mul_compLp_convolutionLp (a : A) (h : Lp A 1 μ) (f : Lp A p μ) :
    (ContinuousLinearMap.mul ℂ A a).compLp (α.convolutionLp μ p hp h f) =
      α.convolutionLp μ p hp ((ContinuousLinearMap.mul ℂ A a).compLp h) f := by
  let L : Lp A p μ →L[ℂ] Lp A p μ := (ContinuousLinearMap.mul ℂ A a).compLpL p μ
  have hcomm := L.integral_comp_comm (α.integrable_mul_translateLp μ hp (L1.integrable_coeFn h) f)
  rw [← ContinuousLinearMap.compLpL_apply, convolutionLp_apply, ← hcomm, convolutionLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ A a).coeFn_compLp h] with y hy
  rw [ContinuousLinearMap.compLpL_apply, hy, ← ContinuousLinearMap.comp_compLp]
  congr 1; ext b; simp [mul_assoc]

/-- Twisted left translation commutes with twisted convolution:
`translateLp g (h ⋆ f) = (translateLp g h) ⋆ f`. -/
theorem translateLp_convolutionLp (g : G) (h : Lp A 1 μ) (f : Lp A p μ) :
    α.translateLp μ p g (α.convolutionLp μ p hp h f) =
      α.convolutionLp μ p hp (α.translateLp μ 1 g h) f := by
  let L : Lp A p μ →L[ℂ] Lp A p μ :=
    (α.translateLp μ p g).toContinuousLinearEquiv.toContinuousLinearMap
  have hL (u : Lp A p μ) : L u = α.translateLp μ p g u := rfl
  have hcomm := L.integral_comp_comm (α.integrable_mul_translateLp μ hp (L1.integrable_coeFn h) f)
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

/-- On compactly supported continuous functions, `convolutionLp` is represented almost everywhere
by `CStarAction.convolution`. -/
theorem convolutionLp_toL1_ae_eq_convolution (f g : C_c(G, A)) :
    α.convolutionLp μ 1 ENNReal.one_ne_top (f.integrable.toL1 f) (g.integrable.toL1 g) =ᵐ[μ]
      α.convolution μ f g := by
  refine (L1.integrable_coeFn _).ae_eq_of_forall_setIntegral_eq _ _
    (α.convolution μ f g).integrable fun s _ _ => ?_
  let T : Lp A 1 μ →L[ℂ] A :=
    (L1.integralCLM' (μ := μ.restrict s) ℂ).comp (LpToLpRestrictCLM G A ℂ μ 1 s)
  have hT (u : Lp A 1 μ) : T u = ∫ x in s, u x ∂μ := by
    rw [ContinuousLinearMap.comp_apply, ← L1.integral_eq', L1.integral_eq_integral]
    exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℂ s u)
  have hL (r : G) :
      ∫ x in s, ((ContinuousLinearMap.mul ℂ A (f r)).compLp
        (α.translateLp μ 1 r (g.integrable.toL1 g))) x ∂μ =
      ∫ x in s, f r * α r (g (r⁻¹ * x)) ∂μ := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [(ContinuousLinearMap.mul ℂ A (f r)).coeFn_compLp
        (α.translateLp μ 1 r (g.integrable.toL1 g)),
      α.coeFn_translateLp r (g.integrable.toL1 g),
      (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae g.integrable.coeFn_toL1]
      with x h₁ h₂ h₃
    rw [h₁, ContinuousLinearMap.mul_apply', h₂, h₃]
  rw [← hT, α.convolutionLp_toL1 f.integrable,
    ← T.integral_comp_comm (α.integrable_mul_translateLp μ ENNReal.one_ne_top f.integrable _)]
  simp_rw [hT, hL, α.convolution_apply]
  let F : G → G → A := fun x r => f r * α r (g (r⁻¹ * x))
  have hFc : Continuous (uncurry F) := by rw [uncurry_def]; fun_prop
  have hFs : HasCompactSupport (uncurry F) :=
    hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport
      fun x r hxr =>
        ⟨subset_tsupport _ (mem_support.2 (left_ne_zero_of_mul hxr)),
          subset_tsupport _ (mem_support.2 fun hg => right_ne_zero_of_mul hxr (by simp [hg]))⟩
  exact integral_integral_swap_of_hasCompactSupport (f := fun r x => F x r)
    (hFc.comp continuous_swap) (hFs.comp_homeomorph (Homeomorph.prodComm G G))

/-- On compactly supported continuous functions, `convolutionLp` agrees with
`CStarAction.convolution`. -/
@[simp]
theorem convolutionLp_toL1_eq_toL1_convolution (f g : C_c(G, A)) :
    α.convolutionLp μ 1 ENNReal.one_ne_top (f.integrable.toL1 f) (g.integrable.toL1 g) =
      (α.convolution μ f g).integrable.toL1 (α.convolution μ f g) :=
  Lp.ext <| (α.convolutionLp_toL1_ae_eq_convolution f g).trans
    (α.convolution μ f g).integrable.coeFn_toL1.symm

/-- On `ConvolutionAlgebra α μ`, `toL1` intertwines multiplication with `convolutionLp`. -/
@[simp]
theorem ConvolutionAlgebra.convolutionLp_toL1 (f g : ConvolutionAlgebra α μ) :
    α.convolutionLp μ 1 ENNReal.one_ne_top (ConvolutionAlgebra.toL1 f)
        (ConvolutionAlgebra.toL1 g) =
      ConvolutionAlgebra.toL1 (f * g) := by
  rw [ConvolutionAlgebra.toL1_apply, ConvolutionAlgebra.toL1_apply,
    ConvolutionAlgebra.toL1_apply, ConvolutionAlgebra.ofConv_mul,
    α.convolutionLp_toL1_eq_toL1_convolution]

end ConvolutionLp

/-! ### Isometric identification of the `L¹` completion with Bochner `L¹` -/

namespace ConvolutionAlgebra

variable {G A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A]

section FromCompletion

variable [OpensMeasurableSpace G] (α : CStarAction G A) (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ]

/-- Linear isometry from `Completion (ConvolutionAlgebra α μ)` into `Lp A 1 μ`, extending
`ConvolutionAlgebra.toL1LI`. -/
def toL1FromCompletion : Completion (ConvolutionAlgebra α μ) →ₗᵢ[ℂ] Lp A 1 μ :=
  (toL1LI α μ).fromCompletion

variable {α μ}

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
  (toL1LI α μ).toContinuousLinearMap_fromCompletion

/-- `toL1FromCompletion` intertwines the completion's multiplication with `convolutionLp`. -/
@[simp]
theorem toL1FromCompletion_mul [IsTopologicalGroup G] [BorelSpace G] [μ.IsMulLeftInvariant]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (x y : Completion (ConvolutionAlgebra α μ)) :
    toL1FromCompletion α μ (x * y) =
      α.convolutionLp μ 1 ENNReal.one_ne_top (toL1FromCompletion α μ x)
        (toL1FromCompletion α μ y) := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f g => simp only [← Completion.coe_mul', toL1FromCompletion_coe, convolutionLp_toL1]

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
  exact ⟨toConv ⟨⟨f, hfc⟩, hfs⟩, Lp.ext <| (coeFn_toL1 _).trans hu.symm⟩

/-- For a regular measure on a weakly locally compact `R₁` group, `toL1FromCompletion` is
surjective onto `Lp A 1 μ`. -/
theorem toL1FromCompletion_surjective : Function.Surjective (toL1FromCompletion α μ) := by
  rw [← Set.range_eq_univ]
  have hd : DenseRange (toL1FromCompletion α μ) :=
    (denseRange_toL1 α μ).mono (by rintro _ ⟨f, rfl⟩; exact ⟨f, toL1FromCompletion_coe f⟩)
  exact (toL1FromCompletion α μ).isometry.isClosedEmbedding.isClosed_range.closure_eq ▸
    hd.closure_eq

/-- **Bochner `L¹` realization of the twisted `L¹` completion**: for a regular measure on a weakly
locally compact `R₁` group, `Completion (ConvolutionAlgebra α μ)` is linearly isometric to
`Lp A 1 μ`. -/
def completionEquivLp : Completion (ConvolutionAlgebra α μ) ≃ₗᵢ[ℂ] Lp A 1 μ :=
  LinearIsometryEquiv.ofSurjective (toL1FromCompletion α μ) (toL1FromCompletion_surjective α μ)

variable {α μ}

/-- The forward map of `completionEquivLp` is `toL1FromCompletion`. -/
theorem coe_completionEquivLp : ⇑(completionEquivLp α μ) = toL1FromCompletion α μ :=
  LinearIsometryEquiv.coe_ofSurjective _ _

/-- Applying `completionEquivLp` agrees with `toL1FromCompletion`. -/
theorem completionEquivLp_apply (x : Completion (ConvolutionAlgebra α μ)) :
    completionEquivLp α μ x = toL1FromCompletion α μ x :=
  congrFun (coe_completionEquivLp (α := α) (μ := μ)) x

/-- On compactly supported elements, `completionEquivLp` is `toL1`. -/
@[simp]
theorem completionEquivLp_coe (f : ConvolutionAlgebra α μ) :
    completionEquivLp α μ f = toL1 f :=
  (completionEquivLp_apply (f : Completion (ConvolutionAlgebra α μ))).trans
    (toL1FromCompletion_coe f)

/-- The inverse of `completionEquivLp` sends `toL1 f` back to the completion class of `f`. -/
@[simp]
theorem completionEquivLp_symm_toL1 (f : ConvolutionAlgebra α μ) :
    (completionEquivLp α μ).symm (toL1 f) = f :=
  (completionEquivLp α μ).symm_apply_eq.2 (completionEquivLp_coe f).symm

/-- The inverse of `completionEquivLp` sends the `L¹` class of `f : C_c(G, A)` to `toConv f`. -/
@[simp]
theorem completionEquivLp_symm_integrable_toL1 (f : C_c(G, A)) :
    (completionEquivLp α μ).symm (f.integrable.toL1 f) = (toConv f : ConvolutionAlgebra α μ) := by
  rw [← toL1_toConv, completionEquivLp_symm_toL1]

/-- `completionEquivLp` transports multiplication on the completion to `convolutionLp`. -/
@[simp]
theorem completionEquivLp_mul [IsTopologicalGroup G] [μ.IsMulLeftInvariant]
    (x y : Completion (ConvolutionAlgebra α μ)) :
    completionEquivLp α μ (x * y) =
      α.convolutionLp μ 1 ENNReal.one_ne_top (completionEquivLp α μ x)
        (completionEquivLp α μ y) := by
  simp only [completionEquivLp_apply, toL1FromCompletion_mul]

/-- The inverse of `completionEquivLp` turns `convolutionLp` into the completion's product. -/
@[simp]
theorem completionEquivLp_symm_convolutionLp [IsTopologicalGroup G] [μ.IsMulLeftInvariant]
    (u v : Lp A 1 μ) :
    (completionEquivLp α μ).symm (α.convolutionLp μ 1 ENNReal.one_ne_top u v) =
      (completionEquivLp α μ).symm u * (completionEquivLp α μ).symm v :=
  (completionEquivLp α μ).injective <| by simp

variable (α) in
/-- Every class in `Lp A 1 μ` is the sum of an absolutely convergent series of compactly supported
convolution elements. -/
theorem exists_hasSum_toL1 (u : Lp A 1 μ) :
    ∃ φ : ℕ → ConvolutionAlgebra α μ,
      HasSum (fun n => toL1 (φ n)) u ∧ Summable fun n => ‖φ n‖ := by
  obtain ⟨φ, hφ_sum, hφ_norm, -⟩ :=
    Completion.exists_hasSum_coe_of_norm_lt ((completionEquivLp α μ).symm u) (lt_add_one _)
  refine ⟨φ, ?_, hφ_norm⟩
  simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    completionEquivLp_coe, LinearIsometryEquiv.apply_symm_apply] using
    (completionEquivLp α μ).toLinearIsometry.toContinuousLinearMap.hasSum hφ_sum

end CompletionEquivLp

end ConvolutionAlgebra

/-! ### Twisted involution on Bochner `L¹` -/

section TwistedInvolution

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) (μ : Measure G) [μ.IsMulLeftInvariant] [μ.Regular]

/-- The **twisted involution** `u ↦ (s ↦ c(s) • α s (star (u s⁻¹)))` on `Lp A 1 μ` for a regular
left-invariant measure `μ`, as a conjugate-linear isometric equivalence. -/
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
theorem twistedInvolutionLp_symm : (α.twistedInvolutionLp μ).symm = α.twistedInvolutionLp μ :=
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

/-- On `ConvolutionAlgebra α μ`, `twistedInvolutionLp` agrees with the compact-support star. -/
@[simp]
theorem ConvolutionAlgebra.twistedInvolutionLp_toL1 (f : ConvolutionAlgebra α μ) :
    α.twistedInvolutionLp μ (ConvolutionAlgebra.toL1 f) = ConvolutionAlgebra.toL1 (star f) := by
  rw [← ConvolutionAlgebra.completionEquivLp_coe, ← ConvolutionAlgebra.completionEquivLp_star,
    ← Completion.coe_star, ConvolutionAlgebra.completionEquivLp_coe]

/-- On `C_c(G, A)`, `twistedInvolutionLp` agrees with `CStarAction.twistedInvolution`. -/
@[simp]
theorem twistedInvolutionLp_toL1 (f : C_c(G, A)) :
    α.twistedInvolutionLp μ (f.integrable.toL1 f) =
      (α.twistedInvolution f).integrable.toL1 (α.twistedInvolution f) := by
  rw [← ConvolutionAlgebra.toL1_toConv (α := α) (μ := μ),
    ConvolutionAlgebra.twistedInvolutionLp_toL1,
    ← ConvolutionAlgebra.toConv_twistedInvolution, ConvolutionAlgebra.toL1_toConv]

/-- `twistedInvolutionLp` reverses twisted `L¹` convolution: `(u ⋆ v)* = v* ⋆ u*`. -/
theorem twistedInvolutionLp_convolutionLp (u v : Lp A 1 μ) :
    α.twistedInvolutionLp μ (α.convolutionLp μ 1 ENNReal.one_ne_top u v) =
      α.convolutionLp μ 1 ENNReal.one_ne_top (α.twistedInvolutionLp μ v)
        (α.twistedInvolutionLp μ u) := by
  rw [twistedInvolutionLp_apply, ConvolutionAlgebra.completionEquivLp_symm_convolutionLp,
    star_mul ((ConvolutionAlgebra.completionEquivLp α μ).symm u),
    ConvolutionAlgebra.completionEquivLp_mul]
  simp

end TwistedInvolution

/-! ### Equivariant functoriality on Bochner `Lᵖ` -/

namespace Hom

variable {G A B C : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}

section MapLp

variable [MeasurableSpace G] (μ : Measure G) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Pointwise application of an equivariant C⋆-algebra homomorphism `φ : Hom α β` on `Lp A p μ`,
as a contractive continuous linear map `Lp A p μ →L[ℂ] Lp B p μ`. -/
def mapLp (φ : Hom α β) : Lp A p μ →L[ℂ] Lp B p μ :=
  (NonUnitalStarAlgHom.toContinuousLinearMap φ).compLpL p μ

variable {μ p}

/-- `Hom.mapLp` is composition on `Lp` with `NonUnitalStarAlgHom.toContinuousLinearMap φ`. -/
theorem mapLp_eq_compLpL (φ : Hom α β) :
    φ.mapLp μ p = (NonUnitalStarAlgHom.toContinuousLinearMap φ).compLpL p μ :=
  (rfl)

/-- Pointwise almost-everywhere formula for `Hom.mapLp`. -/
theorem coeFn_mapLp (φ : Hom α β) (u : Lp A p μ) : φ.mapLp μ p u =ᵐ[μ] fun s => φ (u s) := by
  simpa only [mapLp_eq_compLpL, NonUnitalStarAlgHom.coe_toContinuousLinearMap] using
    (NonUnitalStarAlgHom.toContinuousLinearMap φ).coeFn_compLpL (p := p) (μ := μ) u

/-- `Hom.mapLp` is a contraction: `‖φ.mapLp μ p‖ ≤ 1`. -/
theorem norm_mapLp_le (φ : Hom α β) : ‖φ.mapLp μ p‖ ≤ 1 := by
  rw [mapLp_eq_compLpL]
  exact ((NonUnitalStarAlgHom.toContinuousLinearMap φ).norm_compLpL_le (p := p) (μ := μ)).trans
    (NonUnitalStarAlgHom.norm_toContinuousLinearMap_le φ)

/-- The identity equivariant homomorphism induces the identity on `Lp A p μ`. -/
@[simp]
theorem mapLp_id : (Hom.id α).mapLp μ p = ContinuousLinearMap.id ℂ (Lp A p μ) := by
  rw [mapLp_eq_compLpL]
  have hid : NonUnitalStarAlgHom.toContinuousLinearMap (Hom.id α) =
      ContinuousLinearMap.id ℂ A := by ext a; simp
  rw [hid, ContinuousLinearMap.id_compLpL]

/-- `Hom.mapLp` preserves composition of equivariant homomorphisms. -/
@[simp]
theorem mapLp_comp (ψ : Hom β γ) (φ : Hom α β) :
    (ψ.comp φ).mapLp μ p = (ψ.mapLp μ p).comp (φ.mapLp μ p) := by
  rw [mapLp_eq_compLpL, mapLp_eq_compLpL, mapLp_eq_compLpL, ← ContinuousLinearMap.comp_compLpL]
  congr 1; ext a; simp

/-- `Hom.mapLp` intertwines the pointwise action `actionLp`. -/
theorem mapLp_actionLp (φ : Hom α β) (r : G) (u : Lp A p μ) :
    φ.mapLp μ p (α.actionLp μ p r u) = β.actionLp μ p r (φ.mapLp μ p u) := by
  rw [mapLp_eq_compLpL, actionLp_apply, actionLp_apply, ContinuousLinearMap.compLpL_apply,
    ContinuousLinearMap.compLpL_apply, ← ContinuousLinearMap.comp_compLp,
    ← ContinuousLinearMap.comp_compLp]
  congr 1; ext a; simp [NonUnitalStarAlgHom.toContinuousLinearMap_apply]

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
  rw [hy, ← φ.mapLp_translateLp y f, mapLp_eq_compLpL, ContinuousLinearMap.compLpL_apply,
    ← ContinuousLinearMap.comp_compLp, ContinuousLinearMap.compLpL_apply,
    ← ContinuousLinearMap.comp_compLp]
  congr 1; ext a; simp [NonUnitalStarAlgHom.toContinuousLinearMap_apply]

end MapLp

section Completion

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] (φ : Hom α β)
  (μ : Measure G)

/-- `toL1` intertwines `Hom.convolutionMap` with `Hom.mapLp`. -/
@[simp]
theorem toL1_convolutionMap [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
    (f : ConvolutionAlgebra α μ) :
    ConvolutionAlgebra.toL1 (φ.convolutionMap μ f) = φ.mapLp μ 1 (ConvolutionAlgebra.toL1 f) := by
  refine Lp.ext ?_
  filter_upwards [ConvolutionAlgebra.coeFn_toL1 (φ.convolutionMap μ f),
    φ.coeFn_mapLp (ConvolutionAlgebra.toL1 f), ConvolutionAlgebra.coeFn_toL1 f] with s h₁ h₂ h₃
  simp [h₁, h₂, h₃]

variable [BorelSpace G] [μ.IsMulLeftInvariant]

/-- `toL1FromCompletion` intertwines `Hom.convolutionMapL1` with `Hom.mapLp`. -/
@[simp]
theorem toL1FromCompletion_convolutionMapL1 [IsFiniteMeasureOnCompacts μ]
    (x : Completion (ConvolutionAlgebra α μ)) :
    ConvolutionAlgebra.toL1FromCompletion β μ (φ.convolutionMapL1 μ x) =
      φ.mapLp μ 1 (ConvolutionAlgebra.toL1FromCompletion α μ x) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp

variable [μ.Regular]

/-- `completionEquivLp` intertwines `Hom.convolutionMapL1` with `Hom.mapLp`. -/
@[simp]
theorem completionEquivLp_convolutionMapL1 (x : Completion (ConvolutionAlgebra α μ)) :
    ConvolutionAlgebra.completionEquivLp β μ (φ.convolutionMapL1 μ x) =
      φ.mapLp μ 1 (ConvolutionAlgebra.completionEquivLp α μ x) := by
  simpa only [ConvolutionAlgebra.completionEquivLp_apply] using
    φ.toL1FromCompletion_convolutionMapL1 μ x

/-- The inverse of `completionEquivLp` intertwines `Hom.mapLp` with `Hom.convolutionMapL1`. -/
@[simp]
theorem completionEquivLp_symm_mapLp (u : Lp A 1 μ) :
    (ConvolutionAlgebra.completionEquivLp β μ).symm (φ.mapLp μ 1 u) =
      φ.convolutionMapL1 μ ((ConvolutionAlgebra.completionEquivLp α μ).symm u) :=
  (ConvolutionAlgebra.completionEquivLp β μ).injective <| by simp

/-- `Hom.mapLp` intertwines the twisted involution `twistedInvolutionLp`. -/
theorem mapLp_twistedInvolutionLp (u : Lp A 1 μ) :
    φ.mapLp μ 1 (α.twistedInvolutionLp μ u) = β.twistedInvolutionLp μ (φ.mapLp μ 1 u) := by
  rw [twistedInvolutionLp_apply, twistedInvolutionLp_apply, ← completionEquivLp_convolutionMapL1,
    map_star, ← completionEquivLp_symm_mapLp]

end Completion

end Hom

end TauCeti.CStarAction
