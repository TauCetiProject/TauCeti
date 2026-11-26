/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Pushing a weighted measure forward

A weight travels with the measure it weights: along a measurable equivalence `e`, the image of
`μ.withDensity f` is the image of `μ` weighted by `f ∘ e.symm`. Mathlib has this only for the
special case of a Radon–Nikodym derivative, in
`MeasurableEmbedding.map_withDensity_rnDeriv`.

Combined with a rescaling law for the measure itself, such as
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` on a finite-dimensional real normed
space, this gives the change-of-variables formula for a density under an invertible affine map.
That is the shape a location–scale family needs: it turns a density for the standard member of the
family into a density for every other member.

A map that is injective only on part of the line admits the same change of variables there, at the
price of restricting Lebesgue measure to that part and inserting the absolute derivative into the
weight. The substitution `x = t ^ 2` on the positive half-line is the case a square-root law needs.

A weight `exp ∘ g` whose exponent is bounded above almost everywhere keeps a finite measure finite.
A weight equal to one on a measurable set leaves the mass of that set unchanged.
A measure restricted to a measurable set and then weighted still lives on that set.

The topological support of a weighted measure is also computed: an almost-everywhere nonzero
density preserves it, and, when the reference measure is positive on nonempty open sets, a density
positive on an open set and zero off its closure gives that closure as support. A measure is
absolutely continuous with respect to itself weighted by an almost-everywhere positive density, and
continuous nonnegative real densities presenting the same weighted measure against a sigma-finite
measure that is positive on nonempty open sets are equal. Two densities presenting the same
sigma-finite weighted measure agree almost everywhere against the reference measure, without
requiring the reference measure itself to be sigma-finite.

## Main statements

* `MeasurableEquiv.map_withDensity`: the image of a weighted measure along a measurable
  equivalence is the image measure weighted by the transported weight.
* `TauCeti.Probability.map_abs_withDensity`: the image of a weighted Lebesgue measure under
  absolute value has the folded density.
* `MeasureTheory.Measure.map_withDensity_eq_withDensity`: an almost-everywhere factorization of one
  weight through a map whose Jacobian identity is already known transports that weight to the image.
* `MeasureTheory.Measure.map_withDensity_comp`: the image of a measure weighted by a pulled-back
  weight is the image measure weighted by that weight.
* `MeasurableEmbedding.map_withDensity_comp`: the same along a measurable embedding, with no
  measurability of the weight.
* `MeasureTheory.Measure.map_add_right_withDensity`: translating a weighted right-invariant
  measure translates the weight.
* `MeasureTheory.Measure.map_affine_withDensity`: the image of a weighted Haar measure under an
  invertible affine map is that Haar measure weighted by the substituted density, rescaled by the
  constant Jacobian factor.
* `MeasureTheory.Measure.rnDeriv_map_affine`: the Radon–Nikodym derivative of an affine image is
  obtained by the same substitution and Jacobian factor.
* `MeasureTheory.Measure.support_withDensity_eq`: weighting a measure by an almost-everywhere
  nonzero density preserves its topological support.
* `MeasureTheory.Measure.support_withDensity_eq_closure_of_subset`: for a measure positive on
  nonempty open sets, a density positive on an open set and zero off its closure has topological
  support equal to that closure.
* `MeasureTheory.Measure.support_withDensity_eq_closure`: the special case where the function
  support is exactly the open set.
* `MeasureTheory.Measure.support_withDensity_ofReal`: for a measure positive on nonempty open
  sets, a continuous nonnegative real density has the same topological support as the measure it
  defines.
* `MeasureTheory.withDensity_apply_eq_self_of_eqOn_one`: a weight equal to one on a measurable set
  does not change the mass of that set.
* `MeasureTheory.absolutelyContinuous_withDensity_ofReal`: a measure is absolutely continuous with
  respect to itself weighted by an almost-everywhere positive real density.
* `MeasureTheory.ae_of_forall_lintegral_ne_top_ae_restrict`: weighted σ-finite localization
  principle reducing a global a.e. goal to restrictions of finite weighted mass.
* `MeasureTheory.withDensity_eq_iff_of_sigmaFinite_withDensity`: two a.e. measurable densities
  presenting the same sigma-finite weighted measure agree almost everywhere against the reference
  measure.
* `MeasureTheory.continuous_eq_of_withDensity_ofReal_eq`: continuous nonnegative real densities
  presenting the same weighted measure against a sigma-finite measure positive on nonempty open
  sets are equal pointwise.
* `MeasureTheory.isFiniteMeasure_withDensity_ofReal_exp`: a finite measure weighted by `exp ∘ g`,
  with `g` bounded above almost everywhere, is finite.
* `MeasureTheory.eq_withDensity_div_of_eq_withDensity_mul`: if `P ≪ L` where `L` is σ-finite, and
  `P`, `L` have `ℝ≥0∞`-densities `g * h` and `G * h` against `μ`, then `P = L.withDensity (g / G)`.
* `MeasureTheory.Measure.restrict_withDensity_restrict`: restricting a weighted restriction
  to the same set leaves it unchanged.
* `MeasureTheory.withDensity_restrict_apply_compl`: a measure restricted to a measurable set and
  then weighted gives no mass to the complement of the set.
* `TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul`: the change of variables on the real line
  along a map injective and differentiable on a measurable set.
* `TauCeti.MeasureTheory.map_sq_withDensity_restrict_Ioi`: its instance for squaring on the
  positive half-line.

-/
public section

open MeasureTheory

open scoped ENNReal

namespace MeasurableEmbedding

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **A pulled-back weight is pushed forward along a measurable embedding.** Unlike
`MeasureTheory.Measure.map_withDensity_comp`, no measurability of the weight `g` is needed. -/
theorem map_withDensity_comp {μ : Measure α} {f : α → β}
    (hf : MeasurableEmbedding f) (g : β → ℝ≥0∞) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator (hf.measurable hs), ← lintegral_indicator hs,
    hf.lintegral_map]
  exact lintegral_congr fun x ↦ Set.indicator_comp_right f

end MeasurableEmbedding

namespace MeasurableEquiv

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **A weight travels with the measure it weights.** Pushing `μ.withDensity f` forward along a
measurable equivalence `e` gives the pushforward of `μ` weighted by `f ∘ e.symm`. The weight `f`
is arbitrary; no measurability of it is required. -/
theorem map_withDensity (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity fun y => f (e.symm y) := by
  simpa [Function.comp_def] using e.measurableEmbedding.map_withDensity_comp (μ := μ) (f ∘ e.symm)

end MeasurableEquiv

namespace TauCeti.Probability

open Set

/-- **The folded density.** If `μ` has density `f` with respect to Lebesgue measure, then the
folded law has density `f x + f (-x)` on the positive half-line and `0` elsewhere. -/
theorem map_abs_withDensity {f : ℝ → ℝ≥0∞} (hf : AEMeasurable f) :
    (volume.withDensity f).map (|·|) =
      volume.withDensity ((Ioi 0).indicator fun x => f x + f (-x)) := by
  obtain ⟨g, hg, hfg⟩ := hf
  have hfg' : (fun x => f (-x)) =ᵐ[volume] fun x => g (-x) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hfg
  have hind : (Ioi (0 : ℝ)).indicator (fun x => f x + f (-x)) =ᵐ[volume]
      (Ioi 0).indicator fun x => g x + g (-x) := by
    filter_upwards [hfg, hfg'] with x h h'
    simp only [Set.indicator, h, h']
  rw [withDensity_congr_ae hfg, withDensity_congr_ae hind]
  have hneg : (volume.withDensity g).neg = volume.withDensity fun x => g (-x) := by
    simpa [Measure.neg_def] using MeasurableEquiv.map_withDensity (MeasurableEquiv.neg ℝ) volume g
  rw [(volume.withDensity g).map_abs_eq_restrict_add_restrict, hneg,
    restrict_withDensity measurableSet_Ici,
    restrict_withDensity measurableSet_Ioi, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm,
    ← withDensity_indicator measurableSet_Ioi, ← withDensity_indicator measurableSet_Ioi,
    ← withDensity_add_left (hg.indicator measurableSet_Ioi)]
  congr 1
  ext x
  by_cases hx : x ∈ Ioi 0 <;> simp [hx]

end TauCeti.Probability

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Weighting a measure by an almost-everywhere nonzero density preserves its topological support.
-/
theorem support_withDensity_eq {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0) :
    (μ.withDensity f).support = μ.support :=
  Set.Subset.antisymm (withDensity_absolutelyContinuous μ f).support_mono
    (withDensity_absolutelyContinuous' hf hf_ne_zero).support_mono

/-- If a measurable density is positive on an open set and zero off its closure, then its weighted
measure has topological support equal to that closure, provided the reference measure is positive
on nonempty open sets.

This form allows the density to take arbitrary values on the boundary. -/
theorem support_withDensity_eq_closure_of_subset {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure]
    {f : X → ℝ≥0∞} {U : Set X} (hf : Measurable f) (hU : IsOpen U)
    (hU_support : U ⊆ Function.support f)
    (hsupport_closure : Function.support f ⊆ closure U) :
    (μ.withDensity f).support = closure U := by
  apply Set.Subset.antisymm
  · apply support_subset_of_isClosed isClosed_closure
    rw [← Filter.eventually_mem_set, ae_withDensity_iff hf]
    exact ae_of_all _ fun _ hx ↦ hsupport_closure hx
  · rw [support_eq_forall_isOpen]
    intro x hx V hxV hV
    obtain ⟨y, hyV, hyU⟩ := mem_closure_iff.mp hx V hV hxV
    refine lt_of_lt_of_le ?_ (withDensity_apply_le f V)
    rw [setLIntegral_pos_iff hf]
    exact ((hU.inter hV).measure_pos μ ⟨y, hyU, hyV⟩).trans_le
      (measure_mono fun _ hz ↦ ⟨hU_support hz.1, hz.2⟩)

/-- If a measurable density is positive exactly on an open set, then its weighted measure has
topological support equal to the closure of that set, provided the reference measure is positive
on nonempty open sets. -/
theorem support_withDensity_eq_closure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {f : X → ℝ≥0∞}
    {U : Set X} (hf : Measurable f) (hU : IsOpen U) (hsupp : Function.support f = U) :
    (μ.withDensity f).support = closure U :=
  support_withDensity_eq_closure_of_subset hf hU hsupp.ge (hsupp.le.trans subset_closure)

/-- The support of a measure with continuous nonnegative real density is the topological support
of that density, provided the reference measure is positive on nonempty open sets. -/
theorem support_withDensity_ofReal {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure] {f : X → ℝ}
    (hf : Continuous f) (hf0 : 0 ≤ f) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))).support = tsupport f := by
  apply support_withDensity_eq_closure hf.measurable.ennreal_ofReal hf.isOpen_support
  ext x
  simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero]
  exact not_congr ⟨fun h ↦ le_antisymm h (hf0 x), fun h ↦ h.le⟩

/-- The measurable case of `map_withDensity_eq_withDensity`. -/
private theorem map_withDensity_eq_withDensity_of_measurable {μ : Measure α} {ν : Measure β}
    {f : α → β} {jac h : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : Measurable f)
    (hjac : AEMeasurable jac μ) (hg : Measurable g) (hmap : (μ.withDensity jac).map f = ν)
    (hh : ∀ᵐ z ∂μ, jac z * g (f z) = h z) :
    (μ.withDensity h).map f = ν.withDensity g := by
  ext q hq
  have hcomp : Measurable fun z => q.indicator g (f z) := (hg.indicator hq).comp hf
  rw [Measure.map_apply hf hq, withDensity_apply _ (hf hq), withDensity_apply _ hq,
    ← lintegral_indicator (hf hq), ← lintegral_indicator hq, ← hmap,
    lintegral_map (hg.indicator hq) hf,
    lintegral_withDensity_eq_lintegral_mul₀ hjac hcomp.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hh] with z hz
  by_cases hzq : f z ∈ q
  · rw [Set.indicator_of_mem (Set.mem_preimage.mpr hzq), Pi.mul_apply,
      Set.indicator_of_mem hzq, hz]
  · rw [Set.indicator_of_notMem (Set.mem_preimage.not.mpr hzq), Pi.mul_apply,
      Set.indicator_of_notMem hzq, mul_zero]

/-- **A Jacobian identity transports a weight.** Suppose `f` carries `μ` weighted by `jac` to `ν`,
which is the Jacobian formula for `f` when `μ` and `ν` are the restrictions of a Haar measure to
the two regions `f` maps onto each other. If a weight `h` upstairs factors almost everywhere as
`jac` times a weight `g` downstairs, then `f` carries `μ.withDensity h` to `ν.withDensity g`: the
change of variables for measures upgrades to one for densities.

This is the step that turns a pointwise density computation into an identity of measures, so the
work in an application is the factorization hypothesis alone. The map `f` is only required to be
`μ`-almost everywhere measurable and the weight `g` almost everywhere measurable for the image
measure `ν`. -/
theorem map_withDensity_eq_withDensity {μ : Measure α} {ν : Measure β} {f : α → β}
    {jac h : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hjac : AEMeasurable jac μ) (hg : AEMeasurable g ν) (hmap : (μ.withDensity jac).map f = ν)
    (hh : ∀ᵐ z ∂μ, jac z * g (f z) = h z) :
    (μ.withDensity h).map f = ν.withDensity g := by
  obtain ⟨f', hf', hff'⟩ := hf
  obtain ⟨g', hg', hgg'⟩ := hg
  have hmap' : (μ.withDensity jac).map f' = ν :=
    (Measure.map_congr ((withDensity_absolutelyContinuous μ jac).ae_eq hff')).symm.trans hmap
  have hgf : ∀ᵐ z ∂μ, jac z ≠ 0 → g (f' z) = g' (f' z) :=
    (ae_withDensity_iff' hjac).1 (ae_of_ae_map hf'.aemeasurable (hmap' ▸ hgg'))
  rw [Measure.map_congr ((withDensity_absolutelyContinuous μ h).ae_eq hff'),
    withDensity_congr_ae hgg']
  refine map_withDensity_eq_withDensity_of_measurable hf' hjac hg' hmap' ?_
  filter_upwards [hh, hgf, hff'] with z hz hz' hz''
  by_cases hj : jac z = 0
  · rw [hj, zero_mul, ← hz, hj, zero_mul]
  · rw [← hz, hz'', hz' hj]

/-- **A pulled-back weight is pushed forward.** If `f` is `μ`-almost everywhere measurable and `g`
is almost everywhere measurable with respect to `μ.map f`, the image under `f` of `μ` weighted by
`g ∘ f` is the image of `μ` weighted by `g`. This is the case of
`map_withDensity_eq_withDensity` with trivial Jacobian. -/
theorem map_withDensity_comp {μ : Measure α} {f : α → β} {g : β → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g (μ.map f)) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g :=
  map_withDensity_eq_withDensity (jac := fun _ => 1) hf aemeasurable_const hg (by simp) (by simp)

/-- **Translating a weighted invariant measure translates its weight.** If `μ` is invariant under
right translation, then pushing `μ.withDensity f` forward along `x ↦ x + y` gives `μ` weighted by
`x ↦ f (x - y)`. This is how the location parameter of a location family on the line moves under
translation. -/
@[simp]
theorem map_add_right_withDensity {G : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddRightInvariant] (f : G → ℝ≥0∞) (y : G) :
    (μ.withDensity f).map (· + y) = μ.withDensity fun x => f (x - y) := by
  rw [← MeasurableEquiv.coe_addRight y, MeasurableEquiv.map_withDensity]
  simp only [MeasurableEquiv.coe_addRight, MeasurableEquiv.symm_addRight, map_add_right_eq_self,
    sub_eq_add_neg]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

/-- **Change of variables for a density under an invertible affine map.** The image of
`μ.withDensity g` under `x ↦ c + A x` is `μ` weighted by the substituted density
`y ↦ g (A⁻¹ (y - c))`, scaled by the constant Jacobian factor `|det A|⁻¹`. -/
theorem map_affine_withDensity (μ : Measure E) [μ.IsAddHaarMeasure] (A : E ≃L[ℝ] E) (c : E)
    (g : E → ℝ≥0∞) :
    (μ.withDensity g).map (fun x => c + A x) =
      μ.withDensity fun y =>
        ENNReal.ofReal |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| * g (A.symm (y - c)) := by
  let e : E ≃ᵐ E := A.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addLeft c)
  have he : (e : E → E) = fun x ↦ c + A x := by funext x; simp [e]
  rw [← he, MeasurableEquiv.map_withDensity, he, Measure.map_affine_addHaar_eq_smul,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext y
  simp [e, neg_add_eq_sub]

/-- **Radon–Nikodym derivative under an invertible affine map.** The derivative of the image of
a measure with a Lebesgue decomposition under `x ↦ c + A x`, relative to an additive Haar measure,
is obtained by substituting the inverse affine map and multiplying by the reciprocal absolute
determinant. -/
theorem rnDeriv_map_affine (μ : Measure E) [μ.IsAddHaarMeasure] (A : E ≃L[ℝ] E) (c : E)
    (ν : Measure E) [ν.HaveLebesgueDecomposition μ] :
    (ν.map fun x ↦ c + A x).rnDeriv μ =ᵐ[μ]
      fun y ↦ ENNReal.ofReal |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| *
        ν.rnDeriv μ (A.symm (y - c)) := by
  let e : E ≃ᵐ E := A.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addLeft c)
  have he : (e : E → E) = fun x ↦ c + A x := by
    funext x
    simp [e]
  have hemb : MeasurableEmbedding (fun x ↦ c + A x) := by
    rw [← he]
    exact e.measurableEmbedding
  let r : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹|
  have hdet : LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 := ((A : E ≃ₗ[ℝ] E).isUnit_det').ne_zero
  have hr : r ≠ 0 := by simp [r, hdet]
  have hmapμ : μ.map (fun x ↦ c + A x) = r • μ := Measure.map_affine_addHaar_eq_smul μ A c
  have hsing : (ν.singularPart μ).map (fun x ↦ c + A x) ⟂ₘ μ := by
    have h := hemb.mutuallySingular_map (Measure.mutuallySingular_singularPart ν μ)
    rw [hmapμ] at h
    exact h.mono_ac Measure.AbsolutelyContinuous.rfl (Measure.absolutelyContinuous_smul hr)
  have hadd : ν.map (fun x ↦ c + A x) =
      (ν.singularPart μ).map (fun x ↦ c + A x) +
        μ.withDensity (fun y ↦ r * ν.rnDeriv μ (A.symm (y - c))) := by
    calc
      ν.map (fun x ↦ c + A x) =
          (ν.singularPart μ + μ.withDensity (ν.rnDeriv μ)).map
            (fun x ↦ c + A x) := congrArg (fun ρ : Measure E ↦
              ρ.map (fun x ↦ c + A x)) (Measure.haveLebesgueDecomposition_add ν μ)
      _ = (ν.singularPart μ).map (fun x ↦ c + A x) +
          (μ.withDensity (ν.rnDeriv μ)).map (fun x ↦ c + A x) := by
            rw [Measure.map_add _ _ (by fun_prop)]
      _ = (ν.singularPart μ).map (fun x ↦ c + A x) +
          μ.withDensity (fun y ↦ r * ν.rnDeriv μ (A.symm (y - c))) := by
            rw [map_affine_withDensity μ A c]
  exact (Measure.eq_rnDeriv₀ (by fun_prop) hsing hadd).symm

end MeasureTheory.Measure

namespace MeasureTheory

/-- A weight equal to one on a measurable set `s` does not change the mass of `s`. -/
theorem withDensity_apply_eq_self_of_eqOn_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s) (hf : Set.EqOn f 1 s) :
    μ.withDensity f s = μ s := by
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs hf, Pi.one_def, setLIntegral_one]

/-- A measure is absolutely continuous with respect to itself weighted by an almost-everywhere
positive real density: the weight `ENNReal.ofReal ∘ w` vanishes only on a null set, so weighting
destroys no null sets. -/
theorem absolutelyContinuous_withDensity_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w : α → ℝ} (hwm : AEMeasurable w μ) (hwpos : ∀ᵐ x ∂μ, 0 < w x) :
    μ ≪ μ.withDensity fun x => ENNReal.ofReal (w x) :=
  withDensity_absolutelyContinuous' hwm.ennreal_ofReal (by simpa using hwpos)

/-- **Weighted σ-finite localization principle.** To prove a property `p` holds `μ`-almost
everywhere, it suffices to prove it on every measurable set `s` on which `w` has finite Lebesgue
integral (`∫⁻ x, w x ∂μ.restrict s ≠ ∞`), provided `μ.withDensity w` is σ-finite. -/
theorem ae_of_forall_lintegral_ne_top_ae_restrict {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w : α → ℝ≥0∞} [SigmaFinite (μ.withDensity w)] {p : α → Prop}
    (hp : ∀ s : Set α, MeasurableSet s → ∫⁻ x, w x ∂μ.restrict s ≠ ∞ → ∀ᵐ x ∂μ.restrict s, p x) :
    ∀ᵐ x ∂μ, p x := by
  have hae_n : ∀ n, ∀ᵐ x ∂μ.restrict (spanningSets (μ.withDensity w) n), p x := fun n ↦ by
    have hs := measurableSet_spanningSets (μ.withDensity w) n
    refine hp _ hs ?_
    rw [← withDensity_apply w hs]
    exact (measure_spanningSets_lt_top (μ.withDensity w) n).ne
  rw [← Measure.restrict_univ (μ := μ), ← iUnion_spanningSets (μ.withDensity w)]
  exact (ae_restrict_iUnion_iff _ _).2 hae_n

/-- Two a.e. measurable `ℝ≥0∞`-valued densities define the same σ-finite weighted measure if and
only if they agree almost everywhere with respect to the reference measure `μ`.

Unlike Mathlib's `MeasureTheory.withDensity_eq_iff_of_sigmaFinite`, this requires σ-finiteness of
the weighted measure `μ.withDensity f` rather than of the reference measure `μ` (for example, when
`μ` is only s-finite and `μ.withDensity f` is finite). -/
theorem withDensity_eq_iff_of_sigmaFinite_withDensity {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ≥0∞} [SigmaFinite (μ.withDensity f)]
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    μ.withDensity f = μ.withDensity g ↔ f =ᵐ[μ] g := by
  refine ⟨fun hfg ↦ ae_of_forall_lintegral_ne_top_ae_restrict (w := f) fun s hs hfin ↦ ?_,
    withDensity_congr_ae⟩
  have heq : (μ.restrict s).withDensity f = (μ.restrict s).withDensity g := by
    rw [← restrict_withDensity hs, ← restrict_withDensity hs]
    exact congrArg (·.restrict s) hfg
  exact (withDensity_eq_iff hf.restrict hg.restrict hfin).mp heq

/-- Continuous nonnegative real densities that present the same measure are equal pointwise, with
respect to a σ-finite reference measure that is positive on nonempty open sets. -/
theorem continuous_eq_of_withDensity_ofReal_eq {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {ν : Measure X} [SigmaFinite ν]
    [ν.IsOpenPosMeasure] {p q : X → ℝ} (hp : Continuous p) (hq : Continuous q)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (h : ν.withDensity (fun x ↦ ENNReal.ofReal (p x)) =
      ν.withDensity (fun x ↦ ENNReal.ofReal (q x))) :
    p = q := by
  have haeENN : (fun x ↦ ENNReal.ofReal (p x)) =ᵐ[ν] fun x ↦ ENNReal.ofReal (q x) :=
    (withDensity_eq_iff_of_sigmaFinite hp.measurable.ennreal_ofReal.aemeasurable
      hq.measurable.ennreal_ofReal.aemeasurable).1 h
  have hae : p =ᵐ[ν] q := by
    filter_upwards [haeENN] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (hp0 x) (hq0 x)).mp hx
  exact (hp.ae_eq_iff_eq ν hq).1 hae

/-- A measure with log-density bounded above almost everywhere against a finite measure is
finite. -/
theorem isFiniteMeasure_withDensity_ofReal_exp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {g : α → ℝ} {M : ℝ} (hgM : ∀ᵐ x ∂μ, g x ≤ M) :
    IsFiniteMeasure (μ.withDensity fun x ↦ ENNReal.ofReal (Real.exp (g x))) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine lt_of_le_of_lt (lintegral_mono_ae (g := fun _ ↦ ENNReal.ofReal (Real.exp M))
    (hgM.mono fun x hx ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hx))) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- If `P ≪ L` where `L` is σ-finite, and `P`, `L` have `ℝ≥0∞`-valued densities `g * h` and
`G * h` with respect to `μ`, then `P` has `L`-density `g / G`. -/
theorem eq_withDensity_div_of_eq_withDensity_mul {α : Type*} [MeasurableSpace α]
    {P L μ : Measure α} [SigmaFinite L] {g G h : α → ℝ≥0∞}
    (hg : AEMeasurable g μ) (hG : AEMeasurable G μ) (hh : AEMeasurable h μ) (hPL : P ≪ L)
    (hP : P = μ.withDensity fun x ↦ g x * h x)
    (hL : L = μ.withDensity fun x ↦ G x * h x) :
    P = L.withDensity fun x ↦ g x / G x := by
  have hLm : AEMeasurable (fun x ↦ G x * h x) μ := hG.mul hh
  have hPm : AEMeasurable (fun x ↦ g x * h x) μ := hg.mul hh
  -- σ-finiteness of `L` ensures `G x * h x < ∞` `μ`-almost everywhere.
  have : SigmaFinite (μ.withDensity fun x ↦ G x * h x) := hL ▸ inferInstance
  have hLlt : ∀ᵐ x ∂μ, G x * h x < ∞ :=
    ae_of_forall_lintegral_ne_top_ae_restrict (w := fun x ↦ G x * h x) fun _ _ hfin ↦
      ae_lt_top' hLm.restrict hfin
  -- `G` is nonzero `L`-a.e., hence `P`-a.e., so `G x = 0` forces `g x * h x = 0` `μ`-a.e.
  have hZ : ∀ᵐ x ∂μ, G x = 0 → g x * h x = 0 := by
    have hLG : ∀ᵐ x ∂L, G x ≠ 0 := by
      rw [hL, ae_withDensity_iff' hLm]
      exact ae_of_all _ fun _ hx ↦ left_ne_zero_of_mul hx
    have hPG : ∀ᵐ x ∂P, G x ≠ 0 := hPL.ae_le hLG
    rw [hP, ae_withDensity_iff' hPm] at hPG
    exact hPG.mono fun _ hx hG0 ↦ not_not.mp fun hne ↦ hx hne hG0
  rw [hP, hL, ← withDensity_mul₀ (g := fun x ↦ g x / G x) hLm (hg.div hG)]
  refine withDensity_congr_ae ?_
  filter_upwards [hLlt, hZ] with x hxlt hxZ
  simp only [Pi.mul_apply]
  by_cases hh0 : h x = 0
  · simp [hh0]
  · by_cases hG0 : G x = 0
    · rw [hxZ hG0, hG0, zero_mul, zero_mul]
    · have hGtop : G x ≠ ∞ := by
        intro htop
        rw [htop, ENNReal.top_mul hh0] at hxlt
        exact lt_irrefl _ hxlt
      calc g x * h x
        _ = (g x / G x) * G x * h x := by rw [ENNReal.div_mul_cancel hG0 hGtop]
        _ = G x * h x * (g x / G x) := by ac_rfl

/-- Weighting a measure restricted to `s` and restricting it again to `s` leaves the weighted
measure unchanged. -/
@[simp]
theorem Measure.restrict_withDensity_restrict {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (f : α → ℝ≥0∞) :
    ((μ.restrict s).withDensity f).restrict s = (μ.restrict s).withDensity f := by
  refine le_antisymm Measure.restrict_le_self (Measure.le_iff.2 fun t ht ↦ ?_)
  rw [Measure.restrict_apply ht, withDensity_apply _ ht]
  calc
    (∫⁻ x in t, f x ∂μ.restrict s) = ∫⁻ x in t ∩ s, f x ∂μ.restrict s := by
      rw [Measure.restrict_restrict ht, Measure.restrict_restrict_of_subset Set.inter_subset_right]
    _ ≤ (μ.restrict s).withDensity f (t ∩ s) := withDensity_apply_le _ _

/-- A measure restricted to a measurable set `s` and then weighted gives no mass to the complement
of `s`. The weight `f` is arbitrary; no measurability of it is required. -/
theorem withDensity_restrict_apply_compl {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    (μ.restrict s).withDensity f sᶜ = 0 :=
  withDensity_absolutelyContinuous _ _ <| by
    rw [Measure.restrict_apply hs.compl, Set.compl_inter_self, measure_empty]

end MeasureTheory

namespace TauCeti.MeasureTheory

open Set

variable {s : Set ℝ} {φ φ' : ℝ → ℝ} {f : ℝ → ℝ≥0∞}

/-- **Change of variables for a weighted Lebesgue measure on the real line.** If `φ` is injective
and differentiable on a measurable set `s`, then weighting Lebesgue measure on `s` by
`|φ' t| * f (φ t)` and pushing forward along `φ` gives Lebesgue measure on the image `φ '' s`
weighted by `f`.

This is the measure-level form of Mathlib's
`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`, and it carries a weight where
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` has none: its one-dimensional instance
is the case `f = 1`. Unlike
`MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul`, it does not ask
`φ` to be injective off `s`, which is what a substitution on a half-line needs. The weight `f` is
arbitrary; no measurability of it is required. -/
theorem map_withDensity_abs_deriv_mul (hs : MeasurableSet s)
    (hφ' : ∀ x ∈ s, HasDerivWithinAt φ (φ' x) s x) (hinj : InjOn φ s) :
    ((volume.restrict s).withDensity fun t ↦ ENNReal.ofReal |φ' t| * f (φ t)).map φ =
      (volume.restrict (φ '' s)).withDensity f := by
  classical
  -- `φ` agrees on `s` with the measurable `ψ`, which changes neither side.
  set ψ := s.piecewise φ 0
  have hψ : Measurable ψ := ContinuousOn.measurable_piecewise
    (fun x hx ↦ (hφ' x hx).continuousWithinAt) continuous_zero.continuousOn hs
  have he : ∀ᵐ t ∂volume.restrict s, ψ t = φ t := by
    filter_upwards [ae_restrict_mem hs] with t ht using piecewise_eq_of_mem _ _ _ ht
  rw [← Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_eq he),
    withDensity_congr_ae (g := fun t ↦ ENNReal.ofReal |φ' t| * f (ψ t))
      (by filter_upwards [he] with t ht; rw [ht]),
    ← image_congr (piecewise_eqOn s φ 0)]
  replace hφ' x (hx : x ∈ s) : HasDerivWithinAt ψ (φ' x) s x :=
    (hφ' x hx).congr (fun y hy ↦ piecewise_eq_of_mem _ _ _ hy) (piecewise_eq_of_mem _ _ _ hx)
  replace hinj : InjOn ψ s := hinj.congr (piecewise_eqOn s φ 0).symm
  ext A hA
  rw [Measure.map_apply hψ hA, withDensity_apply _ (hψ hA), withDensity_apply _ hA,
    Measure.restrict_restrict (hψ hA), Measure.restrict_restrict hA,
    ← image_preimage_inter ψ s A, lintegral_image_eq_lintegral_abs_deriv_mul ((hψ hA).inter hs)
    (fun x hx ↦ (hφ' x hx.2).mono inter_subset_right) (hinj.mono inter_subset_right)]

/-- **The substitution `x = t ^ 2` on the positive half-line.** Weighting Lebesgue measure on
`Ioi 0` by `2 * t * f (t ^ 2)` and pushing forward along squaring gives Lebesgue measure on
`Ioi 0` weighted by `f`. -/
theorem map_sq_withDensity_restrict_Ioi (f : ℝ → ℝ≥0∞) :
    ((volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦
        ENNReal.ofReal (2 * t) * f (t ^ 2)).map (fun t ↦ t ^ 2) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity f := by
  have himage : (fun t : ℝ ↦ t ^ 2) '' Ioi 0 = Ioi 0 :=
    Real.sqPartialHomeomorph.image_source_eq_target
  have hinj : InjOn (fun t : ℝ ↦ t ^ 2) (Ioi 0) := Real.sqPartialHomeomorph.injOn
  have hweight : (fun t : ℝ ↦ ENNReal.ofReal (2 * t) * f (t ^ 2)) =ᵐ[volume.restrict (Ioi 0)]
      fun t ↦ ENNReal.ofReal |2 * t| * f (t ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [abs_of_pos (by simpa using ht : (0 : ℝ) < 2 * t)]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * t) t := fun t ↦ by
    simpa using hasDerivAt_pow 2 t
  rw [withDensity_congr_ae hweight, map_withDensity_abs_deriv_mul measurableSet_Ioi
    (fun t _ ↦ (hderiv t).hasDerivWithinAt) hinj, himage]

end TauCeti.MeasureTheory
