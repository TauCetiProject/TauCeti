/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.MeasureTheory.Measure.Real

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

Finally, a weight `exp ∘ g` whose exponent is bounded above almost everywhere keeps a finite
measure finite.

## Main statements

* `MeasurableEquiv.map_withDensity`: the image of a weighted measure along a measurable
  equivalence is the image measure weighted by the transported weight.
* `TauCeti.Probability.map_abs_withDensity`: the image of a weighted Lebesgue measure under
  absolute value has the folded density.
* `MeasureTheory.Measure.map_withDensity_eq_withDensity`: a pointwise factorization of one weight
  through a map whose Jacobian identity is already known transports that weight to the image.
* `MeasureTheory.Measure.map_add_right_withDensity`: translating a weighted right-invariant
  measure translates the weight.
* `MeasureTheory.Measure.map_affine_withDensity`: the image of a weighted Haar measure under an
  invertible affine map is that Haar measure weighted by the substituted density, rescaled by the
  constant Jacobian factor.
* `MeasureTheory.Measure.rnDeriv_map_affine`: the Radon–Nikodym derivative of an affine image is
  obtained by the same substitution and Jacobian factor.
* `MeasureTheory.Measure.support_withDensity_eq_closure_of_subset`: a density positive on an open
  set and zero off its closure has topological support equal to that closure.
* `MeasureTheory.Measure.support_withDensity_eq_closure`: the special case where the function
  support is exactly the open set.
* `MeasureTheory.isFiniteMeasure_withDensity_ofReal_exp`: a finite measure weighted by `exp ∘ g`,
  with `g` bounded above almost everywhere, is finite.
* `TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul`: the change of variables on the real line
  along a map injective and differentiable on a measurable set.
* `TauCeti.MeasureTheory.map_sq_withDensity_restrict_Ioi`: its instance for squaring on the
  positive half-line.
-/
public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace MeasurableEquiv

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **A weight travels with the measure it weights.** Pushing `μ.withDensity f` forward along a
measurable equivalence `e` gives the pushforward of `μ` weighted by `f ∘ e.symm`. The weight `f`
is arbitrary; no measurability of it is required. -/
theorem map_withDensity (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity fun y => f (e.symm y) := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), Measure.restrict_map e.measurable hs,
    lintegral_map_equiv]
  simp only [MeasurableEquiv.symm_apply_apply]

end MeasurableEquiv

namespace TauCeti.Probability

open Set

/-- **The folded density.** If `μ` has density `f` with respect to Lebesgue measure, then the
folded law has density `f x + f (-x)` on the positive half-line and `0` elsewhere. -/
theorem map_abs_withDensity {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (volume.withDensity f).map (|·|) =
      volume.withDensity ((Ioi 0).indicator fun x => f x + f (-x)) := by
  have hvolume : volume.map (fun x : ℝ => -x) = volume := by
    exact Measure.map_neg_eq_self (volume : Measure ℝ)
  have hneg : (volume.withDensity f).neg = volume.withDensity fun x => f (-x) := by
    have h := MeasurableEquiv.map_withDensity (MeasurableEquiv.neg ℝ) volume f
    have hvolume' : volume.map (MeasurableEquiv.neg ℝ) = volume := hvolume
    rw [hvolume'] at h
    simpa [Measure.neg_def] using h
  rw [(volume.withDensity f).map_abs_eq_restrict_add_restrict, hneg,
    restrict_withDensity measurableSet_Ici,
    restrict_withDensity measurableSet_Ioi, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm,
    ← withDensity_indicator measurableSet_Ioi, ← withDensity_indicator measurableSet_Ioi,
    ← withDensity_add_left (hf.indicator measurableSet_Ioi)]
  congr 1
  ext x
  by_cases hx : x ∈ Ioi 0 <;> simp [hx]

end TauCeti.Probability

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- If a measurable density is positive on an open set and zero off its closure, then its weighted
measure has topological support equal to that closure, provided the reference measure is positive
on nonempty open sets.

This form allows the density to take arbitrary values on the boundary. -/
theorem support_withDensity_eq_closure_of_subset {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure]
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
    rw [withDensity_apply _ hV.measurableSet, setLIntegral_pos_iff hf]
    exact ((hU.inter hV).measure_pos μ ⟨y, hyU, hyV⟩).trans_le
      (measure_mono fun _ hz ↦ ⟨hU_support hz.1, hz.2⟩)

/-- If a measurable density is positive exactly on an open set, then its weighted measure has
topological support equal to the closure of that set, provided the reference measure is positive
on nonempty open sets. -/
theorem support_withDensity_eq_closure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure] {f : X → ℝ≥0∞}
    {U : Set X} (hf : Measurable f) (hU : IsOpen U) (hsupp : Function.support f = U) :
    (μ.withDensity f).support = closure U := by
  exact support_withDensity_eq_closure_of_subset hf hU (hsupp.ge)
    (hsupp.le.trans subset_closure)

/-- **A Jacobian identity transports a weight.** Suppose `f` carries `μ` weighted by `jac` to `ν`,
which is the Jacobian formula for `f` when `μ` and `ν` are the restrictions of a Haar measure to
the two regions `f` maps onto each other. If a weight `h` upstairs factors almost everywhere as
`jac` times a weight `g` downstairs, then `f` carries `μ.withDensity h` to `ν.withDensity g`: the
change of variables for measures upgrades to one for densities.

This is the step that turns a pointwise density computation into an identity of measures, so the
work in an application is the factorization hypothesis alone. -/
theorem map_withDensity_eq_withDensity {μ : Measure α} {ν : Measure β} {f : α → β}
    {jac h : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : Measurable f) (hjac : Measurable jac)
    (hg : Measurable g) (hmap : (μ.withDensity jac).map f = ν)
    (hh : ∀ᵐ z ∂μ, jac z * g (f z) = h z) :
    (μ.withDensity h).map f = ν.withDensity g := by
  ext q hq
  have hcomp : Measurable fun z => q.indicator g (f z) := (hg.indicator hq).comp hf
  rw [Measure.map_apply hf hq, withDensity_apply _ (hf hq), withDensity_apply _ hq,
    ← lintegral_indicator (hf hq), ← lintegral_indicator hq, ← hmap,
    lintegral_map (hg.indicator hq) hf, lintegral_withDensity_eq_lintegral_mul _ hjac hcomp]
  refine lintegral_congr_ae ?_
  filter_upwards [hh] with z hz
  by_cases hzq : f z ∈ q
  · rw [Set.indicator_of_mem (Set.mem_preimage.mpr hzq), Pi.mul_apply,
      Set.indicator_of_mem hzq, hz]
  · rw [Set.indicator_of_notMem (Set.mem_preimage.not.mpr hzq), Pi.mul_apply,
      Set.indicator_of_notMem hzq, mul_zero]

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
  set r : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| with hr
  have hdet : LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 := ((A : E ≃ₗ[ℝ] E).isUnit_det').ne_zero
  have hmapA : μ.map A = r • μ := by
    rw [hr]
    simpa using Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  -- the linear part rescales the measure by the Jacobian, and substitutes `A⁻¹` in the density
  have hlin : (μ.withDensity g).map A = μ.withDensity fun y => r * g (A.symm y) := by
    rw [← A.coe_toHomeomorph, ← Homeomorph.toMeasurableEquiv_coe, MeasurableEquiv.map_withDensity]
    simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.toMeasurableEquiv_symm_coe,
      ContinuousLinearEquiv.coe_toHomeomorph, ContinuousLinearEquiv.coe_symm_toHomeomorph]
    rw [hmapA, withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    exact congrArg μ.withDensity (funext fun y => by simp only [Pi.smul_apply, smul_eq_mul, hr])
  -- the translation leaves the Haar measure alone, and substitutes `· - c` in the density
  calc (μ.withDensity g).map (fun x => c + A x)
      = ((μ.withDensity g).map A).map (fun y : E => c + y) :=
        (Measure.map_map (by fun_prop) (by fun_prop)).symm
    _ = (μ.withDensity fun y => r * g (A.symm y)).map (fun y : E => c + y) := by rw [hlin]
    _ = μ.withDensity fun y => r * g (A.symm (y - c)) := by
        rw [← MeasurableEquiv.coe_addLeft c, MeasurableEquiv.map_withDensity]
        simp only [MeasurableEquiv.coe_addLeft, MeasurableEquiv.symm_addLeft,
          map_add_left_eq_self, neg_add_eq_sub]

/-- **Radon–Nikodym derivative under an invertible affine map.** The derivative of the image of
an s-finite measure under `x ↦ c + A x`, relative to an additive Haar measure, is obtained by
substituting the inverse affine map and multiplying by the reciprocal absolute determinant. -/
theorem rnDeriv_map_affine (μ : Measure E) [μ.IsAddHaarMeasure] (A : E ≃L[ℝ] E) (c : E)
    (ν : Measure E) [SFinite ν] :
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
  have hmapμ : μ.map (fun x ↦ c + A x) = r • μ := by
    have hmapA : μ.map A = r • μ := by
      simpa [r] using Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
    calc
      μ.map (fun x ↦ c + A x) = (μ.map A).map (fun y : E ↦ c + y) :=
        (Measure.map_map (by fun_prop) (by fun_prop)).symm
      _ = (r • μ).map (fun y : E ↦ c + y) := by rw [hmapA]
      _ = r • μ := by
        rw [Measure.map_smul r
          ((by fun_prop : Measurable fun y : E ↦ c + y).aemeasurable), map_add_left_eq_self]
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

/-- A measure with log-density bounded above almost everywhere against a finite measure is
finite. -/
theorem isFiniteMeasure_withDensity_ofReal_exp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {g : α → ℝ} {M : ℝ} (hg : AEMeasurable g μ) (hgM : ∀ᵐ x ∂μ, g x ≤ M) :
    IsFiniteMeasure (μ.withDensity fun x ↦ ENNReal.ofReal (Real.exp (g x))) := by
  refine isFiniteMeasure_withDensity_ofReal (Integrable.of_bound
    (Real.measurable_exp.comp_aemeasurable hg).aestronglyMeasurable (Real.exp M)
    (hgM.mono fun x hx ↦ ?_)).2
  rwa [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]

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
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` has none: that theorem is the case
`f = 1`. Unlike
`MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul`, it does not ask
`φ` to be injective off `s`, which is what a substitution on a half-line needs. The weight `f` is
arbitrary; no measurability of it is required. -/
theorem map_withDensity_abs_deriv_mul (hs : MeasurableSet s) (hφ : Measurable φ)
    (hφ' : ∀ x ∈ s, HasDerivWithinAt φ (φ' x) s x) (hinj : InjOn φ s) :
    ((volume.restrict s).withDensity fun t ↦ ENNReal.ofReal |φ' t| * f (φ t)).map φ =
      (volume.restrict (φ '' s)).withDensity f := by
  ext A hA
  rw [Measure.map_apply hφ hA, withDensity_apply _ (hφ hA), withDensity_apply _ hA,
    Measure.restrict_restrict (hφ hA), Measure.restrict_restrict hA,
    ← image_preimage_inter φ s A, lintegral_image_eq_lintegral_abs_deriv_mul ((hφ hA).inter hs)
    (fun x hx ↦ (hφ' x hx.2).mono inter_subset_right) (hinj.mono inter_subset_right)]

/-- **The substitution `x = t ^ 2` on the positive half-line.** Weighting Lebesgue measure on
`Ioi 0` by `2 * t * f (t ^ 2)` and pushing forward along squaring gives Lebesgue measure on
`Ioi 0` weighted by `f`. -/
theorem map_sq_withDensity_restrict_Ioi (f : ℝ → ℝ≥0∞) :
    ((volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦
        ENNReal.ofReal (2 * t) * f (t ^ 2)).map (fun t ↦ t ^ 2) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity f := by
  have himage : (fun t : ℝ ↦ t ^ 2) '' Ioi 0 = Ioi 0 := by
    ext x
    refine ⟨fun ⟨t, ht, htx⟩ ↦ htx ▸ mem_Ioi.mpr (pow_pos ht 2),
      fun hx ↦ ⟨√x, Real.sqrt_pos.mpr hx, ?_⟩⟩
    simpa using Real.sq_sqrt (mem_Ioi.mp hx).le
  have hinj : InjOn (fun t : ℝ ↦ t ^ 2) (Ioi 0) :=
    (pow_left_strictMonoOn₀ two_ne_zero).injOn.mono fun t ht ↦ le_of_lt ht
  have hweight : (fun t : ℝ ↦ ENNReal.ofReal (2 * t) * f (t ^ 2)) =ᵐ[volume.restrict (Ioi 0)]
      fun t ↦ ENNReal.ofReal |2 * t| * f (t ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [abs_of_pos (by simpa using ht : (0 : ℝ) < 2 * t)]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * t) t := fun t ↦ by
    simpa using hasDerivAt_pow 2 t
  rw [withDensity_congr_ae hweight, map_withDensity_abs_deriv_mul measurableSet_Ioi (by fun_prop)
    (fun t _ ↦ (hderiv t).hasDerivWithinAt) hinj, himage]

end TauCeti.MeasureTheory
