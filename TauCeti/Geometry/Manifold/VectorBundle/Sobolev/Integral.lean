/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.PositiveDensity
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection

/-!
# Integrating Sobolev sections against continuous covector fields

Let `M` be a manifold without boundary modelled on a finite-dimensional real inner product space
`E`, let `V → M` be a real vector bundle with finite-dimensional model fibre `F` and a finite
bundle atlas `A` (so `M` is compact), and let `ν` be a positive continuous density measure on `M`
(`TauCeti.IsPositiveDensityMeasure`), for instance the Riemannian volume of a metric. A
*continuous covector field* is a family `L x : V x →L[ℝ] ℝ` that is continuous in the
trivializations of `V`: `x ↦ L x ∘L e.symmL ℝ x` is continuous on the base set of every preferred
trivialization `e`. The pairing `x ↦ ⟪η x, ·⟫` with a continuous section `η` of a bundle with a
continuous fibre metric is an example (`Bundle.Trivialization.continuousOn_innerSL_comp_symmL`).

Every element `w` of the Sobolev space `W^{k,p}(V)` (`TauCeti.SobolevSection A μ p k`), for
`1 ≤ p ≤ ∞`, consists of the chart data of a section `s` of `V`
(`TauCeti.SobolevSection.exists_ae_eq_coord`). This file shows that `x ↦ L x (s x)` is
`ν`-integrable (`TauCeti.SobolevSection.integrable_apply`), and that its integral

`w ↦ ∫ L x (s x) dν`

does not depend on the choice of `s` and is a continuous linear functional on `W^{k,p}(V)`
(`TauCeti.SobolevSection.integralL`, `TauCeti.SobolevSection.integralL_apply`). This is the
`L²` pairing of sections of McDuff–Salamon, Appendix C.1, extended from smooth sections to Sobolev
sections: for a continuous section `η` of a bundle with a fibre metric, the functional for
`L x = ⟪η x, ·⟫` is `w ↦ ∫ ⟪η, s⟫ dν`. On `Cᵏ` sections `σ` it is `∫ L x (σ x) dν`
(`TauCeti.SobolevSection.integralL_ofContMDiffSection`).

## The argument

The sections `s` and `t` representing the same `w` have almost everywhere equal readings in
every chart, so they agree `ν`-almost everywhere
(`TauCeti.SobolevSection.ae_eq_of_ae_eq_coord`): a positive continuous density measure has the
null sets of the charts (`TauCeti.FiniteBundleAtlas.ae_of_forall_ae_restrict_image`).

In chart `i`, at a point `y` of the chart image, `L x (s x)` is `Lᵢ y` applied to the reading
`A.coord i s y`, where `x` is the point read at `y` and `Lᵢ y = L x ∘L (A.triv i).symmL ℝ x`. The
field `Lᵢ` is continuous on the compact chart image of the closure of the chart domain, so it is
bounded on the chart image. The reading of `s` is the chart data of `w`, which are in `Lᵖ` and
hence in `L¹` on the chart image, of finite measure. Lower integrals against `ν` are controlled by
the lower integrals of the readings over the chart images
(`TauCeti.FiniteBundleAtlas.exists_lintegral_le`), which bounds `∫ |L x (s x)| dν` by a constant
times the norm of `w`.

## Main definitions

* `TauCeti.SobolevSection.integralL`: the functional `w ↦ ∫ L x (s x) dν` on `W^{k,p}(V)`.

## Main results

* `TauCeti.SobolevSection.ae_eq_of_ae_eq_coord`: sections with the chart data of one element of
  `W^{k,p}(V)` agree `ν`-almost everywhere.
* `TauCeti.SobolevSection.integrable_apply`: `x ↦ L x (s x)` is `ν`-integrable.
* `TauCeti.SobolevSection.integralL_apply`: the value of the functional at `w` is
  `∫ L x (s x) dν` for every section `s` with the chart data of `w`.
* `TauCeti.SobolevSection.integralL_ofContMDiffSection`: its value on a `Cᵏ` section.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1 (the `L²` pairing of sections and the duality (C.1.3)).
-/

public section

open Bundle MeasureTheory Set
open scoped ENNReal Manifold

universe u

noncomputable section

namespace TauCeti

namespace SobolevSection

section Chart

variable {E : Type*} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas E M F V} {L : ∀ x, V x →L[ℝ] ℝ}

/-- A continuous covector field is bounded in chart `i` on the chart image: it is continuous on
the base set of the trivialization of the chart, which contains the compact closure of the chart
domain. -/
private theorem exists_norm_comp_symmL_le
    (hL : ∀ x₀ : M, ContinuousOn (fun x ↦ L x ∘L (trivializationAt F V x₀).symmL ℝ x)
      (trivializationAt F V x₀).baseSet) (i : Fin A.n) :
    ∃ K : ℝ, ∀ y ∈ A.image i,
      ‖L ((A.chart i).symm y) ∘L (A.triv i).symmL ℝ ((A.chart i).symm y)‖ ≤ K := by
  obtain ⟨K, hK⟩ := (A.isCompact_closure_dom i).exists_bound_of_continuousOn
    ((hL (A.center i)).mono (A.closure_dom_subset_baseSet i))
  exact ⟨K, fun y hy ↦ hK _ (subset_closure (A.symm_mem_dom hy))⟩

/-- In chart `i`, `L x (s x)` is the covector `L x ∘L (A.triv i).symmL ℝ x` applied to the reading
of `s`. -/
private theorem apply_eq_comp_symmL_apply_coord {i : Fin A.n} {y : E} (hy : y ∈ A.image i)
    (s : ∀ x, V x) :
    L ((A.chart i).symm y) (s ((A.chart i).symm y)) =
      (L ((A.chart i).symm y) ∘L (A.triv i).symmL ℝ ((A.chart i).symm y)) (A.coord i s y) := by
  have hb := A.dom_subset_baseSet i (A.symm_mem_dom hy)
  rw [ContinuousLinearMap.comp_apply, A.coord_def, Trivialization.symmL_apply _ hb,
    Trivialization.symm_apply_apply_mk _ hb]

end Chart

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [MeasurableSpace M] [BorelSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas E M F V} {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {k : ℕ} {ν : Measure M}

/-- **Uniqueness of the section almost everywhere.** Two sections of `V` whose readings in every
chart agree almost everywhere with the chart data of the same element of `W^{k,p}(V)` agree
`ν`-almost everywhere. -/
theorem ae_eq_of_ae_eq_coord (hν : IsPositiveDensityMeasure 𝓘(ℝ, E) ν)
    {w : SobolevSection A μ p k} {s t : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (ht : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i t) :
    ∀ᵐ x ∂ν, s x = t x := by
  refine FiniteBundleAtlas.ae_of_forall_ae_restrict_image (A := A) (μ := μ) hν fun i ↦ ?_
  filter_upwards [(hs i).symm.trans (ht i), ae_restrict_mem (A.image i).isOpen.measurableSet]
    with y hy hyi
  refine A.eq_of_coord_chart_eq (A.symm_mem_dom hyi) ?_
  rwa [(A.chart i).right_inv (A.image_subset_target_inter_preimage_baseSet i hyi).1]

variable {L : ∀ x, V x →L[ℝ] ℝ}

variable (hν : IsPositiveDensityMeasure 𝓘(ℝ, E) ν)
  (hL : ∀ x₀ : M, ContinuousOn (fun x ↦ L x ∘L (trivializationAt F V x₀).symmL ℝ x)
    (trivializationAt F V x₀).baseSet)
include hν hL

/-- `x ↦ L x (s x)` is almost everywhere strongly measurable for `ν` when `s` has the chart data
of an element of `W^{k,p}(V)`. -/
private theorem aestronglyMeasurable_apply {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    AEStronglyMeasurable (fun x ↦ L x (s x)) ν := by
  refine FiniteBundleAtlas.aestronglyMeasurable_of_forall (A := A) (μ := μ) hν fun i ↦ ?_
  have hmeas : MeasurableSet (A.image i : Set E) := (A.image i).isOpen.measurableSet
  -- The covector field read in chart `i` is continuous on the chart image.
  have hc : ContinuousOn
      (fun y ↦ L ((A.chart i).symm y) ∘L (A.triv i).symmL ℝ ((A.chart i).symm y)) (A.image i) :=
    (hL (A.center i)).comp (A.continuousOn_chart_symm i) fun y hy ↦
      A.dom_subset_baseSet i (A.symm_mem_dom hy)
  -- Evaluation of covectors on vectors, as a continuous bilinear map.
  let ev : F →L[ℝ] (F →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ
  refine (ev.aestronglyMeasurable_comp₂
    (Lp.aestronglyMeasurable (A.sectionChartData.chartValueL μ p k i w))
    (hc.aestronglyMeasurable hmeas)).congr ?_
  filter_upwards [hs i, ae_restrict_mem hmeas] with y hy hyi
  rw [hy, apply_eq_comp_symmL_apply_coord hyi, ContinuousLinearMap.apply_apply]

omit hν [MeasurableSpace M] [BorelSpace M] in
/-- In chart `i`, the integral over the chart image of the reading of `x ↦ |L x (s x)|` is at most a
constant times the norm of `w`. -/
private theorem exists_setLIntegral_image_le (i : Fin A.n) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ (w : SobolevSection A μ p k) (s : ∀ x, V x),
      A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s →
        ∫⁻ y in A.image i, ‖L ((A.chart i).symm y) (s ((A.chart i).symm y))‖ₑ ∂μ ≤ c * ‖w‖ₑ := by
  obtain ⟨K, hK⟩ := exists_norm_comp_symmL_le hL i
  let T := A.sectionChartData.chartValueL μ p k i
  have hp : 1 / p.toReal ≤ 1 := by
    rcases eq_or_ne p ⊤ with rfl | hp
    · simp
    · exact div_le_one_of_le₀ (ENNReal.toReal_one ▸ ENNReal.toReal_mono hp Fact.out)
        ENNReal.toReal_nonneg
  -- The measure of the chart image, as seen by the chart data.
  let m := μ.restrict (A.sectionChartData.image i) univ ^ (1 - 1 / p.toReal)
  refine ⟨ENNReal.ofReal K * (m * ‖T‖ₑ), ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hp) (measure_ne_top _ _))
      eNorm_ne_top), fun w s hs ↦ ?_⟩
  have hmeas : MeasurableSet (A.image i : Set E) := (A.image i).isOpen.measurableSet
  calc ∫⁻ y in A.image i, ‖L ((A.chart i).symm y) (s ((A.chart i).symm y))‖ₑ ∂μ
      ≤ ∫⁻ y in A.image i, ENNReal.ofReal K * ‖T w y‖ₑ ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hs, ae_restrict_mem hmeas] with y hy hyi
        rw [apply_eq_comp_symmL_apply_coord hyi, ← hy]
        refine (ContinuousLinearMap.le_opENorm_of_le _ le_rfl).trans ?_
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hK y hyi)
    _ = ENNReal.ofReal K * eLpNorm (T w) 1 (μ.restrict (A.sectionChartData.image i)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← FiniteBundleAtlas.sectionChartData_image,
          eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable (T w))]
    _ ≤ ENNReal.ofReal K * (‖T w‖ₑ * m) := by
        gcongr
        rw [Lp.eNorm_def]
        simpa only [ENNReal.toReal_one, div_one] using
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (Fact.out : 1 ≤ p)
            (Lp.aestronglyMeasurable (T w))
    _ ≤ ENNReal.ofReal K * (‖T‖ₑ * ‖w‖ₑ * m) := by
        gcongr ENNReal.ofReal K * (?_ * _)
        rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal ((T.le_opNorm _).trans_eq (by rw [Submodule.norm_coe]))
    _ = _ := by ring

/-- **The `L¹` bound.** There is a finite constant `C` such that `∫ |L x (s x)| dν ≤ C ‖w‖` for
every element `w` of `W^{k,p}(V)` and every section `s` with the chart data of `w`. -/
private theorem exists_lintegral_le :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (w : SobolevSection A μ p k) (s : ∀ x, V x),
      (∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) →
        ∫⁻ x, ‖L x (s x)‖ₑ ∂ν ≤ C * ‖w‖ₑ := by
  obtain ⟨C₀, hC₀, hle⟩ := A.exists_lintegral_le (μ := μ) hν
  choose c hc_top hc using fun i ↦
    exists_setLIntegral_image_le (A := A) (μ := μ) (p := p) (k := k) hL i
  refine ⟨C₀ * ∑ i, c i, ENNReal.mul_ne_top hC₀ (ENNReal.sum_ne_top.2 fun i _ ↦ hc_top i),
    fun w s hs ↦ (hle _).trans ?_⟩
  rw [mul_assoc, Finset.sum_mul]
  gcongr with i
  exact hc i w s (hs i)

/-- **Integrability.** For every section `s` with the chart data of an element of `W^{k,p}(V)`,
`x ↦ L x (s x)` is `ν`-integrable. -/
theorem integrable_apply {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    Integrable (fun x ↦ L x (s x)) ν := by
  obtain ⟨C, hC, hle⟩ := exists_lintegral_le (A := A) (μ := μ) (p := p) (k := k) hν hL
  exact ⟨aestronglyMeasurable_apply hν hL hs,
    (hle w s hs).trans_lt (ENNReal.mul_lt_top hC.lt_top eNorm_lt_top)⟩

omit hL in
/-- The integral of `x ↦ L x (s x)` is the same for all sections `s` with the chart data of
`w`. -/
private theorem integral_eq_of_ae_eq_coord {w : SobolevSection A μ p k} {s t : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (ht : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i t) :
    ∫ x, L x (s x) ∂ν = ∫ x, L x (t x) ∂ν :=
  integral_congr_ae <| by
    filter_upwards [ae_eq_of_ae_eq_coord hν hs ht] with x hx
    rw [hx]

variable (A μ p k) in
/-- **The integral of a continuous covector field against Sobolev sections.** The continuous linear
functional `w ↦ ∫ L x (s x) dν` on `W^{k,p}(V)`, where `s` is any section with the chart data of
`w` (`TauCeti.SobolevSection.integralL_apply`). -/
def integralL : SobolevSection A μ p k →L[ℝ] ℝ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun w ↦ ∫ x, L x ((exists_ae_eq_coord w).choose x) ∂ν
      map_add' := fun w w' ↦ by
        have hs := (exists_ae_eq_coord w).choose_spec
        have hs' := (exists_ae_eq_coord w').choose_spec
        rw [integral_eq_of_ae_eq_coord hν (exists_ae_eq_coord (w + w')).choose_spec
          fun i ↦ chartValueL_add_ae_coord (hs i) (hs' i)]
        simp only [Pi.add_apply, map_add]
        exact integral_add (integrable_apply hν hL hs) (integrable_apply hν hL hs')
      map_smul' := fun c w ↦ by
        have hs := (exists_ae_eq_coord w).choose_spec
        rw [integral_eq_of_ae_eq_coord hν (exists_ae_eq_coord (c • w)).choose_spec
          fun i ↦ chartValueL_smul_ae_coord c (hs i)]
        simp only [Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
    (by
      obtain ⟨C, hC, hle⟩ := exists_lintegral_le (A := A) (μ := μ) (p := p) (k := k) hν hL
      refine ⟨C.toReal, fun w ↦ ?_⟩
      have hs := (exists_ae_eq_coord w).choose_spec
      refine (norm_integral_le_lintegral_norm _).trans ?_
      simp only [ofReal_norm]
      refine (ENNReal.toReal_mono (ENNReal.mul_ne_top hC eNorm_ne_top) (hle w _ hs)).trans_eq ?_
      rw [ENNReal.toReal_mul, toReal_eNorm])

/-- **The value of the integral functional.** For every section `s` with the chart data of
`w ∈ W^{k,p}(V)`, `TauCeti.SobolevSection.integralL` takes the value `∫ L x (s x) dν` at `w`. -/
theorem integralL_apply {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    integralL A μ p k hν hL w = ∫ x, L x (s x) ∂ν :=
  integral_eq_of_ae_eq_coord hν (exists_ae_eq_coord w).choose_spec hs

/-- On `Cᵏ` sections, `TauCeti.SobolevSection.integralL` is the integral of `L` against the
section. -/
@[simp]
theorem integralL_ofContMDiffSection [IsManifold 𝓘(ℝ, E) k M]
    [ContMDiffVectorBundle k F V 𝓘(ℝ, E)] (σ : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) :
    integralL A μ p k hν hL (ofContMDiffSection A μ p k σ) = ∫ x, L x (σ x) ∂ν :=
  integralL_apply hν hL (chartValueL_ofContMDiffSection_ae A μ p k σ)

end SobolevSection

end TauCeti
