/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Prod.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.Geometry.Manifold.ExtChartAt.Prod
import TauCeti.Geometry.Manifold.Measure.Prod
import TauCeti.MeasureTheory.Integral.Lebesgue.Gram

/-!
# The Riemannian volume of a product

Give `M × N` the product of Riemannian metrics on `M` and `N`
(`TauCeti.Manifold.instRiemannianBundleProd`). Its Riemannian volume is the product of the
Riemannian volumes of the factors (`TauCeti.riemannianVolume_prod`):

`dV_{M × N} = dV_M ⊗ dV_N`.

So integrals over `M × N` are iterated integrals over the factors, by Fubini's theorem, and
`L²(M × N)` is `L²(dV_M ⊗ dV_N)`. Together with `MeasureTheory.Lp.completedTensorProdEquiv`, this
identifies `L²(M × N)` with the completed Hilbert tensor product `L²(M) ⊗̂ L²(N)`, in which the
functions `f(x) g(y)` are the elementary tensors, as for the eigenfunction expansion of the
Laplacian of a product.

## The argument

In the preferred chart of `M × N`, the product of the preferred charts of `M` and `N`, the inverse
tangent trivialization acts componentwise
(`TauCeti.Manifold.tangentSpaceProdEquiv_symmL_trivializationAt`), so the product metric read in
coordinates is the block-diagonal form `LinearMap.BilinForm.prod` of the metrics of the factors
read in their charts. The chart density is the Gram density of this form in `Module.finBasis`
(`TauCeti.chartVolumeDensity_eq_sqrt_det`), and the coordinate measure weighted by a Gram density
does not depend on the basis; in the product basis the Gram matrix is block diagonal and the Haar
measure is the product of the Haar measures
(`Module.Basis.setLIntegral_ofReal_sqrt_det_toMatrix_prod`). Hence the two measures agree on
products of measurable subsets of chart sources. The factor volumes are locally finite, hence
`σ`-finite on second countable manifolds, so the measures agree everywhere
(`TauCeti.eq_prod_of_apply_prod_chart_source`).

The route follows the product formula for top-form measures, `TauCeti.RoughForm.measure_eq_prod`.

## Main results

* `TauCeti.riemannianVolume_prod`: the Riemannian volume of a product of second countable
  Riemannian manifolds is the product of the Riemannian volumes.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 2.44 (the Riemannian density in coordinates) and Chapter 2 (product metrics).
-/

public section

noncomputable section

open Bundle MeasureTheory Riemannian.Tensor Set
open scoped ENNReal Manifold TauCeti

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- On the source of a product chart, the product metric read in the chart is the block-diagonal
form of the metrics of the factors read in their charts. -/
private theorem chartMetricForm_prod {α : M} {β : N} {p : M × N}
    (hp : p ∈ (chartAt (ModelProd H G) (α, β)).source) :
    chartMetricForm (I := I.prod J) (α, β) p =
      (chartMetricForm (I := I) α p.1).prod (chartMetricForm (I := J) β p.2) := by
  refine LinearMap.ext₂ fun u v ↦ ?_
  simp only [chartMetricForm_apply, Manifold.inner_tangentSpace_prod,
    Manifold.tangentSpaceProdEquiv_symmL_trivializationAt hp, LinearMap.BilinForm.prod_apply]

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology M] [SecondCountableTopology N]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle F (fun y : N ↦ TangentSpace J y)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- The Riemannian volume of a product of measurable subsets of chart sources is the product of
the volumes. -/
private theorem riemannianVolume_prod_of_subset {α : M} {β : N} {s : Set M} {t : Set N}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hsα : s ⊆ (chartAt H α).source)
    (htβ : t ⊆ (chartAt G β).source) :
    riemannianVolume (I.prod J) (M × N) (s ×ˢ t) =
      riemannianVolume I M s * riemannianVolume J N t := by
  have hsα' : s ⊆ (extChartAt I α).source := by rwa [extChartAt_source]
  have htβ' : t ⊆ (extChartAt J β).source := by rwa [extChartAt_source]
  have hA₁ := (image_mono hsα').trans (extChartAt I α).image_source_eq_target.subset
  have hA₂ := (image_mono htβ').trans (extChartAt J β).image_source_eq_target.subset
  have hm₁ := hs.image_extChartAt α hsα'
  have hm₂ := ht.image_extChartAt β htβ'
  -- The image of `s ×ˢ t` is measurable for the chart measurable structure on `E × F`.
  have hm : MeasurableSet[extChartAtMeasurableSpaceE]
      ((extChartAt I α '' s) ×ˢ (extChartAt J β '' t)) := by
    have h := hm₁.prod hm₂
    rwa [(Prod.borelSpace (α := E) (β := F)).measurable_eq] at h
  rw [riemannianVolume_apply_eq_setLIntegral_of_subset (α := (α, β)) (prod_mono hsα htβ)
      (hs.prod ht),
    riemannianVolume_apply_eq_setLIntegral_of_subset hsα hs,
    riemannianVolume_apply_eq_setLIntegral_of_subset htβ ht, extChartAt_prod_image_prod]
  simp_rw [chartVolumeDensity_eq_sqrt_det]
  -- In coordinates, the product metric is block diagonal.
  rw [setLIntegral_congr_fun hm (g := fun z ↦ ENNReal.ofReal
    √(LinearMap.BilinForm.toMatrix (Module.finBasis ℝ (E × F))
      ((chartMetricForm (I := I) α ((extChartAt I α).symm z.1)).prod
        (chartMetricForm (I := J) β ((extChartAt J β).symm z.2)))).det) fun z hz ↦ ?_]
  · -- The chart measurable structure on `E × F` is supplied explicitly: elaborating it by
    -- instance search would find the product structure and force an expensive unification.
    exact Module.Basis.setLIntegral_ofReal_sqrt_det_toMatrix_prod
      (mEF := extChartAtMeasurableSpaceE) (Module.finBasis ℝ (E × F)) (Module.finBasis ℝ E)
      (Module.finBasis ℝ F) hm₁ hm₂
      (fun y ↦ chartMetricForm (I := I) α ((extChartAt I α).symm y))
      (fun y ↦ chartMetricForm (I := J) β ((extChartAt J β).symm y))
      (fun _ _ ↦ by
        rw [toMatrix_chartMetricForm]
        exact chartGramMatrix_det_nonneg _ _)
      (by simpa only [chartVolumeDensity_eq_sqrt_det] using
        aemeasurable_ofReal_chartVolumeDensity_extChartAt_symm α hm₁ hA₁ _)
      (by simpa only [chartVolumeDensity_eq_sqrt_det] using
        aemeasurable_ofReal_chartVolumeDensity_extChartAt_symm β hm₂ hA₂ _)
  have hz₁ := (extChartAt I α).map_target (hA₁ hz.1)
  have hz₂ := (extChartAt J β).map_target (hA₂ hz.2)
  rw [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe, chartMetricForm_prod]
  simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, extChartAt_source]
    using mk_mem_prod hz₁ hz₂

/-- **The Riemannian volume of a product is the product of the Riemannian volumes.** For second
countable Riemannian manifolds `M` and `N` with continuous metrics, the Riemannian volume of the
product metric on `M × N` is `dV_M ⊗ dV_N`. -/
theorem riemannianVolume_prod :
    riemannianVolume (I.prod J) (M × N) = (riemannianVolume I M).prod (riemannianVolume J N) :=
  eq_prod_of_apply_prod_chart_source fun _ _ _ _ hs ht hsα htβ ↦
    riemannianVolume_prod_of_subset hs ht hsα htβ

end TauCeti
