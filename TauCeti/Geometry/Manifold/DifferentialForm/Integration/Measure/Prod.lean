/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Measure
public import Mathlib.MeasureTheory.Measure.Prod

import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.MeasureTheory.Integral.Bochner.Alternating
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# The measure of a product of top forms

Let `φ₁` and `φ₂` be top forms on manifolds `M` and `N` of dimensions `k` and `l`, and let `φ` be a
top form on `M × N` which factors on product frames: for tangent vectors `v₁, …, vₖ` at `x` and
`w₁, …, wₗ` at `y`,

`φ_(x, y)((v₁, 0), …, (vₖ, 0), (0, w₁), …, (0, wₗ)) = φ₁_x(v₁, …, vₖ) φ₂_y(w₁, …, wₗ)`.

Then the measure `|φ|` of `TauCeti.RoughForm.measure` is the product measure `|φ₁| ⊗ |φ₂|`
(`TauCeti.RoughForm.measure_eq_prod`), provided `φ₁` and `φ₂` are continuous and `M`, `N` are
second countable. The symplectic volume form of a product form factors in this way
(`TauCeti.SmoothTwoForm.volumeForm_prod_apply`), which gives the product formula for Liouville
measures.

In the preferred chart of `M × N`, the product of the preferred charts of `M` and `N`, the
coefficient of `φ` in the product of coordinate bases is the product of the coefficients of `φ₁`
and `φ₂` (`TauCeti.RoughForm.inChartAt_prod_apply`). Since the coordinate measure of
`TauCeti.RoughForm.measure` does not depend on the basis used to normalize it, and the Haar measure
of a product basis is the product of the Haar measures, the two measures agree on products of
measurable subsets of chart sources. Both measures are `σ`-finite, so they agree on each product
chart source, and these sources cover `M × N`.

## Main results

* `TauCeti.RoughForm.inChartAt_prod_apply`: the coefficient of a factoring top form in a product
  chart, on a product basis.
* `TauCeti.RoughForm.measure_eq_prod`: the measure of a factoring top form is the product measure.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16
  (densities and their integrals).
-/

public section

noncomputable section

open Module MeasureTheory Set
open scoped ENNReal Manifold

namespace TauCeti

namespace RoughForm

variable {E H M F H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N] {k l p : ℕ}
  {φ : RoughForm (I.prod J) (M × N) ℝ p} {φ₁ : RoughForm I M ℝ k} {φ₂ : RoughForm J N ℝ l}

/-- **The coefficient of a factoring top form in a product chart.** If a top form `φ` on `M × N`
takes the value `φ₁_x(v) φ₂_y(w)` on the family `(v₁, 0), …, (vₖ, 0), (0, w₁), …, (0, wₗ)`, then
in the preferred chart at `(α, β)` its coefficient in the product of bases `b₁` and `b₂` is the
product of the coefficients of `φ₁` in `b₁` and of `φ₂` in `b₂`. -/
theorem inChartAt_prod_apply (hp : k + l = p)
    (h : ∀ (x : M) (y : N) (v : Fin k → TangentSpace I x) (w : Fin l → TangentSpace J y),
      φ (x, y) (fun r ↦ Sum.elim (fun i ↦ ((v i, 0) : E × F)) (fun j ↦ (0, w j))
        (finSumFinEquiv.symm (Fin.cast hp.symm r))) = φ₁ x v * φ₂ y w)
    (α : M) (β : N) {y : E} {z : F} (hy : y ∈ (extChartAt I α).target)
    (hz : z ∈ (extChartAt J β).target) (b₁ : Basis (Fin k) ℝ E) (b₂ : Basis (Fin l) ℝ F) :
    φ.inChartAt (α, β) (y, z) ((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr hp))) =
      φ₁.inChartAt α y b₁ * φ₂.inChartAt β z b₂ := by
  have hyz : (y, z) ∈ (extChartAt (I.prod J) (α, β)).target := by
    rw [extChartAt_prod]
    exact ⟨hy, hz⟩
  rw [inChartAt_apply, inChartAt_apply, inChartAt_apply, mfderivWithin_extChartAt_prod_symm _ hyz,
    ← h, extChartAt_prod]
  congr 1
  funext r
  simp only [Basis.reindex_apply, Basis.prod_apply, Equiv.symm_trans_apply, finCongr_symm,
    finCongr_apply]
  -- The product derivative acts on `(b₁ i, 0)` and `(0, b₂ j)` componentwise; the first
  -- component of the first and the second component of the second hold by unfolding `prodMap`.
  rcases finSumFinEquiv.symm (Fin.cast hp.symm r) with i | j
  · exact Prod.ext rfl (map_zero (mfderivWithin 𝓘(ℝ, F) J (extChartAt J β).symm (range J) z))
  · exact Prod.ext (map_zero (mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) y)) rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- A top-form coefficient integral over a product set whose integrand factors in the product
basis is the product of the factor integrals. The Borel structure on `E × F` is arbitrary, so this
applies to the chart measurable structure of `TauCeti.RoughForm.measure`. -/
private theorem setLIntegral_prod_addHaar [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] [mEF : MeasurableSpace (E × F)] [BorelSpace (E × F)]
    (hp : k + l = p) (b₀ : Basis (Fin p) ℝ (E × F)) (b₁ : Basis (Fin k) ℝ E)
    (b₂ : Basis (Fin l) ℝ F) {A₁ : Set E} {A₂ : Set F} (hA₁ : MeasurableSet A₁)
    (hA₂ : MeasurableSet A₂) (ψ : E × F → (E × F) [⋀^Fin p]→L[ℝ] ℝ) {f : E → ℝ≥0∞}
    {g : F → ℝ≥0∞} (hf : AEMeasurable f (b₁.addHaar.restrict A₁))
    (hg : AEMeasurable g (b₂.addHaar.restrict A₂))
    (hψ : ∀ z ∈ A₁ ×ˢ A₂, ENNReal.ofReal
      |ψ z ((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr hp)))| = f z.1 * g z.2) :
    ∫⁻ z in A₁ ×ˢ A₂, ENNReal.ofReal |ψ z b₀| ∂b₀.addHaar =
      (∫⁻ y in A₁, f y ∂b₁.addHaar) * ∫⁻ z in A₂, g z ∂b₂.addHaar := by
  obtain rfl : mEF = Prod.instMeasurableSpace :=
    BorelSpace.measurable_eq.trans (Prod.borelSpace (α := E) (β := F)).measurable_eq.symm
  rw [Basis.setLIntegral_ofReal_abs_apply_basis_change
      ((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr hp))),
    setLIntegral_congr_fun (hA₁.prod hA₂) hψ, Basis.addHaar_reindex, Basis.prod_addHaar,
    ← Measure.prod_restrict, lintegral_prod_mul hf hg]

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology M] [SecondCountableTopology N] [hk : Fact (finrank ℝ E = k)]
  [hl : Fact (finrank ℝ F = l)] [Fact (finrank ℝ (E × F) = p)]

attribute [local instance] TauCeti.extChartAtMeasurableSpaceE TauCeti.extChartAtBorelSpaceE

/-- The measure of a factoring top form on a product of measurable subsets of chart sources is the
product of the measures. -/
private theorem measure_prod_of_subset (hp : k + l = p) (hφ₁ : IsSmoothForm I 0 φ₁)
    (hφ₂ : IsSmoothForm J 0 φ₂)
    (h : ∀ (x : M) (y : N) (v : Fin k → TangentSpace I x) (w : Fin l → TangentSpace J y),
      φ (x, y) (fun r ↦ Sum.elim (fun i ↦ ((v i, 0) : E × F)) (fun j ↦ (0, w j))
        (finSumFinEquiv.symm (Fin.cast hp.symm r))) = φ₁ x v * φ₂ y w)
    {α : M} {β : N} {s : Set M} {t : Set N} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsα : s ⊆ (extChartAt I α).source) (htβ : t ⊆ (extChartAt J β).source) :
    φ.measure (s ×ˢ t) = φ₁.measure s * φ₂.measure t := by
  set b₁ := finBasisOfFinrankEq ℝ E hk.out
  set b₂ := finBasisOfFinrankEq ℝ F hl.out
  have hsub : s ×ˢ t ⊆ (extChartAt (I.prod J) (α, β)).source := by
    rw [extChartAt_prod, PartialEquiv.prod_source]
    exact prod_mono hsα htβ
  have himage : extChartAt (I.prod J) (α, β) '' (s ×ˢ t) =
      (extChartAt I α '' s) ×ˢ (extChartAt J β '' t) := by
    rw [extChartAt_prod, PartialEquiv.prod_coe, prod_image_image_eq]
  have hA₁ : extChartAt I α '' s ⊆ (extChartAt I α).target :=
    (image_mono hsα).trans (extChartAt I α).image_source_eq_target.subset
  have hA₂ : extChartAt J β '' t ⊆ (extChartAt J β).target :=
    (image_mono htβ).trans (extChartAt J β).image_source_eq_target.subset
  have hm₁ : AEMeasurable (fun y ↦ ENNReal.ofReal |φ₁.inChartAt α y b₁|)
      (b₁.addHaar.restrict (extChartAt I α '' s)) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (continuous_abs.comp_continuousOn
      ((continuous_eval_const (b₁ : Fin k → E)).comp_continuousOn
        ((hφ₁.continuousOn_inChartAt α).mono hA₁)))).aemeasurable (hs.image_extChartAt α hsα)
  have hm₂ : AEMeasurable (fun z ↦ ENNReal.ofReal |φ₂.inChartAt β z b₂|)
      (b₂.addHaar.restrict (extChartAt J β '' t)) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (continuous_abs.comp_continuousOn
      ((continuous_eval_const (b₂ : Fin l → F)).comp_continuousOn
        ((hφ₂.continuousOn_inChartAt β).mono hA₂)))).aemeasurable (ht.image_extChartAt β htβ)
  rw [φ.measure_apply_of_subset (hs.prod ht) hsub, φ₁.measure_apply_of_subset hs hsα,
    φ₂.measure_apply_of_subset ht htβ, himage]
  -- The chart measurable structure on `E × F` is supplied explicitly: elaborating it by instance
  -- search would find the product structure and force an expensive unification.
  refine setLIntegral_prod_addHaar (mEF := TauCeti.extChartAtMeasurableSpaceE) hp _ b₁ b₂
    (hs.image_extChartAt α hsα) (ht.image_extChartAt β htβ) _ hm₁ hm₂ fun z hz ↦ ?_
  rw [inChartAt_prod_apply hp h α β (hA₁ hz.1) (hA₂ hz.2), abs_mul,
    ENNReal.ofReal_mul (abs_nonneg _)]

/-- **The measure of a product of top forms is the product measure.** Let `φ₁` and `φ₂` be
continuous top forms on second countable manifolds `M` and `N` of dimensions `k` and `l`, and let
`φ` be a top form on `M × N` taking the value `φ₁_x(v) φ₂_y(w)` on every family
`(v₁, 0), …, (vₖ, 0), (0, w₁), …, (0, wₗ)` of tangent vectors at `(x, y)`. Then
`|φ| = |φ₁| ⊗ |φ₂|`. -/
theorem measure_eq_prod (hp : k + l = p) (hφ₁ : IsSmoothForm I 0 φ₁) (hφ₂ : IsSmoothForm J 0 φ₂)
    (h : ∀ (x : M) (y : N) (v : Fin k → TangentSpace I x) (w : Fin l → TangentSpace J y),
      φ (x, y) (fun r ↦ Sum.elim (fun i ↦ ((v i, 0) : E × F)) (fun j ↦ (0, w j))
        (finSumFinEquiv.symm (Fin.cast hp.symm r))) = φ₁ x v * φ₂ y w) :
    φ.measure = φ₁.measure.prod φ₂.measure := by
  have := isLocallyFiniteMeasure_measure hφ₁
  have := isLocallyFiniteMeasure_measure hφ₂
  -- Both measures are determined by their restrictions to countably many product chart sources.
  obtain ⟨T, hT, hcover⟩ := LindelofSpace.elim_nhds_subcover
    (fun q : M × N ↦ (extChartAt (I.prod J) q).source) fun q ↦ extChartAt_source_mem_nhds q
  refine Measure.ext_of_biUnion_eq_univ hT hcover fun q _ ↦ ?_
  have hU := (isOpen_extChartAt_source (I := I) q.1).measurableSet
  have hV := (isOpen_extChartAt_source (I := J) q.2).measurableSet
  rw [extChartAt_prod, PartialEquiv.prod_source, ← Measure.prod_restrict]
  refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
  rw [Measure.restrict_apply (hs.prod ht), prod_inter_prod, Measure.restrict_apply hs,
    Measure.restrict_apply ht]
  exact measure_prod_of_subset hp hφ₁ hφ₂ h (hs.inter hU) (ht.inter hV) inter_subset_right
    inter_subset_right

end RoughForm

end TauCeti
