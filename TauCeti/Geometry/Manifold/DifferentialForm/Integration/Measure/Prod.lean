/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Measure.Basic
public import Mathlib.MeasureTheory.Measure.Prod

import TauCeti.MeasureTheory.Integral.Bochner.Alternating

/-!
# The measure of a product of top forms

Let `φ₁` and `φ₂` be top forms on manifolds `M` and `N` of dimensions `k` and `l`, and let `φ` be a
top form on `M × N` which factors on product frames: for tangent vectors `v₁, …, vₖ` at `x` and
`w₁, …, wₗ` at `y`, read in the tangent space at `(x, y)` through `Manifold.tangentSpaceProdEquiv`,

`φ_(x, y)((v₁, 0), …, (vₖ, 0), (0, w₁), …, (0, wₗ)) = φ₁_x(v₁, …, vₖ) φ₂_y(w₁, …, wₗ)`.

Then the measure `|φ|` of `TauCeti.RoughForm.measure` is the product measure `|φ₁| ⊗ |φ₂|`
(`TauCeti.RoughForm.measure_eq_prod`), provided `φ₁` and `φ₂` are continuous and `M`, `N` are
second countable. The symplectic volume form of a product form factors in this way
(`TauCeti.SmoothTwoForm.volumeForm_prod_apply_sumElim`), which gives the product formula for
Liouville measures.

In the preferred chart of `M × N`, the product of the preferred charts of `M` and `N`, the
coefficient of `φ` in the product of coordinate bases is the product of the coefficients of `φ₁`
and `φ₂` (`TauCeti.RoughForm.inChartAt_prod_apply_sumElim`). Since the coordinate measure
of `TauCeti.RoughForm.measure` does not depend on the basis used to normalize it, and the Haar
measure of a product basis is the product of the Haar measures, the two measures agree on products
of measurable subsets of chart sources (`Module.Basis.setLIntegral_ofReal_abs_apply_prod`).
Continuity of `φ₁` and `φ₂` and second countability of `M` and `N` make the factor measures
`|φ₁|` and `|φ₂|` `σ`-finite, so `|φ|` and `|φ₁| ⊗ |φ₂|` agree on each product chart source by
`MeasureTheory.Measure.prod_eq`, and these sources cover `M × N`.

## Main results

* `TauCeti.RoughForm.measure_eq_prod`: the measure of a factoring top form is the product measure.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16
  (densities and their integrals).
-/

public section

noncomputable section

open Module MeasureTheory Set
open scoped Manifold

namespace TauCeti

namespace RoughForm

variable {E H M F H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N] {k l p : ℕ}
  {φ : RoughForm (I.prod J) (M × N) ℝ p} {φ₁ : RoughForm I M ℝ k} {φ₂ : RoughForm J N ℝ l}

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology M] [SecondCountableTopology N] [hk : Fact (finrank ℝ E = k)]
  [hl : Fact (finrank ℝ F = l)] [Fact (finrank ℝ (E × F) = p)]

attribute [local instance] TauCeti.extChartAtMeasurableSpaceE TauCeti.extChartAtBorelSpaceE

/-- The measure of a factoring top form on a product of measurable subsets of chart sources is the
product of the measures. -/
private theorem measure_prod_of_subset (hp : k + l = p) (hφ₁ : IsSmoothForm I 0 φ₁)
    (hφ₂ : IsSmoothForm J 0 φ₂)
    (h : ∀ (x : M) (y : N) (v : Fin k → TangentSpace I x) (w : Fin l → TangentSpace J y),
      φ (x, y) (fun r ↦ (Manifold.tangentSpaceProdEquiv (x, y)).symm (Sum.elim (fun i ↦ (v i, 0))
        (fun j ↦ (0, w j)) (finSumFinEquiv.symm (Fin.cast hp.symm r)))) = φ₁ x v * φ₂ y w)
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
  rw [φ.measure_apply_of_subset (hs.prod ht) hsub, φ₁.measure_apply_of_subset hs hsα,
    φ₂.measure_apply_of_subset ht htβ, himage]
  -- The chart measurable structure on `E × F` is supplied explicitly: elaborating it by instance
  -- search would find the product structure and force an expensive unification.
  refine Basis.setLIntegral_ofReal_abs_apply_prod (mEF := TauCeti.extChartAtMeasurableSpaceE) hp
    _ b₁ b₂ (hs.image_extChartAt α hsα) (ht.image_extChartAt β htβ) _
    (aemeasurable_ofReal_abs_inChartAt hφ₁ b₁ hs hsα)
    (aemeasurable_ofReal_abs_inChartAt hφ₂ b₂ ht htβ) fun z hz ↦ ?_
  have hb : ((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr hp)) : Fin p → E × F) =
      fun r ↦ Sum.elim (fun i ↦ (b₁ i, 0)) (fun j ↦ (0, b₂ j))
        (finSumFinEquiv.symm (Fin.cast hp.symm r)) := by
    funext r
    simp only [Basis.reindex_apply, Basis.prod_apply, Equiv.symm_trans_apply, finCongr_symm,
      finCongr_apply]
    rcases finSumFinEquiv.symm (Fin.cast hp.symm r) with i | j <;> simp
  rw [hb, inChartAt_prod_apply_sumElim φ hp α β (hA₁ hz.1) (hA₂ hz.2), h, ← inChartAt_apply,
    ← inChartAt_apply, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]

/-- **The measure of a product of top forms is the product measure.** Let `φ₁` and `φ₂` be
continuous top forms on second countable manifolds `M` and `N` of dimensions `k` and `l`, and let
`φ` be a top form on `M × N` taking the value `φ₁_x(v) φ₂_y(w)` on every family
`(v₁, 0), …, (vₖ, 0), (0, w₁), …, (0, wₗ)` of tangent vectors at `(x, y)`. Then
`|φ| = |φ₁| ⊗ |φ₂|`. -/
theorem measure_eq_prod (hp : k + l = p) (hφ₁ : IsSmoothForm I 0 φ₁) (hφ₂ : IsSmoothForm J 0 φ₂)
    (h : ∀ (x : M) (y : N) (v : Fin k → TangentSpace I x) (w : Fin l → TangentSpace J y),
      φ (x, y) (fun r ↦ (Manifold.tangentSpaceProdEquiv (x, y)).symm (Sum.elim (fun i ↦ (v i, 0))
        (fun j ↦ (0, w j)) (finSumFinEquiv.symm (Fin.cast hp.symm r)))) = φ₁ x v * φ₂ y w) :
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
