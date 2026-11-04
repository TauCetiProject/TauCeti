/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Topology.Semicontinuity.Defs

import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Convolution existence and continuous linear maps

An essentially bounded function convolves with an integrable function at every point of a
measurable additive group with a measure invariant under left translations and negation
(`MeasureTheory.convolutionExists_of_ae_norm_le_of_integrable` and
`MeasureTheory.convolutionExists_of_integrable_of_ae_norm_le`). No topology on the group or
sigma-finiteness of the measure is required.

A continuous linear map `L : F →L[𝕜] F'` between real or complex Banach spaces commutes with
convolution against a scalar kernel `ρ : G → 𝕜`: `ρ ⋆ (L ∘ f) = L (ρ ⋆ f)` at every point where
`ρ ⋆ f` exists (`ContinuousLinearMap.convolution_lsmul_comp_comm`). This is the convolution form
of `ContinuousLinearMap.integral_comp_comm`. It lets a mollification be moved through a continuous
linear map, for instance to mollify the image of a function in a dual space.

Mollification by a nonnegative real kernel `ρ` of integral `1` supported in `ball 0 R` preserves
one-sided bounds: a lower (upper) bound on `g` over `ball x₀ R` is a lower (upper) bound on
`(ρ ⋆ g) x₀`, and a bound on the norm of a vector-valued `f` over `ball x₀ R` bounds the norm of
`(ρ ⋆ f) x₀`. So as the supports of the kernels shrink, the mollifications of a function lower
(upper) semicontinuous at `x₀` eventually lie almost above (below) its value there, and the minimum
(maximum) of the mollification and the function tends to that value.

A convolution `(f ⋆ g) x` only sees `g` at the points `x - t` with `t` in the support of `f`, so
`g` may be replaced by its indicator on any set containing them. Consequently, pairing a
convolution `ρ ⋆ u` with a continuous compactly supported `ψ` only involves `u` on the compact set
`tsupport ψ - tsupport ρ`, and Fubini moves the kernel outside:
`∫ ψ (ρ ⋆ u) = ∫ ρ(t) (∫ ψ(x) u(x - t) dx) dt` for `u` locally integrable near that set.

## Main declarations

* `MeasureTheory.convolutionExists_of_ae_norm_le_of_integrable`,
  `MeasureTheory.convolutionExists_of_integrable_of_ae_norm_le`: existence of `f ⋆ g` when one
  factor is integrable and the other essentially bounded.
* `ContinuousLinearMap.convolution_lsmul_comp_comm`: `ρ ⋆ (L ∘ f) = L (ρ ⋆ f)`.
* `MeasureTheory.le_convolution_lsmul_of_forall_le` and
  `MeasureTheory.convolution_lsmul_le_of_forall_le`: one-sided bounds on a ball pass to the
  mollification at its centre.
* `MeasureTheory.norm_convolution_lsmul_le_of_forall_norm_le`: a norm bound on a ball passes to the
  mollification at its centre.
* `MeasureTheory.eventually_lt_convolution_lsmul_of_lowerSemicontinuousAt` and
  `MeasureTheory.eventually_convolution_lsmul_lt_of_upperSemicontinuousAt`: mollification by
  shrinking kernels at a point of lower (upper) semicontinuity.
* `MeasureTheory.tendsto_min_convolution_lsmul_of_lowerSemicontinuousAt` and
  `MeasureTheory.tendsto_max_convolution_lsmul_of_upperSemicontinuousAt`: the minimum (maximum) of
  the mollification and the function converges to the value at a point of lower (upper)
  semicontinuity.
* `MeasureTheory.convolution_indicator_eq_of_forall_sub_mem`: replacing `g` by its indicator on a
  set containing `x - support f` does not change `(f ⋆ g) x`.
* `MeasureTheory.integral_mul_convolution_eq_integral_mul_integral_comp_sub`: the Fubini identity
  `∫ ψ (ρ ⋆ u) = ∫ ρ(t) (∫ ψ(x) u(x - t) dx) dt` for compactly supported `ψ` and `ρ`.
-/

public section

open MeasureTheory
open scoped Convolution

namespace MeasureTheory

variable {G E E' F : Type*} {f : G → E} {g : G → E'} {M : ℝ}

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [AddGroup G] [MeasurableSpace G]
  [MeasurableAdd G] [MeasurableNeg G] {μ : Measure G} [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
  (L : E →L[𝕜] E' →L[𝕜] F)

/-- An essentially bounded function convolves with an integrable function at every point. -/
theorem convolutionExists_of_ae_norm_le_of_integrable (hf : AEStronglyMeasurable f μ)
    (hfM : ∀ᵐ t ∂μ, ‖f t‖ ≤ M) (hg : Integrable g μ) : ConvolutionExists f g L μ := fun x => by
  simpa only [ConvolutionExistsAt, Function.comp_def] using
    L.integrable_of_bilin_of_bdd_left M hf hfM (hg.comp_sub_left x)

/-- An integrable function convolves with an essentially bounded function at every point. -/
theorem convolutionExists_of_integrable_of_ae_norm_le (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (hgM : ∀ᵐ t ∂μ, ‖g t‖ ≤ M) : ConvolutionExists f g L μ :=
  fun x => by
    have hsub := (Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving
    simpa only [ConvolutionExistsAt, Function.comp_def] using
      L.integrable_of_bilin_of_bdd_right M hf (hg.comp_quasiMeasurePreserving hsub) (hsub.ae hgM)

end MeasureTheory

/-- A continuous linear map commutes with convolution against a scalar kernel, at every point
where the convolution exists. -/
theorem ContinuousLinearMap.convolution_lsmul_comp_comm {𝕜 G F F' : Type*} [RCLike 𝕜] [Sub G]
    [MeasurableSpace G] {μ : Measure G} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
    [CompleteSpace F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedSpace ℝ F']
    [CompleteSpace F'] (L : F →L[𝕜] F') {ρ : G → 𝕜} {f : G → F} {x : G}
    (h : ConvolutionExistsAt ρ f x (ContinuousLinearMap.lsmul 𝕜 𝕜) μ) :
    (ρ ⋆[ContinuousLinearMap.lsmul 𝕜 𝕜, μ] fun y ↦ L (f y)) x =
      L ((ρ ⋆[ContinuousLinearMap.lsmul 𝕜 𝕜, μ] f) x) := by
  simpa only [convolution_lsmul, ContinuousLinearMap.lsmul_apply, map_smul] using
    L.integral_comp_comm h.integrable

namespace MeasureTheory

open ContinuousLinearMap Filter Metric Topology

section OneSided

variable {G : Type*} [SeminormedAddCommGroup G] [MeasurableSpace G] {μ : Measure G}
  {ρ g : G → ℝ} {x₀ : G} {R c : ℝ}

/-- **Lower bounds survive mollification.** If `ρ` is a nonnegative kernel of integral `1`
supported in `ball 0 R` and `c ≤ g` on `ball x₀ R`, then `c ≤ (ρ ⋆ g) x₀`. -/
theorem le_convolution_lsmul_of_forall_le (hρs : Function.support ρ ⊆ ball 0 R)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y ∂μ = 1) (hg : ConvolutionExistsAt ρ g x₀ (lsmul ℝ ℝ) μ)
    (h : ∀ y ∈ ball x₀ R, c ≤ g y) : c ≤ (ρ ⋆[lsmul ℝ ℝ, μ] g) x₀ := by
  calc c = ∫ y, ρ y * c ∂μ := by rw [integral_mul_const, hρ1, one_mul]
    _ ≤ (ρ ⋆[lsmul ℝ ℝ, μ] g) x₀ := by
      rw [convolution_def]
      refine integral_mono ((integrable_of_integral_eq_one hρ1).mul_const c) hg.integrable
        fun y ↦ ?_
      by_cases hy : ρ y = 0
      · simp [hy]
      have hy' : y ∈ ball (0 : G) R := hρs hy
      rw [mem_ball_zero_iff] at hy'
      exact mul_le_mul_of_nonneg_left (h _ (by simpa [dist_eq_norm] using hy')) (hρ0 y)

/-- **Upper bounds survive mollification.** If `ρ` is a nonnegative kernel of integral `1`
supported in `ball 0 R` and `g ≤ c` on `ball x₀ R`, then `(ρ ⋆ g) x₀ ≤ c`. -/
theorem convolution_lsmul_le_of_forall_le (hρs : Function.support ρ ⊆ ball 0 R)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y ∂μ = 1) (hg : ConvolutionExistsAt ρ g x₀ (lsmul ℝ ℝ) μ)
    (h : ∀ y ∈ ball x₀ R, g y ≤ c) : (ρ ⋆[lsmul ℝ ℝ, μ] g) x₀ ≤ c := by
  have hneg : (ρ ⋆[lsmul ℝ ℝ, μ] fun y ↦ -g y) x₀ = -(ρ ⋆[lsmul ℝ ℝ, μ] g) x₀ := by
    simp [convolution_def, integral_neg]
  have := le_convolution_lsmul_of_forall_le (c := -c) (g := fun y ↦ -g y) hρs hρ0 hρ1
    (by simpa [ConvolutionExistsAt] using hg.integrable.neg) fun y hy ↦ neg_le_neg (h y hy)
  linarith

/-- **Sup-norm bounds survive mollification.** If `ρ` is a nonnegative kernel of integral `1`
supported in `ball 0 R` and `‖f‖ ≤ M` on `ball x₀ R`, then `‖(ρ ⋆ f) x₀‖ ≤ M`. -/
theorem norm_convolution_lsmul_le_of_forall_norm_le {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [CompleteSpace E'] [BorelSpace G] [SecondCountableTopology G]
    [μ.IsAddLeftInvariant] [SFinite μ] {f : G → E'} {M : ℝ}
    (hρs : Function.support ρ ⊆ ball 0 R) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y ∂μ = 1)
    (hf : AEStronglyMeasurable f μ) (h : ∀ y ∈ ball x₀ R, ‖f y‖ ≤ M) :
    ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x₀‖ ≤ M := by
  -- The kernel has integral `1`, so its support, and hence `ball 0 R`, is nonempty.
  have hR : 0 < R := by
    by_contra hR
    have hρ : ρ = 0 := Function.support_eq_empty_iff.1
      (Set.subset_empty_iff.1 (hρs.trans (ball_eq_empty.2 (not_lt.1 hR)).subset))
    simp [hρ] at hρ1
  simpa using dist_convolution_le (z₀ := (0 : E'))
    ((norm_nonneg _).trans (h x₀ (mem_ball_self hR))) hρs hρ0 hρ1 hf
    (fun y hy ↦ by simpa using h y hy)

variable {ι : Type*} {l : Filter ι} {ρ : ι → G → ℝ}

/-- **Mollification and lower semicontinuity.** Let `ρ i` be nonnegative kernels of integral `1`
whose supports shrink to `0`. If `g` is lower semicontinuous at `x₀`, then every `c < g x₀` is
eventually below `(ρ i ⋆ g) x₀`. -/
theorem eventually_lt_convolution_lsmul_of_lowerSemicontinuousAt
    (hρ0 : ∀ᶠ i in l, ∀ y, 0 ≤ ρ i y) (hρ1 : ∀ᶠ i in l, ∫ y, ρ i y ∂μ = 1)
    (hρs : Tendsto (fun i ↦ Function.support (ρ i)) l (𝓝 0).smallSets)
    (hg : ∀ᶠ i in l, ConvolutionExistsAt (ρ i) g x₀ (lsmul ℝ ℝ) μ)
    (hgx : LowerSemicontinuousAt g x₀) (hc : c < g x₀) :
    ∀ᶠ i in l, c < (ρ i ⋆[lsmul ℝ ℝ, μ] g) x₀ := by
  obtain ⟨c', hcc', hc'⟩ := exists_between hc
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 (hgx c' hc')
  filter_upwards [hρ0, hρ1, hg, tendsto_smallSets_iff.1 hρs _ (ball_mem_nhds 0 hr)]
    with i h0 h1 hgi hsi
  exact hcc'.trans_le (le_convolution_lsmul_of_forall_le hsi h0 h1 hgi fun y hy ↦ (hrs hy).le)

/-- **Mollification and upper semicontinuity.** Let `ρ i` be nonnegative kernels of integral `1`
whose supports shrink to `0`. If `g` is upper semicontinuous at `x₀`, then every `c > g x₀` is
eventually above `(ρ i ⋆ g) x₀`. -/
theorem eventually_convolution_lsmul_lt_of_upperSemicontinuousAt
    (hρ0 : ∀ᶠ i in l, ∀ y, 0 ≤ ρ i y) (hρ1 : ∀ᶠ i in l, ∫ y, ρ i y ∂μ = 1)
    (hρs : Tendsto (fun i ↦ Function.support (ρ i)) l (𝓝 0).smallSets)
    (hg : ∀ᶠ i in l, ConvolutionExistsAt (ρ i) g x₀ (lsmul ℝ ℝ) μ)
    (hgx : UpperSemicontinuousAt g x₀) (hc : g x₀ < c) :
    ∀ᶠ i in l, (ρ i ⋆[lsmul ℝ ℝ, μ] g) x₀ < c := by
  obtain ⟨c', hc', hcc'⟩ := exists_between hc
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 (hgx c' hc')
  filter_upwards [hρ0, hρ1, hg, tendsto_smallSets_iff.1 hρs _ (ball_mem_nhds 0 hr)]
    with i h0 h1 hgi hsi
  exact (convolution_lsmul_le_of_forall_le hsi h0 h1 hgi fun y hy ↦ (hrs hy).le).trans_lt hcc'

/-- **Mollification and lower semicontinuity, in the limit.** Let `ρ i` be nonnegative kernels of
integral `1` whose supports shrink to `0`. If `g` is lower semicontinuous at `x₀`, then
`min ((ρ i ⋆ g) x₀) (g x₀)` tends to `g x₀`. -/
theorem tendsto_min_convolution_lsmul_of_lowerSemicontinuousAt
    (hρ0 : ∀ᶠ i in l, ∀ y, 0 ≤ ρ i y) (hρ1 : ∀ᶠ i in l, ∫ y, ρ i y ∂μ = 1)
    (hρs : Tendsto (fun i ↦ Function.support (ρ i)) l (𝓝 0).smallSets)
    (hg : ∀ᶠ i in l, ConvolutionExistsAt (ρ i) g x₀ (lsmul ℝ ℝ) μ)
    (hgx : LowerSemicontinuousAt g x₀) :
    Tendsto (fun i ↦ min ((ρ i ⋆[lsmul ℝ ℝ, μ] g) x₀) (g x₀)) l (𝓝 (g x₀)) :=
  tendsto_order.2 ⟨fun _ hc ↦ (eventually_lt_convolution_lsmul_of_lowerSemicontinuousAt hρ0 hρ1
    hρs hg hgx hc).mono fun _ hi ↦ lt_min hi hc,
    fun _ hc ↦ .of_forall fun _ ↦ (min_le_right _ _).trans_lt hc⟩

/-- **Mollification and upper semicontinuity, in the limit.** Let `ρ i` be nonnegative kernels of
integral `1` whose supports shrink to `0`. If `g` is upper semicontinuous at `x₀`, then
`max ((ρ i ⋆ g) x₀) (g x₀)` tends to `g x₀`. -/
theorem tendsto_max_convolution_lsmul_of_upperSemicontinuousAt
    (hρ0 : ∀ᶠ i in l, ∀ y, 0 ≤ ρ i y) (hρ1 : ∀ᶠ i in l, ∫ y, ρ i y ∂μ = 1)
    (hρs : Tendsto (fun i ↦ Function.support (ρ i)) l (𝓝 0).smallSets)
    (hg : ∀ᶠ i in l, ConvolutionExistsAt (ρ i) g x₀ (lsmul ℝ ℝ) μ)
    (hgx : UpperSemicontinuousAt g x₀) :
    Tendsto (fun i ↦ max ((ρ i ⋆[lsmul ℝ ℝ, μ] g) x₀) (g x₀)) l (𝓝 (g x₀)) :=
  tendsto_order.2 ⟨fun _ hc ↦ .of_forall fun _ ↦ hc.trans_le (le_max_right _ _),
    fun _ hc ↦ (eventually_convolution_lsmul_lt_of_upperSemicontinuousAt hρ0 hρ1 hρs hg hgx
      hc).mono fun _ hi ↦ max_lt hi hc⟩

end OneSided

section Support

variable {𝕜 G E E' F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedSpace ℝ F]

/-- A convolution at `x` sees `g` only at the points `x - t` with `t` in the support of the
kernel `f`, so `g` may be replaced by its indicator on any set containing all of them. -/
theorem convolution_indicator_eq_of_forall_sub_mem [Sub G] [MeasurableSpace G] {μ : Measure G}
    (L : E →L[𝕜] E' →L[𝕜] F) {f : G → E} {g : G → E'} {s : Set G} {x : G}
    (h : ∀ t ∈ Function.support f, x - t ∈ s) :
    (f ⋆[L, μ] s.indicator g) x = (f ⋆[L, μ] g) x := by
  simp only [convolution_def]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  by_cases ht : f t = 0
  · simp [ht]
  · simp only [Set.indicator_of_mem (h t ht)]

end Support

section Fubini

variable {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {μ : Measure G}

/-- **Pairing a convolution with a test function.** For a continuous compactly supported `ψ`, an
integrable compactly supported kernel `ρ` and a function `u` locally integrable on a set `s`
containing `tsupport ψ - tsupport ρ`, Fubini gives
`∫ ψ (ρ ⋆ u) = ∫ ρ(t) (∫ ψ(x) u(x - t) dx) dt`. -/
theorem integral_mul_convolution_eq_integral_mul_integral_comp_sub [SFinite μ]
    [μ.IsAddRightInvariant] {ψ ρ u : G → ℝ} {s : Set G} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hρ : Integrable ρ μ) (hρc : HasCompactSupport ρ)
    (hu : LocallyIntegrableOn u s μ) (hs : ∀ t ∈ tsupport ρ, ∀ x ∈ tsupport ψ, x - t ∈ s) :
    ∫ x, ψ x * (ρ ⋆[lsmul ℝ ℝ, μ] u) x ∂μ = ∫ t, ρ t * ∫ x, ψ x * u (x - t) ∂μ ∂μ := by
  -- Only the values of `u` on the compact set `K = tsupport ψ - tsupport ρ ⊆ s` enter either
  -- side, and `u` is integrable there.
  set K := (fun p : G × G ↦ p.1 - p.2) '' (tsupport ψ ×ˢ tsupport ρ)
  have hK : IsCompact K := (hψc.isCompact.prod hρc.isCompact).image (by fun_prop)
  have hKs : K ⊆ s := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact hs t ht x hx
  have hmem {x t : G} (hx : ψ x ≠ 0) (ht : ρ t ≠ 0) : x - t ∈ K :=
    Set.mem_image_of_mem _ (Set.mk_mem_prod (subset_tsupport _ hx) (subset_tsupport _ ht))
  have hw : Integrable (K.indicator u) μ :=
    (hu.integrableOn_compact_subset hKs hK).integrable_indicator hK.measurableSet
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hψc
  have hint : Integrable (fun p : G × G ↦ ψ p.1 * (ρ p.2 * K.indicator u (p.1 - p.2)))
      (μ.prod μ) :=
    (hρ.convolution_integrand (lsmul ℝ ℝ) hw).bdd_mul
      (hψ.comp continuous_fst).aestronglyMeasurable (.of_forall fun p ↦ hC p.1)
  calc ∫ x, ψ x * (ρ ⋆[lsmul ℝ ℝ, μ] u) x ∂μ
      = ∫ x, ∫ t, ψ x * (ρ t * K.indicator u (x - t)) ∂μ ∂μ := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        by_cases hx : ψ x = 0
        · simp [hx]
        rw [← convolution_indicator_eq_of_forall_sub_mem _ fun t ht ↦ hmem hx ht]
        simp only [convolution_lsmul, smul_eq_mul, ← integral_const_mul]
    _ = ∫ t, ∫ x, ψ x * (ρ t * K.indicator u (x - t)) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ t, ρ t * ∫ x, ψ x * u (x - t) ∂μ ∂μ := by
        refine integral_congr_ae (.of_forall fun t ↦ ?_)
        dsimp only
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        by_cases hx : ψ x = 0
        · simp [hx]
        by_cases ht : ρ t = 0
        · simp [ht]
        rw [Set.indicator_of_mem (hmem hx ht), mul_left_comm]

end Fubini

end MeasureTheory
