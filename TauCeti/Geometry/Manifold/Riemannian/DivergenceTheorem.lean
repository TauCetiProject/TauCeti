/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Calculus.FDeriv.Integral
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Divergence

/-!
# The divergence theorem on a manifold without boundary

On a smooth manifold without boundary with a `C¹` Riemannian metric, the divergence of a
compactly supported `C¹` vector field has integral zero against the Riemannian volume:

`∫ div X dV = 0`.

Integrating the product rule `div (f X) = f div X + df(X)` then gives the integration-by-parts
formulas for the divergence and the Laplace–Beltrami operator `Δ = div ∘ grad`:

`∫ f div X dV = -∫ df(X) dV`, `∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV`, `∫ f Δg dV = ∫ (Δf) g dV`.

These identities underlie the energy (weak) formulation of second-order operators on closed
manifolds. No orientation is used: the measure is the orientation-free `TauCeti.riemannianVolume`.

## Main results

* `TauCeti.Manifold.integral_divergence_eq_zero`: the divergence theorem `∫ div X dV = 0`.
* `TauCeti.Manifold.integral_mul_divergence`,
  `TauCeti.Manifold.integral_mul_divergence_of_hasCompactSupport_right`:
  `∫ f div X dV = -∫ df(X) dV` when `f` or `X` has compact support.
* `TauCeti.Manifold.integral_mul_laplaceBeltrami`: Green's first identity
  `∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV`.
* `TauCeti.Manifold.integral_mul_laplaceBeltrami_right_eq_left`: Green's second identity
  `∫ f Δg dV = ∫ (Δf) g dV`.
* `TauCeti.Manifold.integrable_divergence`: the divergence of a compactly supported `C¹` field is
  integrable.

## Implementation notes

The proof is chart by chart. In the chart at `α`, with chart frame `e₁, …, eₙ`, volume density `ρ`
and frame coefficients `Xᵏ`, the coordinate formula `ρ div X = ∑ₖ ∂ₖ (ρ Xᵏ)`
(`TauCeti.chartVolumeDensity_mul_divergence`) turns the integral of the divergence of a field
supported in the chart into a sum of integrals of partial derivatives of compactly supported `C¹`
functions on the model space, each of which vanishes. A smooth partition of unity subordinate to
the chart sources reduces a general compactly supported field to finitely many such fields; this
is where the manifold is assumed smooth, while the metric need only be `C¹`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Chapter 16 (the divergence theorem, Theorem 16.32, and Green's identities).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (the divergence and the Riemannian density).
-/

public section

noncomputable section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Chart

variable [IsManifold I 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {α : M} {X : (x : M) → TangentSpace I x}

/-- The `k`-th coefficient of `ρ X` in the chart frame at `α`, read in coordinates and extended by
zero off the chart target. Here `ρ` is the chart volume density. -/
private def chartFlux (α : M) (X : (x : M) → TangentSpace I x)
    (k : Fin (Module.finrank ℝ E)) : E → ℝ :=
  (extChartAt I α).target.indicator fun z ↦
    chartVolumeDensity (I := I) α ((extChartAt I α).symm z) *
      (trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k
        ((extChartAt I α).symm z) (X ((extChartAt I α).symm z))

omit [I.Boundaryless] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The fluxes vanish off the coordinate image of the support of `X`. -/
private theorem chartFlux_eq_zero (k : Fin (Module.finrank ℝ E)) {z : E}
    (hz : z ∉ extChartAt I α '' tsupport (α := E) X) : chartFlux α X k z = 0 := by
  by_cases ht : z ∈ (extChartAt I α).target
  · have hX : X ((extChartAt I α).symm z) = 0 :=
      image_eq_zero_of_notMem_tsupport (α := E) fun h ↦
        hz ⟨_, h, (extChartAt I α).right_inv ht⟩
    simp only [chartFlux, indicator_of_mem ht, hX, map_zero, mul_zero]
  · exact indicator_of_notMem ht _

omit [I.Boundaryless] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The fluxes vanish near every point off the compact coordinate image of the support of `X`. -/
private theorem chartFlux_eventuallyEq_zero (hK : IsCompact (extChartAt I α '' tsupport (α := E) X))
    (k : Fin (Module.finrank ℝ E)) {z : E}
    (hz : z ∉ extChartAt I α '' tsupport (α := E) X) : chartFlux α X k =ᶠ[𝓝 z] 0 :=
  Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hz) fun _ h ↦ chartFlux_eq_zero k h

omit [I.Boundaryless] in
/-- The product of the chart volume density and a frame coefficient of a `C¹` field is `C¹` on the
chart source. -/
private theorem contMDiffOn_chartVolumeDensity_mul_localFrameCoeff
    (hX : ContMDiff I I.tangent 1 (T% X)) (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) 1 (fun y ↦ chartVolumeDensity (I := I) α y *
      (trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k y (X y))
      (chartAt H α).source := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have hs : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source := by simp
  have h1 := contMDiffOn_chartVolumeDensity (I := I) (n := 1) α
  have h2 := contMDiffOn_baseSet_localFrameCoeff (I := I)
    (e := trivializationAt E (TangentSpace I) α) (Module.finBasis ℝ E) (k := 1) hX.contMDiffOn k
  rw [hs] at h1 h2
  exact h1.mul h2

/-- The fluxes of a `C¹` field whose support has compact coordinate image inside the chart target
are `C¹` on the model space. -/
private theorem contDiff_chartFlux (hX : ContMDiff I I.tangent 1 (T% X))
    (hKc : IsCompact (extChartAt I α '' tsupport (α := E) X))
    (himage : extChartAt I α '' tsupport (α := E) X ⊆ (extChartAt I α).target)
    (k : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ 1 (chartFlux α X k) := by
  have hon : ContDiffOn ℝ 1 (chartFlux α X k) (extChartAt I α).target := by
    have h := (contMDiffOn_chartVolumeDensity_mul_localFrameCoeff hX k).comp
      (contMDiffOn_extChartAt_symm (n := 1) α) fun z hz ↦ by
        rw [mem_preimage, ← extChartAt_source (I := I)]
        exact (extChartAt I α).map_target hz
    exact (contMDiffOn_iff_contDiffOn.1 h).congr fun z hz ↦ indicator_of_mem hz _
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  by_cases hz : z ∈ (extChartAt I α).target
  · exact hon.contDiffAt ((isOpen_extChartAt_target α).mem_nhds hz)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (chartFlux_eventuallyEq_zero hKc k fun h ↦ hz (himage h))

/-- On the chart target, the coordinate divergence of the fluxes is `ρ div X` read in the chart.
This is the coordinate formula `ρ div X = ∑ₖ ∂ₖ (ρ Xᵏ)` written in coordinates. -/
private theorem sum_fderiv_chartFlux (hX : ContMDiff I I.tangent 1 (T% X)) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    ∑ k, fderiv ℝ (chartFlux α X k) z (Module.finBasis ℝ E k) =
      chartVolumeDensity (I := I) α ((extChartAt I α).symm z) *
        divergence I X ((extChartAt I α).symm z) := by
  have hy : (extChartAt I α).symm z ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I α).map_target hz
  rw [chartVolumeDensity_mul_divergence α (by simpa using hy)
    ((hX _).mdifferentiableAt one_ne_zero)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mvfderiv_chartLocalFrame α hy
    ((contMDiffOn_chartVolumeDensity_mul_localFrameCoeff hX k).contMDiffAt
      ((chartAt H α).open_source.mem_nhds hy) |>.mdifferentiableAt one_ne_zero),
    (extChartAt I α).right_inv hz]
  have h : chartFlux α X k =ᶠ[𝓝 z] _ :=
    Filter.eventually_of_mem ((isOpen_extChartAt_target α).mem_nhds hz) fun z' hz' ↦
      indicator_of_mem hz' _
  rw [h.fderiv_eq, Function.comp_def]

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

omit [I.Boundaryless] in
/-- The divergence of a compactly supported `C¹` vector field is integrable against the Riemannian
volume. -/
theorem integrable_divergence (hX : ContMDiff I I.tangent 1 (T% X))
    (hc : HasCompactSupport (β := E) X) :
    Integrable (divergence I X) (riemannianVolume I M) :=
  (contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num) (by norm_num)
    (by simpa using hX)).continuous.integrable_of_hasCompactSupport
      (hc.mono' fun x hx ↦ by_contra fun h ↦ hx (divergence_eq_zero_of_notMem_tsupport I h))

/-- The divergence theorem for a compactly supported field whose support lies in one chart. -/
private theorem integral_divergence_eq_zero_of_tsupport_subset
    (hX : ContMDiff I I.tangent 1 (T% X)) (hK : IsCompact (tsupport (α := E) X))
    (hKs : tsupport (α := E) X ⊆ (chartAt H α).source) :
    ∫ x, divergence I X x ∂riemannianVolume I M = 0 := by
  have hKs' : tsupport (α := E) X ⊆ (extChartAt I α).source := by rwa [extChartAt_source]
  have hKc := hK.image_of_continuousOn ((continuousOn_extChartAt α).mono hKs')
  have himage := ((extChartAt I α).mapsTo.mono_left hKs').image_subset
  have hflux (k : Fin (Module.finrank ℝ E)) := contDiff_chartFlux hX hKc himage k
  have hfluxc (k : Fin (Module.finrank ℝ E)) : HasCompactSupport (chartFlux α X k) :=
    HasCompactSupport.intro hKc fun _ hz ↦ chartFlux_eq_zero k hz
  have hint (k : Fin (Module.finrank ℝ E)) :
      Integrable (fun z ↦ fderiv ℝ (chartFlux α X k) z (Module.finBasis ℝ E k))
        (Module.finBasis ℝ E).addHaar :=
    ((hflux k).continuous_fderiv one_ne_zero).clm_apply continuous_const
      |>.integrable_of_hasCompactSupport ((hfluxc k).fderiv_apply ℝ _)
  -- Move the integral to the chart target, where the integrand is the coordinate divergence of
  -- the fluxes, and then to the whole model space, off whose target the fluxes vanish nearby.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (chartAt H α).source) fun x hx ↦
      divergence_eq_zero_of_notMem_tsupport I fun h ↦ hx (hKs h),
    setIntegral_riemannianVolume_of_subset subset_rfl (chartAt H α).open_source.measurableSet,
    ← extChartAt_source (I := I), (extChartAt I α).image_source_eq_target]
  simp_rw [smul_eq_mul]
  rw [setIntegral_congr_fun (isOpen_extChartAt_target α).measurableSet fun z hz ↦
      (sum_fderiv_chartFlux hX hz).symm,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ Finset.sum_eq_zero fun k _ ↦ by
      rw [(chartFlux_eventuallyEq_zero hKc k fun h ↦ hz (himage h)).fderiv_eq]
      simp,
    integral_finsetSum _ fun k _ ↦ hint k]
  -- Each partial derivative of a compactly supported `C¹` function integrates to zero.
  exact Finset.sum_eq_zero fun k _ ↦ integral_apply_eq_zero_of_hasFDerivAt_off_countable
    countable_empty (hflux k).continuous (hfluxc k)
    (fun z _ ↦ ((hflux k).differentiable one_ne_zero z).hasFDerivAt) _ (hint k)

end Chart

variable [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {X : (x : M) → TangentSpace I x}

/-- **The divergence theorem** on a manifold without boundary: the divergence of a compactly
supported `C¹` vector field has integral zero against the Riemannian volume. -/
theorem integral_divergence_eq_zero (hX : ContMDiff I I.tangent 1 (T% X))
    (hc : HasCompactSupport (β := E) X) :
    ∫ x, divergence I X x ∂riemannianVolume I M = 0 := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M
  -- Only finitely many members of the partition meet the support of `X`.
  have hfin := ρ.toPartitionOfUnity.locallyFinite_tsupport.finite_nonempty_inter_compact hc
  set s := hfin.toFinset
  have hmem (i x : M) (hρx : ρ i x ≠ 0) (hXx : X x ≠ 0) : i ∈ s :=
    hfin.mem_toFinset.mpr ⟨x, subset_tsupport (ρ i) hρx, subset_tsupport (α := E) X hXx⟩
  have hsum (x : M) : X x = ∑ i ∈ s, ρ i x • X x := by
    by_cases hx : X x = 0
    · simp [hx]
    · have hs : ρ.finsupport x ⊆ s := fun i hi ↦
        hmem i x (by simpa only [SmoothPartitionOfUnity.mem_finsupport, Function.mem_support]
          using hi) hx
      rw [← Finset.sum_smul, ρ.sum_finsupport' x (mem_univ x) hs, one_smul]
  have hY (i : M) : ContMDiff I I.tangent 1 (T% (fun x ↦ ρ i x • X x)) :=
    ((ρ i).contMDiff.of_le (by simp)).smul_section hX
  have hK (i : M) : IsCompact (tsupport (α := E) (fun x ↦ ρ i x • X x)) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _)
  have hdiv (x : M) :
      divergence I X x = ∑ i ∈ s, divergence I (fun x ↦ ρ i x • X x) x := by
    rw [← divergence_finsetSum I s _ x fun i _ ↦ (hY i x).mdifferentiableAt one_ne_zero]
    exact congrArg (divergence I · x) (funext hsum)
  rw [integral_congr_ae (Filter.Eventually.of_forall hdiv),
    integral_finsetSum _ fun i _ ↦ integrable_divergence (hY i) (hK i)]
  exact Finset.sum_eq_zero fun i _ ↦ integral_divergence_eq_zero_of_tsupport_subset (hY i)
    (hK i) ((tsupport_smul_subset_left _ _).trans (hρ i))

/-- Integration by parts for the divergence, assuming that `f X` has compact support and that
`f div X` is integrable. -/
private theorem integral_mul_divergence_of_integrable {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (hfXc : HasCompactSupport (β := E) (fun x ↦ f x • X x))
    (hint : Integrable (fun x ↦ f x * divergence I X x) (riemannianVolume I M)) :
    ∫ x, f x * divergence I X x ∂riemannianVolume I M =
      -∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M := by
  have hfX : ContMDiff I I.tangent 1 (T% (fun x ↦ f x • X x)) := hf.smul_section hX
  have hpt (x : M) : divergence I (fun x ↦ f x • X x) x =
      f x * divergence I X x + mvfderiv I f x (X x) :=
    divergence_smul_function I f X x ((hf x).mdifferentiableAt one_ne_zero)
      ((hX x).mdifferentiableAt one_ne_zero)
  have hint' : Integrable (fun x ↦ mvfderiv I f x (X x)) (riemannianVolume I M) :=
    ((integrable_divergence hfX hfXc).sub hint).congr
      (Filter.Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply, hpt]; ring)
  have h := integral_divergence_eq_zero hfX hfXc
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hint hint'] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **Integration by parts for the divergence**: for a compactly supported `C¹` function `f` and a
`C¹` vector field `X` on a manifold without boundary, `∫ f div X dV = -∫ df(X) dV`. -/
theorem integral_mul_divergence {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hfc : HasCompactSupport f) (hX : ContMDiff I I.tangent 1 (T% X)) :
    ∫ x, f x * divergence I X x ∂riemannianVolume I M =
      -∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M :=
  integral_mul_divergence_of_integrable hf hX
    (hfc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _))
    ((hf.continuous.mul (contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num)
      (by norm_num) (by simpa using hX)).continuous).integrable_of_hasCompactSupport hfc.mul_right)

/-- **Integration by parts for the divergence**, for a compactly supported field: for a `C¹`
function `f` and a compactly supported `C¹` vector field `X` on a manifold without boundary,
`∫ f div X dV = -∫ df(X) dV`. -/
theorem integral_mul_divergence_of_hasCompactSupport_right {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) 1 f) (hX : ContMDiff I I.tangent 1 (T% X))
    (hXc : HasCompactSupport (β := E) X) :
    ∫ x, f x * divergence I X x ∂riemannianVolume I M =
      -∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M :=
  integral_mul_divergence_of_integrable hf hX
    (hXc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _))
    ((hf.continuous.mul (contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num)
      (by norm_num) (by simpa using hX)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hXc.mono' fun x hx ↦
        by_contra fun h ↦ hx (divergence_eq_zero_of_notMem_tsupport I h))))

/-- **Green's first identity** on a manifold without boundary: for a compactly supported `C¹`
function `f` and a `C²` function `g`, `∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV`. -/
theorem integral_mul_laplaceBeltrami {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hfc : HasCompactSupport f) (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    ∫ x, f x * laplaceBeltrami I g x ∂riemannianVolume I M =
      -∫ x, inner ℝ (mgradient I f x) (mgradient I g x) ∂riemannianVolume I M := by
  have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  simp only [laplaceBeltrami_def, inner_mgradient]
  exact integral_mul_divergence hf hfc (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two]))

/-- **Green's second identity** on a manifold without boundary: for a compactly supported `C²`
function `f` and a `C²` function `g`, `∫ f Δg dV = ∫ (Δf) g dV`. -/
theorem integral_mul_laplaceBeltrami_right_eq_left {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hfc : HasCompactSupport f) (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    ∫ x, f x * laplaceBeltrami I g x ∂riemannianVolume I M =
      ∫ x, laplaceBeltrami I f x * g x ∂riemannianVolume I M := by
  have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  -- The gradient of `f` vanishes off the support of `f`, so it is compactly supported.
  have hgradc : HasCompactSupport (β := E) (mgradient I f) :=
    hfc.mono' fun x hx ↦ by_contra fun h ↦ hx <| mgradient_eq_zero_iff.2 <|
      (notMem_tsupport_iff_eventuallyEq.1 h).mvfderiv_eq.trans mvfderiv_zero
  simp_rw [mul_comm (laplaceBeltrami I f _), laplaceBeltrami_def]
  rw [integral_mul_divergence (hf.of_le (by norm_num)) hfc
      (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])),
    integral_mul_divergence_of_hasCompactSupport_right (hg.of_le (by norm_num))
      (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])) hgradc]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  exact (inner_mgradient_right _).symm.trans (inner_mgradient _)

end TauCeti.Manifold
