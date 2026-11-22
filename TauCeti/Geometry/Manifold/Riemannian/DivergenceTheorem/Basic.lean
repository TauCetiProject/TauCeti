/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Analysis.Calculus.FDeriv.Integral
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Divergence
import TauCeti.Geometry.Manifold.VectorField.Chart.Flux
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame

/-!
# The divergence theorem on a manifold without boundary

On a `C²` manifold without boundary with a `C¹` Riemannian metric, the divergence of a
compactly supported `C¹` vector field has integral zero against the Riemannian volume:

`∫ div X dV = 0`.

Integrating the product rule `div (f X) = f div X + df(X)` then gives the integration-by-parts
formulas for the divergence and the Laplace–Beltrami operator `Δ = div ∘ grad`:

`∫ f div X dV = -∫ df(X) dV`, `∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV`, `∫ f Δg dV = ∫ (Δf) g dV`.

These identities underlie the energy (weak) formulation of second-order operators on closed
manifolds. No orientation is used: the measure is the orientation-free `TauCeti.riemannianVolume`.

## Main results

* `TauCeti.Manifold.integral_divergence_eq_zero`: the divergence theorem `∫ div X dV = 0`.
* `TauCeti.Manifold.integral_laplaceBeltrami_eq_zero`: `∫ Δf dV = 0` for a compactly supported
  `C²` function `f`.
* `TauCeti.Manifold.integral_mul_divergence`,
  `TauCeti.Manifold.integral_mul_divergence_of_hasCompactSupport_right`:
  `∫ f div X dV = -∫ df(X) dV` when `f` or `X` has compact support.
* `TauCeti.Manifold.integral_mvfderiv_mul`: integration by parts along a vector field,
  `∫ df(X) g dV = -∫ f (dg(X) + (div X) g) dV` when `f` or `g` has compact support.
* `TauCeti.Manifold.integral_mul_laplaceBeltrami`: Green's first identity
  `∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV`.
* `TauCeti.Manifold.integral_mul_laplaceBeltrami_right_eq_left`: Green's second identity
  `∫ f Δg dV = ∫ (Δf) g dV`.
* `TauCeti.Manifold.integral_mul_eq_zero_of_laplaceBeltrami_eq_neg_mul`: `L²`-orthogonality of
  `C²` Laplace–Beltrami eigenfunctions with distinct eigenvalues.
* `TauCeti.Manifold.integrable_divergence`: the divergence of a compactly supported `C¹` field is
  integrable.

## Implementation notes

The proof is chart by chart. In the chart at `α`, with chart frame `e₁, …, eₙ`, volume density `ρ`
and frame coefficients `Xᵏ`, the coordinate formula `ρ div X = ∑ₖ ∂ₖ (ρ Xᵏ)`
(`TauCeti.chartVolumeDensity_mul_divergence`) turns the integral of the divergence of a field
supported in the chart into a sum of integrals of partial derivatives of compactly supported `C¹`
functions on the model space, each of which vanishes. A finite partition of unity built from
`IsCompact.exists_smoothBumpCovering_isSubordinate` reduces a general compactly supported field to
finitely many such fields on any `C²` Hausdorff Lindelöf manifold with a `C¹` metric.

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

section Helpers

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

private lemma contMDiff_smoothBumpFunction [IsManifold I 1 M] [T2Space M] {x : M}
    (φ : SmoothBumpFunction I x) : ContMDiff I 𝓘(ℝ) 1 φ := by
  refine contMDiff_of_tsupport fun y hy ↦ ?_
  have hsrc : y ∈ (chartAt H x).source := φ.tsupport_subset_chartAt_source hy
  refine ContMDiffAt.congr_of_eventuallyEq ?_ <| φ.eqOn_source.eventuallyEq_of_mem <|
    (chartAt H x).open_source.mem_nhds hsrc
  exact (φ.contDiffAt.contMDiffAt.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp _
    (contMDiffAt_extChartAt' hsrc)

/-- Decompose a compactly supported `C¹` vector field `X` into a finite sum of compactly
supported `C¹` vector fields `Y i`, each supported in `U (c i)`, for any family of neighbourhoods
`U x ∈ 𝓝 x` covering `tsupport X`. -/
theorem exists_subordinate_vectorField_sum [IsManifold I 2 M] [T2Space M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hc : HasCompactSupport (β := E) X) {U : M → Set M}
    (hU : ∀ x ∈ tsupport (α := E) X, U x ∈ 𝓝 x) :
    ∃ (ι : Type u) (_ : Fintype ι) (c : ι → M) (Y : ι → (x : M) → TangentSpace I x),
      (∀ i, ContMDiff I I.tangent 1 (T% (Y i))) ∧
      (∀ i, HasCompactSupport (β := E) (Y i)) ∧
      (∀ i, tsupport (α := E) (Y i) ⊆ U (c i)) ∧
      (∀ x, X x = ∑ i, Y i x) ∧
      (∀ x, divergence I X x = ∑ i, divergence I (Y i) x) := by
  classical
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  obtain ⟨ι, _, bc, hbc⟩ := hc.exists_smoothBumpCovering_isSubordinate I hU
  let bc' : BumpCovering ι M (tsupport (α := E) X) :=
    { toFun i := ⟨bc i, (contMDiff_smoothBumpFunction (bc i)).continuous⟩
      locallyFinite' := bc.locallyFinite
      nonneg' i _ := (bc i).nonneg
      le_one' i _ := (bc i).le_one
      eventuallyEq_one' := bc.eventuallyEq_one' }
  let ρ := bc'.toPartitionOfUnity
  have hρ_diff (i : ι) : ContMDiff I 𝓘(ℝ) 1 (ρ i) := by
    have hfun : (ρ i : M → ℝ) = fun x ↦
        bc i x * ∏ j ∈ Finset.univ with WellOrderingRel j i, (1 - bc j x) :=
      funext fun x ↦ bc'.toPartitionOfUnity_eq_mul_prod i x Finset.univ
        fun _ _ _ ↦ Finset.mem_univ _
    rw [hfun]
    exact (contMDiff_smoothBumpFunction (bc i)).mul <|
      contMDiff_finsetProd fun j _ ↦ contMDiff_const.sub (contMDiff_smoothBumpFunction (bc j))
  let Y : ι → (x : M) → TangentSpace I x := fun i x ↦ ρ i x • X x
  have hY (i : ι) : ContMDiff I I.tangent 1 (T% (Y i)) := (hρ_diff i).smul_section hX
  have hsum (x : M) : X x = ∑ i, Y i x := by
    by_cases hx : x ∈ tsupport (α := E) X
    · have h1 : ∑ i, ρ i x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact ρ.sum_eq_one hx
      rw [← Finset.sum_smul, h1, one_smul]
    · have hx0 : X x = 0 := image_eq_zero_of_notMem_tsupport (α := E) hx
      simp [Y, hx0]
  refine ⟨ι, inferInstance, bc.c, Y, hY,
    fun i ↦ hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _),
    fun i ↦ (tsupport_smul_subset_left _ _).trans <|
      (closure_mono (bc'.support_toPartitionOfUnity_subset i)).trans (hbc i),
    hsum, fun x ↦ ?_⟩
  rw [← divergence_finsetSum I Finset.univ Y x fun i _ ↦ (hY i x).mdifferentiableAt one_ne_zero]
  exact congrArg (divergence I · x) (funext hsum)

variable [IsManifold I 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The divergence of a compactly supported `C¹` vector field is integrable against the Riemannian
volume. -/
theorem integrable_divergence {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent 1 (T% X)) (hc : HasCompactSupport (β := E) X) :
    Integrable (divergence I X) (riemannianVolume I M) :=
  (contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num) (by norm_num)
    (by simpa using hX)).continuous.integrable_of_hasCompactSupport (hc.divergence I)

/-- Integration-by-parts decomposition for the divergence of `f • X`, assuming `f • X` has
compact support and `f * div X` is integrable. -/
theorem integral_mul_divergence_eq_integral_divergence_smul_sub {f : M → ℝ}
    {X : (x : M) → TangentSpace I x} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (hfXc : HasCompactSupport (β := E) (fun x ↦ f x • X x))
    (hint : Integrable (fun x ↦ f x * divergence I X x) (riemannianVolume I M)) :
    ∫ x, f x * divergence I X x ∂riemannianVolume I M =
      (∫ x, divergence I (fun x ↦ f x • X x) x ∂riemannianVolume I M) -
        ∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M := by
  have hfX : ContMDiff I I.tangent 1 (T% (fun x ↦ f x • X x)) := hf.smul_section hX
  have hpt (x : M) : divergence I (fun x ↦ f x • X x) x =
      f x * divergence I X x + mvfderiv I f x (X x) :=
    divergence_smul_function I f X x ((hf x).mdifferentiableAt one_ne_zero)
      ((hX x).mdifferentiableAt one_ne_zero)
  have hint' : Integrable (fun x ↦ mvfderiv I f x (X x)) (riemannianVolume I M) :=
    ((integrable_divergence hfX hfXc).sub hint).congr
      (Filter.Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply, hpt]; ring)
  have hdiv : ∫ x, divergence I (fun x ↦ f x • X x) x ∂riemannianVolume I M =
      (∫ x, f x * divergence I X x ∂riemannianVolume I M) +
        ∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hint hint']
  linarith

/-- Integration-by-parts decomposition for `f * div X` when `f` has compact support. -/
theorem integral_mul_divergence_eq_integral_divergence_smul_sub_of_hasCompactSupport_left
    {f : M → ℝ} {X : (x : M) → TangentSpace I x} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hfc : HasCompactSupport f) (hX : ContMDiff I I.tangent 1 (T% X)) :
    ∫ x, f x * divergence I X x ∂riemannianVolume I M =
      (∫ x, divergence I (fun x ↦ f x • X x) x ∂riemannianVolume I M) -
        ∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M :=
  integral_mul_divergence_eq_integral_divergence_smul_sub hf hX
    (hfc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _))
    ((hf.continuous.mul (contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num)
      (by norm_num) (by simpa using hX)).continuous).integrable_of_hasCompactSupport hfc.mul_right)

/-- Integration-by-parts decomposition for `f * div X` when `X` has compact support. -/
theorem integral_mul_divergence_eq_integral_divergence_smul_sub_of_hasCompactSupport_right
    {f : M → ℝ} {X : (x : M) → TangentSpace I x} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hX : ContMDiff I I.tangent 1 (T% X)) (hXc : HasCompactSupport (β := E) X) :
    ∫ x, f x * divergence I X x ∂riemannianVolume I M =
      (∫ x, divergence I (fun x ↦ f x • X x) x ∂riemannianVolume I M) -
        ∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M :=
  integral_mul_divergence_eq_integral_divergence_smul_sub hf hX
    (hXc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _))
    ((hf.continuous.mul (contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num)
      (by norm_num) (by simpa using hX)).continuous).integrable_of_hasCompactSupport
      (hXc.divergence I).mul_left)

end Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Chart

variable [IsManifold I 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {α : M} {X : (x : M) → TangentSpace I x}

private abbrev finChartFlux (α : M) (X : (x : M) → TangentSpace I x)
    (k : Fin (Module.finrank ℝ E)) : E → ℝ :=
  TauCeti.chartFlux (Module.finBasis ℝ E) (chartVolumeDensity (I := I) α) α X k

/-- On the chart target, the coordinate divergence of the fluxes is `ρ div X` read in the chart.
This is the coordinate formula `ρ div X = ∑ₖ ∂ₖ (ρ Xᵏ)` written in coordinates. -/
private theorem sum_fderiv_finChartFlux (hX : ContMDiff I I.tangent 1 (T% X)) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    ∑ k, fderiv ℝ (finChartFlux α X k) z (Module.finBasis ℝ E k) =
      chartVolumeDensity (I := I) α ((extChartAt I α).symm z) *
        divergence I X ((extChartAt I α).symm z) := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have hy : (extChartAt I α).symm z ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I α).map_target hz
  rw [chartVolumeDensity_mul_divergence α (by simpa using hy)
    ((hX _).mdifferentiableAt one_ne_zero)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [chartLocalFrame_def, mvfderiv_localFrame_trivializationAt_eq_fderivWithin
      (Module.finBasis ℝ E) α hy _ k, I.range_eq_univ, fderivWithin_univ,
    (extChartAt I α).right_inv hz]
  have h : finChartFlux α X k =ᶠ[𝓝 z] _ :=
    Filter.eventually_of_mem ((isOpen_extChartAt_target α).mem_nhds hz) fun z' hz' ↦
      chartFlux_apply_of_mem _ _ k hz'
  rw [h.fderiv_eq, Function.comp_def]

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- The divergence theorem for a compactly supported field whose support lies in one chart. -/
private theorem integral_divergence_eq_zero_of_tsupport_subset
    (hX : ContMDiff I I.tangent 1 (T% X)) (hK : IsCompact (tsupport (α := E) X))
    (hKs : tsupport (α := E) X ⊆ (chartAt H α).source) :
    ∫ x, divergence I X x ∂riemannianVolume I M = 0 := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have hKs' : tsupport (α := E) X ⊆ (extChartAt I α).source := by rwa [extChartAt_source]
  have hKc := hK.image_of_continuousOn ((continuousOn_extChartAt α).mono hKs')
  have himage := ((extChartAt I α).mapsTo.mono_left hKs').image_subset
  have hρ : ContMDiffOn I 𝓘(ℝ) 1 (chartVolumeDensity (I := I) α) (chartAt H α).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using
      contMDiffOn_chartVolumeDensity (I := I) (n := 1) α
  have hflux (k : Fin (Module.finrank ℝ E)) : ContDiff ℝ 1 (finChartFlux α X k) :=
    contDiffOn_univ.1 <| I.range_eq_univ ▸
      contDiffOn_chartFlux (Module.finBasis ℝ E) hρ hX.contMDiffOn hKc himage k
  have hfluxc := hasCompactSupport_chartFlux (Module.finBasis ℝ E)
    (chartVolumeDensity (I := I) α) hKc
  have hint (k : Fin (Module.finrank ℝ E)) :
      Integrable (fun z ↦ fderiv ℝ (finChartFlux α X k) z (Module.finBasis ℝ E k))
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
      (sum_fderiv_finChartFlux hX hz).symm,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ Finset.sum_eq_zero fun k _ ↦ by
      rw [(chartFlux_eventuallyEq_zero _ _ hKc k fun h ↦ hz (himage h)).fderiv_eq]
      simp,
    integral_finsetSum _ fun k _ ↦ hint k]
  -- Each partial derivative of a compactly supported `C¹` function integrates to zero.
  exact Finset.sum_eq_zero fun k _ ↦ integral_apply_eq_zero_of_hasFDerivAt_off_countable
    countable_empty (hflux k).continuous (hfluxc k)
    (fun z _ ↦ ((hflux k).differentiable one_ne_zero z).hasFDerivAt) _

end Chart

variable [IsManifold I 2 M] [T2Space M] [LindelofSpace M]
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
  obtain ⟨ι, _, c, Y, hY, hK, hsub, _, hdiv⟩ :=
    exists_subordinate_vectorField_sum hX hc fun x _ ↦ chart_source_mem_nhds H x
  rw [integral_congr_ae (Filter.Eventually.of_forall hdiv),
    integral_finsetSum _ fun i _ ↦ integrable_divergence (hY i) (hK i)]
  exact Finset.sum_eq_zero fun i _ ↦
    integral_divergence_eq_zero_of_tsupport_subset (hY i) (hK i) (hsub i)

/-- **Integration by parts for the divergence**: for a compactly supported `C¹` function `f` and a
`C¹` vector field `X` on a manifold without boundary, `∫ f div X dV = -∫ df(X) dV`. -/
theorem integral_mul_divergence {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hfc : HasCompactSupport f) (hX : ContMDiff I I.tangent 1 (T% X)) :
    ∫ x, f x * divergence I X x ∂riemannianVolume I M =
      -∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M := by
  rw [integral_mul_divergence_eq_integral_divergence_smul_sub_of_hasCompactSupport_left hf hfc hX,
    integral_divergence_eq_zero (X := fun x ↦ f x • X x) (hf.smul_section hX)
      (hfc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _)),
    zero_sub]

/-- **Integration by parts for the divergence**, for a compactly supported field: for a `C¹`
function `f` and a compactly supported `C¹` vector field `X` on a manifold without boundary,
`∫ f div X dV = -∫ df(X) dV`. -/
theorem integral_mul_divergence_of_hasCompactSupport_right {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) 1 f) (hX : ContMDiff I I.tangent 1 (T% X))
    (hXc : HasCompactSupport (β := E) X) :
    ∫ x, f x * divergence I X x ∂riemannianVolume I M =
      -∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M := by
  rw [integral_mul_divergence_eq_integral_divergence_smul_sub_of_hasCompactSupport_right hf hX hXc,
    integral_divergence_eq_zero (X := fun x ↦ f x • X x) (hf.smul_section hX)
      (hXc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _)),
    zero_sub]

/-- **Integration by parts along a vector field**: for `C¹` functions `f` and `g`, one of which
has compact support, and a `C¹` vector field `X` on a manifold without boundary,
`∫ df(X) g dV = -∫ f (dg(X) + (div X) g) dV`. Thus the formal transpose of differentiation along
`X` is `g ↦ -dg(X) - (div X) g`. -/
theorem integral_mvfderiv_mul {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hg : ContMDiff I 𝓘(ℝ) 1 g) (hX : ContMDiff I I.tangent 1 (T% X))
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) :
    ∫ x, mvfderiv I f x (X x) * g x ∂riemannianVolume I M =
      -∫ x, f x * (mvfderiv I g x (X x) + divergence I X x * g x) ∂riemannianVolume I M := by
  have hgX : ContMDiff I I.tangent 1 (T% (fun x ↦ g x • X x)) := hg.smul_section hX
  have h : ∫ x, f x * divergence I (fun x ↦ g x • X x) x ∂riemannianVolume I M =
      -∫ x, mvfderiv I f x (g x • X x) ∂riemannianVolume I M := by
    rcases hfg with hfc | hgc
    · exact integral_mul_divergence hf hfc hgX
    · exact integral_mul_divergence_of_hasCompactSupport_right hf hgX
        (hgc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _))
  have hpt (x : M) : f x * divergence I (fun x ↦ g x • X x) x =
      f x * (mvfderiv I g x (X x) + divergence I X x * g x) := by
    have hdiv : divergence I (fun x ↦ g x • X x) x =
        g x * divergence I X x + mvfderiv I g x (X x) :=
      divergence_smul_function I g X x ((hg x).mdifferentiableAt one_ne_zero)
        ((hX x).mdifferentiableAt one_ne_zero)
    rw [hdiv]
    ring
  simp_rw [hpt, map_smul, smul_eq_mul] at h
  rw [h, neg_neg]
  simp_rw [mul_comm (g _)]

/-- The Laplace--Beltrami operator of a compactly supported `C²` function on a manifold
without boundary has integral zero against the Riemannian volume. -/
theorem integral_laplaceBeltrami_eq_zero {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hfc : HasCompactSupport f) :
    ∫ x, laplaceBeltrami I f x ∂riemannianVolume I M = 0 := by
  have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  simp only [laplaceBeltrami_def]
  exact integral_divergence_eq_zero
    (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])) (hfc.mgradient I)

/-- **Green's first identity** on a manifold without boundary: for a compactly supported `C¹`
function `f` and a `C²` function `g`, `∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV`. -/
theorem integral_mul_laplaceBeltrami {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hfc : HasCompactSupport f) (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    ∫ x, f x * laplaceBeltrami I g x ∂riemannianVolume I M =
      -∫ x, inner ℝ (mgradient I f x) (mgradient I g x) ∂riemannianVolume I M := by
  have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  simp only [laplaceBeltrami_def, inner_mgradient]
  exact integral_mul_divergence hf hfc (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two]))

/-- The energy identity for a compactly supported `C²` eigenfunction of the scalar Laplacian
on a manifold without boundary, using the convention `Δf = -λ f`. -/
theorem integral_norm_sq_mgradient_eq_mul_integral_sq_of_laplaceBeltrami_eq_neg_mul
    {f : M → ℝ} {lam : ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f) (hfc : HasCompactSupport f)
    (heig : ∀ x, laplaceBeltrami I f x = -lam * f x) :
    ∫ x, ‖mgradient I f x‖ ^ 2 ∂riemannianVolume I M =
      lam * ∫ x, f x ^ 2 ∂riemannianVolume I M := by
  have h := integral_mul_laplaceBeltrami (hf.of_le (by norm_num)) hfc hf
  simp only [heig, real_inner_self_eq_norm_sq] at h
  have hfun : (fun x ↦ f x * (-lam * f x)) = fun x ↦ -lam * f x ^ 2 := by
    ext x
    ring
  rw [hfun, integral_const_mul] at h
  linarith

/-- **Green's second identity** on a manifold without boundary: for a compactly supported `C²`
function `f` and a `C²` function `g`, `∫ f Δg dV = ∫ (Δf) g dV`. -/
theorem integral_mul_laplaceBeltrami_right_eq_left {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hfc : HasCompactSupport f) (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    ∫ x, f x * laplaceBeltrami I g x ∂riemannianVolume I M =
      ∫ x, laplaceBeltrami I f x * g x ∂riemannianVolume I M := by
  have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  simp_rw [mul_comm (laplaceBeltrami I f _), laplaceBeltrami_def]
  rw [integral_mul_divergence (hf.of_le (by norm_num)) hfc
      (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])),
    integral_mul_divergence_of_hasCompactSupport_right (hg.of_le (by norm_num))
      (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])) (hfc.mgradient I)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  exact (inner_mgradient_right _).symm.trans (inner_mgradient _)

/-- **Orthogonality of Laplace–Beltrami eigenfunctions with distinct eigenvalues**: on a manifold
without boundary, if `f` and `g` are `C²` functions with `f` compactly supported satisfying
`Δf = -λ₁ f` and `Δg = -λ₂ g` for `λ₁ ≠ λ₂`, then `∫ f g dV = 0`. -/
theorem integral_mul_eq_zero_of_laplaceBeltrami_eq_neg_mul {f g : M → ℝ} {lam₁ lam₂ : ℝ}
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hfc : HasCompactSupport f) (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hlam₁ : ∀ x, laplaceBeltrami I f x = -lam₁ * f x)
    (hlam₂ : ∀ x, laplaceBeltrami I g x = -lam₂ * g x) (hne : lam₁ ≠ lam₂) :
    ∫ x, f x * g x ∂riemannianVolume I M = 0 := by
  have hgreen := integral_mul_laplaceBeltrami_right_eq_left hf hfc hg
  have hL : (fun x ↦ f x * laplaceBeltrami I g x) = fun x ↦ -lam₂ * (f x * g x) := by
    ext x; rw [hlam₂]; ring
  have hR : (fun x ↦ laplaceBeltrami I f x * g x) = fun x ↦ -lam₁ * (f x * g x) := by
    ext x; rw [hlam₁]; ring
  rw [hL, hR, integral_const_mul, integral_const_mul] at hgreen
  have hmul : (lam₁ - lam₂) * ∫ x, f x * g x ∂riemannianVolume I M = 0 := by linarith
  exact (mul_eq_zero.1 hmul).resolve_left (sub_ne_zero.2 hne)

end TauCeti.Manifold
