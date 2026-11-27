/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure.SmoothDensity
public import TauCeti.Geometry.Manifold.Sobolev.Completion
import TauCeti.Geometry.Manifold.Measure.CutoffPullback
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.Sobolev.BesselPotential.Duality

/-!
# Pairing Sobolev functions on a compact manifold with smooth functions

Let `M` be a compact manifold modelled on `ℝⁿ`, read through finitely many cutoffs `ψᵢ` in charts
`eᵢ` whose readings `ψᵢ ∘ eᵢ` on `M` add up to `1`, and let `H^s(M)` be the Sobolev space of real
order `s` of these charts (`TauCeti.chartSobolevSpace`), the closure of the chart readings of the
smooth functions. Let `μ` be a finite measure on `M` with a smooth positive density
(`TauCeti.HasSmoothPositiveDensity`), such as a Riemannian volume.

For a smooth function `v`, the `L²` pairing `u ↦ ∫ ⟪v, u⟫ dμ` on smooth functions is bounded in
the norm of `H^s(M)`, **for every real order `s`**, negative orders included
(`TauCeti.exists_norm_integral_inner_le_norm_chartReading`). So it extends to a continuous linear
functional on `H^s(M)` (`TauCeti.chartSobolevPairing`). Indeed, `u = ∑ᵢ (ψᵢ ∘ eᵢ) u`, and in the
chart `eᵢ`, where `μ = ρᵢ dy`,

`∫ ⟪v, (ψᵢ ∘ eᵢ) u⟫ dμ = ∫ ⟪ρᵢ χᵢ · (v ∘ eᵢ⁻¹), ψᵢ · (u ∘ eᵢ⁻¹)⟫ dy`

for a cutoff `χᵢ` equal to `1` on the support of `ψᵢ`. The right side is the `L²` pairing of a
fixed Schwartz function with the `i`-th chart reading of `u`, bounded by the `H^{-s}(ℝⁿ)` norm of
the first factor times the `H^s(ℝⁿ)` norm of the second
(`SchwartzMap.norm_integral_inner_le_norm_toBesselPotentialSpaceCLM_mul_norm`).

These functionals are the compatibility conditions of the equation `P u = f` on the whole Sobolev
scale. If `Q` is a formal adjoint of an operator `P` on smooth functions,
`∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ`, and `L : H^s(M) → H^t(M)` is a continuous extension of `P`, then
pairing with `v` after `L` is pairing with `Q v`
(`TauCeti.chartSobolevPairing_comp_of_forall_integral_inner_eq`). In particular every `f` in the
range of `L` satisfies `⟨v, f⟩ = 0` for every smooth solution `v` of `Q v = 0`
(`TauCeti.chartSobolevPairing_apply_eq_zero_of_mem_range`), also when `t` is negative and `f` is
not a function.

The pairings with smooth functions determine the elements of `H^s(M)`
(`TauCeti.eq_of_forall_chartSobolevPairing_eq`): an element `x` is determined by the
conjugate-linear functional `v ↦ ⟨v, x⟩` on smooth functions.
For the `i`-th component of `x ∈ H^s(M)` and a Schwartz function `h`, the `L²` pairing of `h` with
that component is the pairing of `x` with the smooth function `(ρᵢ⁻¹ ψᵢ h) ∘ eᵢ`, extended by `0`,
and these `L²` pairings with Schwartz functions separate the points of `H^s(ℝⁿ)`
(`BesselPotentialSpace.eq_zero_of_forall_inner_toLp_eq_zero`).

## Main definitions

* `TauCeti.chartSobolevPairing μ he ψ v s`: the continuous linear functional on `H^s(M)` extending
  `u ↦ ∫ ⟪v, u⟫ dμ`.

## Main results

* `TauCeti.exists_norm_integral_inner_le_norm_chartReading`: `|∫ ⟪v, u⟫ dμ| ≤ C ‖u‖_{H^s(M)}`.
* `TauCeti.chartSobolevPairing_toChartSobolevSpace`: on smooth functions the pairing is
  `∫ ⟪v, u⟫ dμ`.
* `TauCeti.chartSobolevPairing_comp_chartSobolevInclusion`: the pairings of the different orders
  agree along the inclusions `H^s(M) ⊆ H^r(M)`.
* `TauCeti.chartSobolevPairing_comp_of_forall_integral_inner_eq`: transposition of an operator
  with a formal adjoint.
* `TauCeti.chartSobolevPairing_apply_eq_zero_of_mem_range`: the range of an extension of `P` is
  annihilated by the pairings with the kernel of the formal adjoint.
* `TauCeti.eq_of_forall_chartSobolevPairing_eq`: an element of `H^s(M)` is determined by its
  pairings with smooth functions.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds and the pairing of `H^s(M)` with `H^{-s}(M)`).
* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §6, pp. 517–519 (the cokernel of an elliptic operator through its formal adjoint).
-/

public section

noncomputable section

open Set MeasureTheory OpenPartialHomeomorph ComplexConjugate
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace InnerProductSpace

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [MeasurableSpace M] {μ : Measure M}

/-! ### Changing variables in a chart -/

section Chart

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M) {ρ : CoordinateSpace n → ℝ}
  (hint : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
    ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))

include he hint

/-- **A cut-off integral in a chart.** Let `ρ` be the density of `μ` in the chart `e`, and `χ` and
`θ` cutoffs equal to `1` and to `ρ` on the support of the cutoff `ψ`. Pairing a smooth function `v`
with `u` cut off by `ψ ∘ e` is pairing the readings `θ · (v ∘ e⁻¹)` and `ψ · (u ∘ e⁻¹)` on
`ℝⁿ`. -/
private theorem integral_inner_mul_cutoffPullback_eq (ψ χ θ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (hχ : ∀ y ∈ tsupport ψ, χ y = 1) (hθ : ∀ y ∈ tsupport ψ, θ y = ρ y)
    (u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ∫ x, ⟪v x, (e.cutoffPullback he ψ 1 x : ℂ) * u x⟫_ℂ ∂μ =
      ∫ y, ⟪e.cutoffPushforwardSchwartz he θ v y, e.cutoffPushforwardSchwartz he ψ u y⟫_ℂ := by
  -- `u` cut off by `ψ ∘ e` is the pullback by `ψ` of the reading `χ · (u ∘ e⁻¹)` of `u`.
  have hu (x : M) : (e.cutoffPullback he ψ 1 x : ℂ) * u x =
      e.complexCutoffPullback he ψ (e.complexCutoffPushforward he χ u) x := by
    by_cases hx : x ∈ e.source
    · rw [cutoffPullback_one_apply_of_mem he _ hx, complexCutoffPullback_apply_of_mem he _ _ hx,
        complexCutoffPushforward_apply, e.left_inv hx]
      by_cases hψx : ψ (e x) = 0
      · simp [hψx]
      · simp [hχ _ (subset_tsupport _ hψx), Complex.real_smul]
    · simp [cutoffPullback_apply_of_notMem he _ _ hx,
        complexCutoffPullback_apply_of_notMem he _ _ hx]
  simp_rw [hu]
  rw [integral_inner_complexCutoffPullback he hint ψ _ v.contMDiff.continuous]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  simp only [complexCutoffPushforward_apply, cutoffPushforwardSchwartz_apply, RCLike.inner_apply,
    Complex.real_smul, map_mul, Complex.conj_ofReal]
  by_cases hψy : ψ y = 0
  · simp [hψy]
  · rw [hθ y (subset_tsupport _ hψy), hχ y (subset_tsupport _ hψy)]
    push_cast
    ring

/-- **The pullback of a function on the chart.** Let `ρ` be the density of `μ` in the chart `e`,
and `θ` a cutoff with `ρ θ = ψ` on the chart target. Pairing the smooth function `(θ f) ∘ e` on
`M` with `u` is pairing `f` with the reading `ψ · (u ∘ e⁻¹)` of `u` on `ℝⁿ`. -/
private theorem integral_inner_complexCutoffPullback_eq (ψ θ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (hθ : ∀ y ∈ e.target, ρ y * θ y = ψ y) (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n;
      𝓘(ℝ, ℂ), ℂ⟯) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ∫ x, ⟪e.complexCutoffPullback he θ f x, u x⟫_ℂ ∂μ =
      ∫ y, ⟪f y, e.cutoffPushforwardSchwartz he ψ u y⟫_ℂ := by
  rw [integral_inner_complexCutoffPullback_left he hint θ f u.contMDiff.continuous]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  by_cases hy : y ∈ e.target
  · simp only [cutoffPushforwardSchwartz_apply, ← hθ y hy, RCLike.inner_apply,
      Complex.real_smul]
    push_cast
    ring
  · -- Off the chart target both cutoffs vanish.
    have h0 (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) : φ y = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (φ.tsupport_subset h)
    simp [cutoffPushforwardSchwartz_apply, h0 θ, h0 ψ]

end Chart

/-! ### The pairing -/

variable {ι : Type*} [Fintype ι] {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))

section Bound

variable [BorelSpace M] [IsFiniteMeasure μ]

omit [T2Space M] [Fintype ι] in
/-- Smooth functions on a compact manifold are square integrable against a finite measure, so
their pairing is integrable. -/
private theorem integrable_inner [CompactSpace M]
    (u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    Integrable (fun x ↦ ⟪v x, u x⟫_ℂ) μ :=
  (v.contMDiff.continuous.inner u.contMDiff.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **The `L²` pairing is bounded in every Sobolev norm.** On a compact manifold read through
cutoffs `ψᵢ` in charts `eᵢ` whose readings on `M` add up to `1`, let `μ` be a finite measure with a
smooth positive density, and `v` a smooth function. For every real `s`, negative orders included,
`|∫ ⟪v, u⟫ dμ| ≤ C ‖u‖_{H^s(M)}` for all smooth functions `u`, the norm being that of the chart
readings of `u` in `⨁ᵢ H^s(ℝⁿ)`. -/
theorem exists_norm_integral_inner_le_norm_chartReading
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) (s : ℝ)
    (v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ∃ C, ∀ u, ‖∫ x, ⟪v x, u x⟫_ℂ ∂μ‖ ≤ C * ‖chartReading he ψ s u‖ := by
  have := compactSpace_of_forall_sum_cutoffPullback_eq_one he ψ hψ
  -- In the chart `eᵢ`, `μ = ρᵢ dy`; the cutoff `θᵢ = ρᵢ χᵢ` equals `ρᵢ` on the support of `ψᵢ`.
  choose ρ hρ _ hint using fun i ↦ hasSmoothPositiveDensity_iff.1 hμ (e i) (he i)
  choose χ hχ _ using fun i ↦ TestFunction.exists_eventually_eq_one (n := ⊤)
    (ψ i).hasCompactSupport.isCompact (ψ i).tsupport_subset
  have hχ' (i : ι) (y : CoordinateSpace n) (hy : y ∈ tsupport (ψ i)) : χ i y = 1 :=
    ((hχ i).filter_mono (nhds_le_nhdsSet hy)).self_of_nhds
  set θ := fun i ↦ TestFunction.smulLeftCLMOfContDiffOn (hρ i) (χ i)
  have hθ (i : ι) (y : CoordinateSpace n) (hy : y ∈ tsupport (ψ i)) : θ i y = ρ i y := by
    simp [θ, TestFunction.smulLeftCLMOfContDiffOn_apply, hχ' i y hy]
  -- The readings `θᵢ · (v ∘ eᵢ⁻¹)` of `v`, measured in `H^{-s}(ℝⁿ)`.
  set g := fun i ↦ (e i).cutoffPushforwardSchwartz (he i) (θ i) v
  refine ⟨∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM (-s) 2 (g i)‖, fun u ↦ ?_⟩
  -- `u = ∑ᵢ (ψᵢ ∘ eᵢ) u`, and each term is a pairing of chart readings.
  have hu : (fun x ↦ ⟪v x, u x⟫_ℂ) =
      fun x ↦ ∑ i, ⟪v x, ((e i).cutoffPullback (he i) (ψ i) 1 x : ℂ) * u x⟫_ℂ := by
    funext x
    rw [← inner_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, hψ x, Complex.ofReal_one, one_mul]
  have hint' (i : ι) (_ : i ∈ Finset.univ) : Integrable
      (fun x ↦ ⟪v x, ((e i).cutoffPullback (he i) (ψ i) 1 x : ℂ) * u x⟫_ℂ) μ :=
    (v.contMDiff.continuous.inner ((Complex.continuous_ofReal.comp
      ((e i).cutoffPullback (he i) (ψ i) 1).contMDiff.continuous).mul
      u.contMDiff.continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [hu, integral_finsetSum _ hint', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [integral_inner_mul_cutoffPullback_eq (he i) (hint i) (ψ i) (χ i) (θ i) (hχ' i) (hθ i)]
  refine (SchwartzMap.norm_integral_inner_le_norm_toBesselPotentialSpaceCLM_mul_norm s _ _).trans
    (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [← chartReading_apply]
  exact PiLp.norm_apply_le _ i

end Bound

variable [BorelSpace M] [CompactSpace M] [IsFiniteMeasure μ]

variable (μ) in
/-- The `L²` pairing `u ↦ ∫ ⟪v, u⟫ dμ` with a smooth function `v`, on the smooth functions of a
compact manifold. -/
private def integralInner (v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] ℂ where
  toFun u := ∫ x, ⟪v x, u x⟫_ℂ ∂μ
  map_add' u w := by
    simp only [ContMDiffMap.coe_add, Pi.add_apply, inner_add_right]
    exact integral_add (integrable_inner u v) (integrable_inner w v)
  map_smul' c u := by
    simp [mul_assoc, integral_const_mul]

omit [T2Space M] [Fintype ι] in
private theorem integralInner_apply (v u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    integralInner μ v u = ∫ x, ⟪v x, u x⟫_ℂ ∂μ :=
  rfl

variable (μ) in
/-- **The pairing of `H^s(M)` with a smooth function.** The continuous linear functional on the
Sobolev space `H^s(M)` of the charts `eᵢ` and cutoffs `ψᵢ` extending the `L²` pairing
`u ↦ ∫ ⟪v, u⟫ dμ` with the smooth function `v`, by continuity from the dense smooth functions
(`LinearMap.extendOfNorm`). It extends the pairing when the readings `ψᵢ ∘ eᵢ` add up to `1` and `μ`
has a smooth positive density (`TauCeti.chartSobolevPairing_toChartSobolevSpace`), for every real
order `s`. -/
def chartSobolevPairing (v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (s : ℝ) :
    chartSobolevSpace he ψ s →L[ℂ] ℂ :=
  (integralInner μ v).extendOfNorm (toChartSobolevSpace he ψ s)

variable {he ψ}
variable (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
  (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)

include hμ hψ

/-- On a smooth function `u`, the pairing of `H^s(M)` with the smooth function `v` is the `L²`
pairing `∫ ⟪v, u⟫ dμ`. -/
@[simp]
theorem chartSobolevPairing_toChartSobolevSpace (v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
    (s : ℝ) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevPairing μ he ψ v s (toChartSobolevSpace he ψ s u) = ∫ x, ⟪v x, u x⟫_ℂ ∂μ :=
  LinearMap.extendOfNorm_eq (denseRange_toChartSobolevSpace he ψ s)
    (by
      obtain ⟨C, hC⟩ := exists_norm_integral_inner_le_norm_chartReading he ψ hμ hψ s v
      exact ⟨C, fun u ↦ by rw [integralInner_apply, norm_toChartSobolevSpace]; exact hC u⟩) u

/-- **Uniqueness of the pairing.** A continuous linear functional on `H^s(M)` that is the `L²`
pairing `∫ ⟪v, u⟫ dμ` on smooth functions `u` is the pairing with `v`. -/
theorem chartSobolevPairing_eq {v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {s : ℝ}
    (L : chartSobolevSpace he ψ s →L[ℂ] ℂ)
    (hL : ∀ u, L (toChartSobolevSpace he ψ s u) = ∫ x, ⟪v x, u x⟫_ℂ ∂μ) :
    chartSobolevPairing μ he ψ v s = L :=
  chartSobolevSpace_ext he ψ fun u ↦ by
    rw [chartSobolevPairing_toChartSobolevSpace hμ hψ, hL]

/-- The pairing is additive in the smooth function. -/
theorem chartSobolevPairing_add (v w : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (s : ℝ) :
    chartSobolevPairing μ he ψ (v + w) s =
      chartSobolevPairing μ he ψ v s + chartSobolevPairing μ he ψ w s :=
  chartSobolevPairing_eq hμ hψ _ fun u ↦ by
    simp only [FunLike.coe_add, Pi.add_apply, chartSobolevPairing_toChartSobolevSpace hμ hψ,
      ContMDiffMap.coe_add, inner_add_left]
    exact (integral_add (integrable_inner (μ := μ) u v) (integrable_inner (μ := μ) u w)).symm

/-- The pairing is conjugate-linear in the smooth function. -/
theorem chartSobolevPairing_smul (c : ℂ) (v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
    (s : ℝ) : chartSobolevPairing μ he ψ (c • v) s = conj c • chartSobolevPairing μ he ψ v s :=
  chartSobolevPairing_eq hμ hψ _ fun u ↦ by
    simp only [FunLike.coe_smul, Pi.smul_apply, chartSobolevPairing_toChartSobolevSpace hμ hψ,
      ContMDiffMap.complex_smul_apply, smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    simp only [RCLike.inner_apply, map_mul]
    ring

/-- The pairing with the zero function vanishes. -/
@[simp]
theorem chartSobolevPairing_zero (s : ℝ) : chartSobolevPairing μ he ψ 0 s = 0 :=
  chartSobolevPairing_eq hμ hψ _ fun u ↦ by simp

/-- **The pairings of different orders agree.** For `r ≤ s`, pairing an element of `H^s(M)` with a
smooth function is pairing its image under the inclusion `H^s(M) ⊆ H^r(M)`. -/
theorem chartSobolevPairing_comp_chartSobolevInclusion
    (v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) {r s : ℝ} (h : r ≤ s) :
    (chartSobolevPairing μ he ψ v r).comp (chartSobolevInclusion he ψ h) =
      chartSobolevPairing μ he ψ v s :=
  (chartSobolevPairing_eq hμ hψ _ fun u ↦ by
    rw [ContinuousLinearMap.comp_apply, chartSobolevInclusion_toChartSobolevSpace,
      chartSobolevPairing_toChartSobolevSpace hμ hψ]).symm

/-- The `L²` pairing of a Schwartz function `b` with the `i`-th component of an element `x` of
`H^s(M)` is the pairing of `x` with the smooth function `(ρᵢ⁻¹ ψᵢ b) ∘ eᵢ` on `M`, where `ρᵢ` is
the density of `μ` in the chart `eᵢ`. -/
private theorem exists_chartSobolevPairing_eq_inner (s : ℝ) (i : ι) (b : 𝓢(CoordinateSpace n, ℂ)) :
    ∃ w, ∀ x : chartSobolevSpace he ψ s, chartSobolevPairing μ he ψ w s x =
      ⟪(SchwartzMap.toBesselPotentialSpaceCLM (-s) 2 b).toLp,
        ((x : PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n)) i).toLp⟫_ℂ := by
  obtain ⟨ρ, hρ, hρpos, hint⟩ := hasSmoothPositiveDensity_iff.1 hμ (e i) (he i)
  set θ := TestFunction.smulLeftCLMOfContDiffOn (hρ.inv fun y hy ↦ (hρpos y hy).ne') (ψ i)
  have hθ (y : CoordinateSpace n) (hy : y ∈ (e i).target) : ρ y * θ y = ψ i y := by
    simp [θ, TestFunction.smulLeftCLMOfContDiffOn_apply, ← mul_assoc,
      mul_inv_cancel₀ (hρpos y hy).ne']
  -- The right side is continuous in `x`; on smooth functions both sides are `∫ ⟪b, ψᵢ (u ∘ eᵢ⁻¹)⟫`.
  let L : chartSobolevSpace he ψ s →L[ℂ] ℂ :=
    innerSL ℂ (SchwartzMap.toBesselPotentialSpaceCLM (-s) 2 b).toLp ∘L
      (BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) ℂ s 2).toLinearIsometry.toContinuousLinearMap
      ∘L PiLp.proj 2 _ i ∘L (chartSobolevSpace he ψ s).subtypeL
  have hL : chartSobolevPairing μ he ψ ((e i).complexCutoffPullback (he i) θ
      (ContMDiffMap.ofContDiff b (b.smooth ⊤))) s = L :=
    chartSobolevPairing_eq hμ hψ L fun u ↦ by
      simp only [L, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        coe_toChartSobolevSpace, PiLp.proj_apply, chartReading_apply,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
        BesselPotentialSpace.toLpₗᵢ_apply, innerSL_apply_apply]
      rw [integral_inner_complexCutoffPullback_eq (he i) hint (ψ i) θ hθ,
        ContMDiffMap.coe_ofContDiff]
      exact SchwartzMap.inner_toLp_toBesselPotentialSpaceCLM_neg s b _
  refine ⟨(e i).complexCutoffPullback (he i) θ (ContMDiffMap.ofContDiff b (b.smooth ⊤)),
    fun x ↦ ?_⟩
  rw [hL]
  simp [L]

/-- **The pairings determine the elements of `H^s(M)`.** On a compact manifold read through cutoffs
`ψᵢ` in charts `eᵢ` whose readings add up to `1`, with a finite measure `μ` having a smooth positive
density, two elements of `H^s(M)` with the same pairings with every smooth function are equal, for
every real order `s`. So an element `x` of `H^s(M)` is determined by the conjugate-linear
functional `v ↦ ⟨v, x⟩` on smooth functions. -/
theorem eq_of_forall_chartSobolevPairing_eq {s : ℝ} {x y : chartSobolevSpace he ψ s}
    (h : ∀ v, chartSobolevPairing μ he ψ v s x = chartSobolevPairing μ he ψ v s y) : x = y := by
  rw [← sub_eq_zero]
  refine Subtype.ext (PiLp.ext fun i ↦ ?_)
  -- Each component of `x - y` is orthogonal to all Schwartz functions, read in `H^{-s}(ℝⁿ)`.
  refine BesselPotentialSpace.eq_zero_of_forall_inner_toLp_eq_zero _ fun b ↦ ?_
  obtain ⟨w, hw⟩ := exists_chartSobolevPairing_eq_inner hμ hψ s i b
  rw [← hw, map_sub, h, sub_self]

/-! ### Transposition -/

variable {κ : Type*} [Fintype κ] {e' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
  {he' : ∀ j, e' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {φ : ∀ j, 𝓓(⟨(e' j).target, (e' j).open_target⟩, ℝ)}
  {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
  {s t : ℝ} {L : chartSobolevSpace he ψ s →L[ℂ] chartSobolevSpace he' φ t}

/-- **Transposition.** Let `Q` be a formal adjoint of an operator `P` on the smooth functions,
`∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ`, and `L : H^s(M) → H^t(M)` a continuous extension of `P`, possibly
between the Sobolev spaces of two different chart partitions. Then pairing `L x` with a smooth
function `v` is pairing `x` with `Q v`, for all real orders `s` and `t`. -/
theorem chartSobolevPairing_comp_of_forall_integral_inner_eq
    (hφ : ∀ x, ∑ j, (e' j).cutoffPullback (he' j) (φ j) 1 x = 1)
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, ⟪P u x, v x⟫_ℂ ∂μ = ∫ x, ⟪u x, Q v x⟫_ℂ ∂μ)
    (hL : ∀ u, L (toChartSobolevSpace he ψ s u) = toChartSobolevSpace he' φ t (P u))
    (v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (chartSobolevPairing μ he' φ v t).comp L = chartSobolevPairing μ he ψ (Q v) s :=
  (chartSobolevPairing_eq hμ hψ _ fun u ↦ by
    -- Conjugating the adjoint identity swaps the two factors of each inner product.
    have hconj (f g : M → ℂ) : ∫ x, ⟪f x, g x⟫_ℂ ∂μ = conj (∫ x, ⟪g x, f x⟫_ℂ ∂μ) := by
      simp only [← integral_conj, inner_conj_symm]
    rw [ContinuousLinearMap.comp_apply, hL, chartSobolevPairing_toChartSobolevSpace hμ hφ,
      hconj, hPQ, ← hconj]).symm

/-- **Compatibility conditions.** Let `Q` be a formal adjoint of an operator `P` on the smooth
functions and `L : H^s(M) → H^t(M)` a continuous extension of `P`. Every `f` in the range of `L`
satisfies `⟨v, f⟩ = 0` for each smooth solution `v` of `Q v = 0`, for all real orders `s` and `t`.
-/
theorem chartSobolevPairing_apply_eq_zero_of_mem_range
    (hφ : ∀ x, ∑ j, (e' j).cutoffPullback (he' j) (φ j) 1 x = 1)
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, ⟪P u x, v x⟫_ℂ ∂μ = ∫ x, ⟪u x, Q v x⟫_ℂ ∂μ)
    (hL : ∀ u, L (toChartSobolevSpace he ψ s u) = toChartSobolevSpace he' φ t (P u))
    {f : chartSobolevSpace he' φ t} (hf : f ∈ Set.range L)
    {v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hv : Q v = 0) :
    chartSobolevPairing μ he' φ v t f = 0 := by
  obtain ⟨x, rfl⟩ := hf
  rw [← ContinuousLinearMap.comp_apply,
    chartSobolevPairing_comp_of_forall_integral_inner_eq hμ hψ hφ hPQ hL, hv]
  simp [chartSobolevPairing_zero hμ hψ]

end TauCeti
