/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import TauCeti.Analysis.Calculus.DSlope.Basic

/-!
# Joint continuity of `dslope`

For `f : 𝕜 → E` continuously differentiable on an open set `U` (over `𝕜 = ℝ` or `ℂ`), the divided
slope `(c, w) ↦ dslope f c w` is jointly continuous on `U ×ˢ U`: off the diagonal it is the
difference quotient, and at a diagonal point strict differentiability of `f` makes the nearby
difference quotients converge to the derivative. For holomorphic `f` this yields, via Cauchy's
estimate, a bound on `‖deriv (dslope f c) w‖` uniform for `c` in a compact set and `w` near a point.
These are the analytic inputs Dixon's proof of the homology Cauchy theorem needs about the map
`(c, w) ↦ dslope f c w`.

## Main results

* `TauCeti.continuousOn_dslope_prod` — joint continuity of `(c, w) ↦ dslope f c w` on `U ×ˢ U`.
* `TauCeti.continuousOn_dslope_first_arg` — continuity of `c ↦ dslope f c w₀` on a neighbourhood
  `U` of `w₀`, for `f` continuous on `U` and differentiable at `w₀` (over any nontrivially normed
  field).
* `TauCeti.deriv_dslope_bounded_on_compact` — for holomorphic `f`, a uniform bound on
  `‖deriv (dslope f c) w‖` for `c` in a compact subset of `U` and `w` near a point of `U`.

## Provenance

Adapted from `DslopeIntegral.lean` in the AINTLIB `LeanModularForms` development.
-/

public section

namespace TauCeti

open Set Filter Topology Metric

section NontriviallyNormedField

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E}

/-- **Continuity of `c ↦ dslope f c w₀` on `U`** for `f` continuous on a neighbourhood `U` of `w₀`
and differentiable at `w₀`. -/
theorem continuousOn_dslope_first_arg {U : Set 𝕜} {w₀ : 𝕜} (hU : U ∈ 𝓝 w₀)
    (hf : ContinuousOn f U) (hd : DifferentiableAt 𝕜 f w₀) :
    ContinuousOn (fun c ↦ dslope f c w₀) U := by
  simp_rw [dslope_comm f _ w₀]
  exact (continuousOn_dslope hU).mpr ⟨hf, hd⟩

end NontriviallyNormedField

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E}

/-- **Joint continuity of `(c, w) ↦ dslope f c w` on `U ×ˢ U`** for `f` continuously
differentiable on an open set `U`. -/
theorem continuousOn_dslope_prod {U : Set 𝕜} (hU : IsOpen U) (hf : ContDiffOn 𝕜 1 f U) :
    ContinuousOn (fun p : 𝕜 × 𝕜 ↦ dslope f p.1 p.2) (U ×ˢ U) := by
  rintro ⟨c₀, w₀⟩ ⟨hc₀, hw₀⟩
  refine ContinuousAt.continuousWithinAt ?_
  rcases eq_or_ne w₀ c₀ with rfl | hne
  · -- On the diagonal, `dslope f c c = deriv f c` is controlled by continuity of `deriv f`, and
    -- the off-diagonal difference quotients by strict differentiability of `f` at `w₀`.
    have hstrict := (hasDerivAtFilter_iff_isLittleO.mp ((hf.contDiffAt
      (hU.mem_nhds hw₀)).hasStrictDerivAt one_ne_zero)).comp_tendsto
        (continuous_swap.tendsto (w₀, w₀))
    have hderiv : Tendsto (fun p : 𝕜 × 𝕜 ↦ deriv f p.1) (𝓝 (w₀, w₀)) (𝓝 (deriv f w₀)) :=
      ((hf.continuousOn_deriv_of_isOpen hU le_rfl).continuousAt
        (hU.mem_nhds hw₀)).tendsto.comp continuousAt_fst
    rw [ContinuousAt, dslope_same, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hstrict.def (half_pos hε), Metric.tendsto_nhds.mp hderiv ε hε]
      with p hp hp'
    rcases eq_or_ne p.2 p.1 with h | h
    · rwa [h, dslope_same]
    · have hd : p.2 - p.1 ≠ 0 := sub_ne_zero.2 h
      simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap] at hp
      rw [dslope_of_ne f h, dist_eq_norm, ← inv_smul_smul₀ hd (slope f p.1 p.2 - deriv f w₀),
        norm_smul, norm_inv, smul_sub, sub_smul_slope]
      calc ‖p.2 - p.1‖⁻¹ * ‖f p.2 - f p.1 - (p.2 - p.1) • deriv f w₀‖
          ≤ ‖p.2 - p.1‖⁻¹ * (ε / 2 * ‖p.2 - p.1‖) := by gcongr
        _ = ε / 2 := by field_simp [norm_ne_zero_iff.2 hd]
        _ < ε := half_lt_self hε
  · -- Off the diagonal, `dslope` is locally the difference quotient.
    have hcont : ∀ z ∈ U, ContinuousAt f z := fun z hz ↦
      hf.continuousOn.continuousAt (hU.mem_nhds hz)
    have h_eq : (fun p : 𝕜 × 𝕜 ↦ (p.2 - p.1)⁻¹ • (f p.2 - f p.1)) =ᶠ[𝓝 (c₀, w₀)]
        fun p ↦ dslope f p.1 p.2 := by
      filter_upwards [(continuous_snd.sub continuous_fst).continuousAt.eventually_ne
        (sub_ne_zero.2 hne)] with p hp
      rw [dslope_of_ne f (sub_ne_zero.1 hp), slope_def_module]
    exact (((continuousAt_snd.sub continuousAt_fst).inv₀ (sub_ne_zero.2 hne)).smul
      (((hcont w₀ hw₀).comp continuousAt_snd).sub
        ((hcont c₀ hc₀).comp continuousAt_fst))).congr h_eq

end RCLike

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}

/-- **Uniform bound on `deriv (dslope f c) w`.** For `f` complex differentiable on an open set `U`,
with `c` ranging over a compact subset of `U` and `w` over a small ball around a point `w₀ ∈ U`,
the norm `‖deriv (dslope f c) w‖` is bounded by a single constant. -/
theorem deriv_dslope_bounded_on_compact {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) {w₀ : ℂ}
    (hw₀ : w₀ ∈ U) :
    ∃ C > 0, ∃ δ > 0, ∀ c ∈ K, ∀ w ∈ ball w₀ δ, ‖deriv (dslope f c) w‖ ≤ C := by
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hw₀)
  obtain ⟨M, hM⟩ := (hK.prod (isCompact_closedBall w₀ r)).bddAbove_image
    ((continuousOn_dslope_prod hU (hf.contDiffOn hU)).mono (prod_mono hKU hrU)).norm
  refine ⟨max M 1 / (r / 2), by positivity, r / 2, by positivity, fun c hc w hw ↦ ?_⟩
  have hwr : closedBall w (r / 2) ⊆ closedBall w₀ r :=
    closedBall_subset_closedBall' (by linarith [mem_ball.mp hw])
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hr)
    (((Complex.differentiableOn_dslope (hU.mem_nhds (hKU hc))).mpr hf).diffContOnCl_ball
      (hwr.trans hrU)) fun z hz ↦ ?_
  exact (hM ⟨(c, z), ⟨hc, hwr (sphere_subset_closedBall hz)⟩, rfl⟩).trans (le_max_left _ _)

end Complex

end TauCeti
