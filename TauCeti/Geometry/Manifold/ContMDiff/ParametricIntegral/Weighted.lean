/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Basic

/-!
# Weighted parametric integrals

Let `Φ : M → N → E₁` be a `C^n` function of a point `x` and a parameter `a`, let `g : N → E₂` be
merely continuous on a compact set `K` of parameters, and let `L : E₁ →L[ℝ] E₂ →L[ℝ] F` be a
continuous bilinear map. Then

`x ↦ ∫ a in K, L (Φ x a) (g a) ∂μ`

is `C^n`: all derivatives fall on the smooth factor `Φ`. The integrand is not jointly smooth, so
`IsCompact.contMDiffAt_setIntegral_parametric` does not apply directly. Instead the weight is moved
into the measure: with `j a = (a, g a)`, the integral is the integral of the jointly smooth function
`(x, (a, e)) ↦ L (Φ x a) e` against the pushforward of `μ` restricted to `K` along `j`, which is
concentrated on the compact graph `j '' K` of `g` over `K`.

On a Lie group this gives smoothness of `x ↦ ∫ y, L (a (x⁻¹ * y)) (f y) ∂ν` for a compactly
supported `C^n` function `a` and a continuous `f`
(`ContinuousLinearMap.contMDiff_integral_comp_inv_mul`). For a strongly continuous representation
`π`, the vector `π(x) π(a) v` is this integral with `f y = π y v`, which is the analytic input of
Gårding smoothing.

## Main results

* `IsCompact.contMDiffAt_setIntegral_clm`: smoothness of a weighted integral over a compact set.
* `ContinuousLinearMap.contMDiff_integral_comp_inv_mul`: the Lie-group corollary.
-/

public section

open Set Filter MeasureTheory Function
open scoped Topology ContDiff Manifold Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [MeasurableSpace N] [OpensMeasurableSpace N]
  [T2Space N] {μ : Measure N}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {n : ℕ∞} [IsManifold I n M] [IsManifold J n N] {x₀ : M}

/-- **Smoothness of a weighted integral over a compact set of parameters.** Let `K` be a compact
set of parameters with `μ K < ∞`, let `g` be continuous on `K` and let `L` be a continuous bilinear
map. If `(x, a) ↦ Φ x a` is `C^n` at every point `(x₀, a)` with `a ∈ K`, then
`x ↦ ∫ a in K, L (Φ x a) (g a) ∂μ` is `C^n` at `x₀`. No smoothness of `g` is needed. -/
theorem _root_.IsCompact.contMDiffAt_setIntegral_clm (L : E₁ →L[ℝ] E₂ →L[ℝ] F)
    {Φ : M → N → E₁} {g : N → E₂} {K : Set N} (hK : IsCompact K) (hμK : μ K ≠ ⊤)
    (hΦ : ∀ a ∈ K, ContMDiffAt (I.prod J) 𝓘(ℝ, E₁) n (uncurry Φ) (x₀, a))
    (hg : ContinuousOn g K) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ ∫ a in K, L (Φ x a) (g a) ∂μ) x₀ := by
  borelize (N × E₂)
  let j : N → N × E₂ := fun a ↦ (a, g a)
  have hjc : ContinuousOn j K := continuousOn_id.prodMk hg
  have hK' : IsCompact (j '' K) := hK.image_of_continuousOn hjc
  have hj : AEMeasurable j (μ.restrict K) := hjc.aemeasurable hK.measurableSet
  set ν := (μ.restrict K).map j
  have hν : ν (j '' K) ≠ ⊤ := by
    rw [Measure.map_apply_of_aemeasurable hj hK'.measurableSet]
    exact ne_top_of_le_ne_top hμK <| (measure_mono (subset_univ _)).trans_eq
      (Measure.restrict_apply_univ K)
  have hf : ∀ b ∈ j '' K, ContMDiffAt (I.prod (J.prod 𝓘(ℝ, E₂))) 𝓘(ℝ, F) n
      (uncurry fun x (b : N × E₂) ↦ L (Φ x b.1) b.2) (x₀, b) := by
    rintro _ ⟨a, ha, rfl⟩
    have h₁ : ContMDiffAt (I.prod (J.prod 𝓘(ℝ, E₂))) 𝓘(ℝ, E₁) n
        (fun p : M × (N × E₂) ↦ Φ p.1 p.2.1) (x₀, j a) :=
      (hΦ a ha).comp (x₀, j a) (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).contMDiffAt
    exact (L.contMDiff.contMDiffAt.comp _ h₁).clm_apply
      (contMDiff_snd.comp contMDiff_snd).contMDiffAt
  refine (hK'.contMDiffAt_setIntegral_parametric (μ := ν) hν hf).congr_of_eventuallyEq ?_
  -- Near `x₀`, each `Φ x` is continuous on `K`, so the integrand against `ν` is measurable.
  obtain ⟨U, V, hU, -, hx₀U, hKV, hΦU⟩ := exists_isOpen_prod_contMDiffOn (I' := I.prod J)
    (J := 𝓘(ℝ, E₁)) (n := 0) (f := uncurry Φ) hK (by simp) fun a ha ↦ (hΦ a ha).of_le zero_le
  have hνK : ν.restrict (j '' K) = ν :=
    Measure.restrict_eq_self_of_ae_mem <| (ae_map_iff hj hK'.measurableSet).2 <|
      ae_restrict_of_forall_mem hK.measurableSet fun a ha ↦ mem_image_of_mem j ha
  filter_upwards [hU.mem_nhds hx₀U] with x hx
  have hΦx : ContinuousOn (Φ x) K :=
    hΦU.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) fun a ha ↦ ⟨hx, hKV ha⟩
  have hc : ContinuousOn (fun b : N × E₂ ↦ L (Φ x b.1) b.2) (j '' K) := by
    refine L.continuous₂.comp_continuousOn ((hΦx.comp continuousOn_fst ?_).prodMk continuousOn_snd)
    rintro _ ⟨a, ha, rfl⟩
    exact ha
  have hm : AEStronglyMeasurable (fun b : N × E₂ ↦ L (Φ x b.1) b.2) ν := by
    simpa only [hνK] using hc.aestronglyMeasurable_of_isCompact (μ := ν) hK' hK'.measurableSet
  rw [hνK, integral_map hj hm]

/-- **Smoothing by a test function on a Lie group.** If `a` is `C^n` with compact support and `f`
is continuous on a locally compact Lie group `G` carrying a measure `ν` that is finite on compact
sets, then for a continuous bilinear map `L` the function `x ↦ ∫ y, L (a (x⁻¹ * y)) (f y) ∂ν` is
`C^n`. Only `a` is differentiated. -/
theorem _root_.ContinuousLinearMap.contMDiff_integral_comp_inv_mul {G : Type*}
    [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I n G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G] {ν : Measure G}
    [IsFiniteMeasureOnCompacts ν] (L : E₁ →L[ℝ] E₂ →L[ℝ] F) {a : G → E₁} {f : G → E₂}
    (ha : ContMDiff I 𝓘(ℝ, E₁) n a) (ha' : HasCompactSupport a) (hf : Continuous f) :
    ContMDiff I 𝓘(ℝ, F) n (fun x ↦ ∫ y, L (a (x⁻¹ * y)) (f y) ∂ν) := by
  have := continuousMul_of_contMDiffMul I n (G := G)
  intro x₀
  obtain ⟨C, hC, hx₀C⟩ := exists_compact_mem_nhds x₀
  have hK : IsCompact (C * tsupport a) := hC.mul ha'
  have hΦ : ContMDiff (I.prod I) 𝓘(ℝ, E₁) n (uncurry fun x y : G ↦ a (x⁻¹ * y)) :=
    ha.comp (contMDiff_fst.inv.mul contMDiff_snd)
  refine (hK.contMDiffAt_setIntegral_clm (μ := ν) L hK.measure_lt_top.ne (fun y _ ↦ hΦ _)
    hf.continuousOn).congr_of_eventuallyEq ?_
  filter_upwards [hx₀C] with x hx
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_).symm
  have : x⁻¹ * y ∉ tsupport a := fun h ↦ hy ⟨x, hx, x⁻¹ * y, h, mul_inv_cancel_left x y⟩
  simp [image_eq_zero_of_notMem_tsupport this]

end TauCeti
