/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Volume

/-!
# The relative volume of a compactly supported variation of a metric

On a manifold `M` that need not be compact, let `g_t` be a family of metrics that agrees with a
fixed metric `g₀` outside one compact set `K`, for all `t` near `t₀`. The relative density
`J(g₀, g_t)` is then `1` off `K`, so the relative volume `V(t) = ∫ (J(g₀, g_t) - 1) dV_{g₀}` is
finite without `M` having finite volume, and it is `C^k` in `t` at `t₀` when the inner products of
`g_t` are `C^k` jointly in `(t, x)` at the points `(t₀, x)` with `x ∈ K`
(`Bundle.ContMDiffRiemannianMetric.contDiffAt_relativeVolume_of_isCompact`). This is the
noncompact case of the relative-volume functional, whose compact case is
`Bundle.ContMDiffRiemannianMetric.contDiffAt_relativeVolume`.
-/

public section

open Bundle MeasureTheory Set Function TauCeti Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n n' : ℕ∞ω} [LindelofSpace M]
  {g₀ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {g : ℝ → ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x)} {t₀ : ℝ}

/-- **Regularity of the relative volume of a compactly supported variation.** Let `K` be a compact
subset of a manifold `M`, not necessarily compact, and `g_t` a family of metrics with
`g_t = g₀` outside `K` for all `t` near `t₀`. If the inner products of `g₀` are `C^k` at the points
of `K`, and those of `g_t` are `C^k` jointly in `(t, x)` at the points `(t₀, x)` with `x ∈ K`, then
the relative volume `t ↦ ∫ (J(g₀, g_t) - 1) dV_{g₀}` is `C^k` at `t₀`. -/
theorem contDiffAt_relativeVolume_of_isCompact [T2Space M] {k : ℕ∞} [IsManifold I (k + 1) M]
    {K : Set M} (hK : IsCompact K)
    (hg₀ : ∀ x ∈ K, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) k
      (fun x : M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (g₀.inner x)) x)
    (hg : ∀ x ∈ K, ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) k
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x))
    (hgK : ∀ᶠ t in 𝓝 t₀, ∀ x ∉ K, (g t).inner x = g₀.inner x) :
    ContDiffAt ℝ k (fun t ↦ relativeVolume g₀ (g t)) t₀ := by
  have : IsManifold I k M := IsManifold.of_le (n := (k : ℕ∞ω) + 1) le_self_add
  simp only [relativeVolume_def]
  have hK' : IsCompact (WithMetric.ofWithMetric ⁻¹' K : Set (WithMetric g₀)) :=
    WithMetric.coe_homeomorph g₀ ▸ (WithMetric.homeomorph g₀).isCompact_preimage.mpr hK
  refine (hK'.contMDiffAt_parametric_integral (I := 𝓘(ℝ)) (J := I)
    hK'.measure_lt_top.ne (fun a ha ↦ ?_) ?_).contDiffAt
  · exact ((contMDiffAt_uncurry_relativeVolumeDensity (hg₀ _ ha) (hg _ ha)).comp (t₀, a)
      (contMDiffAt_fst.prodMk
        ((WithMetric.contMDiff_ofWithMetric (g := g₀)).contMDiffAt.comp _ contMDiffAt_snd))).sub
      contMDiffAt_const
  · filter_upwards [hgK] with t ht a ha
    rw [relativeVolumeDensity_congr g₀ (g t) (g₁ := g₀) (g₂ := g₀) rfl (ht _ ha),
      relativeVolumeDensity_self, sub_self]

end Bundle.ContMDiffRiemannianMetric
