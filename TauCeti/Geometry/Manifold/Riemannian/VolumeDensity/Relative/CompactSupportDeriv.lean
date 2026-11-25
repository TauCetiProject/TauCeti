/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Deriv
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.CompactSupport

/-!
# The first two variations of the relative volume of a compactly supported variation

On a manifold `M` that need not be compact, let `g_t` be a family of metrics that agrees with a
fixed metric `g₀` outside one compact set `K`, for all `t` near `t₀`. The relative volume
`V(t) = ∫ (J(g₀, g_t) - 1) dV_{g₀}` is then finite
(`Bundle.ContMDiffRiemannianMetric.contDiffAt_relativeVolume_of_isCompact`), and its first two
derivatives at `t₀` are computed by differentiation under the integral sign:

`V'(t₀) = ∫ ∂_t J(g₀, g_t) dV_{g₀}` and `V''(t₀) = ∫ ∂_t² J(g₀, g_t) dV_{g₀}`,

the derivatives of `J` being taken at `t = t₀`. The integrands vanish outside `K`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_of_isCompact` and
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_deriv_relativeVolume_of_isCompact`: the first two
  derivatives of the relative volume of a compactly supported variation of a metric. They are the
  noncompact case of `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume` and
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_deriv_relativeVolume`.
-/

public section

open Bundle MeasureTheory Set Function TauCeti Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n n' : ℕ∞ω} [LindelofSpace M] [T2Space M]
  {g₀ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {g : ℝ → ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x)} {t₀ : ℝ}
  {K : Set M}

omit [FiniteDimensional ℝ E] [LindelofSpace M] [T2Space M] in
/-- The preimage of a compact set of `M` in the copy of `M` carrying `g₀` is compact. -/
private theorem isCompact_preimage_ofWithMetric (hK : IsCompact K) :
    IsCompact (WithMetric.ofWithMetric ⁻¹' K : Set (WithMetric g₀)) :=
  WithMetric.coe_homeomorph g₀ ▸ (WithMetric.homeomorph g₀).isCompact_preimage.mpr hK

omit [LindelofSpace M] [T2Space M] in
/-- The integrand `J(g₀, g_t) - 1` of the relative volume vanishes outside `K` for `t` near `t₀`
when `g_t = g₀` outside `K` for `t` near `t₀`. -/
private theorem eventually_relativeVolume_integrand_eq_zero
    (hgK : ∀ᶠ t in 𝓝 t₀, ∀ x ∉ K, (g t).inner x = g₀.inner x) :
    ∀ᶠ t in 𝓝 t₀, ∀ a ∉ (WithMetric.ofWithMetric ⁻¹' K : Set (WithMetric g₀)),
      relativeVolumeDensity g₀ (g t) a.ofWithMetric - 1 = 0 := by
  filter_upwards [hgK] with t ht a ha
  rw [relativeVolumeDensity_congr g₀ (g t) (g₁ := g₀) (g₂ := g₀) rfl (ht _ ha),
    relativeVolumeDensity_self, sub_self]

/-- **The first variation of the relative volume of a compactly supported variation.** Let `K` be
a compact subset of a manifold `M`, not necessarily compact, and `g_t` a family of metrics with
`g_t = g₀` outside `K` for all `t` near `t₀`. If the inner products of `g₀` are `C¹` at the points
of `K`, and those of `g_t` are `C¹` jointly in `(t, x)` at the points `(t₀, x)` with `x ∈ K`, then
the relative volume `t ↦ ∫ (J(g₀, g_t) - 1) dV_{g₀}` has derivative `∫ ∂_t J(g₀, g_t) dV_{g₀}`
at `t₀`. -/
theorem hasDerivAt_relativeVolume_of_isCompact [IsManifold I 2 M] (hK : IsCompact K)
    (hg₀ : ∀ x ∈ K, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun x : M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (g₀.inner x)) x)
    (hg : ∀ x ∈ K, ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x))
    (hgK : ∀ᶠ t in 𝓝 t₀, ∀ x ∉ K, (g t).inner x = g₀.inner x) :
    HasDerivAt (fun t ↦ relativeVolume g₀ (g t))
      (∫ x, deriv (fun s ↦ relativeVolumeDensity g₀ (g s) x.ofWithMetric) t₀
        ∂riemannianVolume I (WithMetric g₀)) t₀ := by
  have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  have hK' := isCompact_preimage_ofWithMetric (g₀ := g₀) hK
  simpa only [relativeVolume_def, deriv_sub_const] using
    hK'.hasDerivAt_parametric_integral (J := I) hK'.measurableSet hK'.measure_lt_top.ne
      (fun a ha ↦ contMDiffAt_relativeVolume_integrand (hg₀ _ ha) (hg _ ha))
      (eventually_relativeVolume_integrand_eq_zero hgK)

/-- **The second variation of the relative volume of a compactly supported variation.** Let `K` be
a compact subset of a manifold `M`, not necessarily compact, and `g_t` a family of metrics with
`g_t = g₀` outside `K` for all `t` near `t₀`. If the inner products of `g₀` are `C²` at the points
of `K`, and those of `g_t` are `C²` jointly in `(t, x)` at the points `(t₀, x)` with `x ∈ K`, then
the derivative of the relative volume `t ↦ ∫ (J(g₀, g_t) - 1) dV_{g₀}` has derivative
`∫ ∂_t² J(g₀, g_t) dV_{g₀}` at `t₀`. -/
theorem hasDerivAt_deriv_relativeVolume_of_isCompact [IsManifold I 3 M] (hK : IsCompact K)
    (hg₀ : ∀ x ∈ K, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x : M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (g₀.inner x)) x)
    (hg : ∀ x ∈ K, ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x))
    (hgK : ∀ᶠ t in 𝓝 t₀, ∀ x ∉ K, (g t).inner x = g₀.inner x) :
    HasDerivAt (deriv fun t ↦ relativeVolume g₀ (g t))
      (∫ x, deriv (fun s ↦ deriv (fun r ↦ relativeVolumeDensity g₀ (g r) x.ofWithMetric) s) t₀
        ∂riemannianVolume I (WithMetric g₀)) t₀ := by
  have : IsManifold I (2 + 1) M := IsManifold.of_le (n := 3) (by norm_num)
  have : IsManifold I 2 M := IsManifold.of_le (n := 3) (by norm_num)
  have hK' := isCompact_preimage_ofWithMetric (g₀ := g₀) hK
  simpa only [relativeVolume_def, deriv_sub_const] using
    hK'.hasDerivAt_deriv_parametric_integral (J := I) hK'.measurableSet hK'.measure_lt_top.ne
      (fun a ha ↦ contMDiffAt_relativeVolume_integrand (hg₀ _ ha) (hg _ ha))
      (eventually_relativeVolume_integrand_eq_zero hgK)

end Bundle.ContMDiffRiemannianMetric
