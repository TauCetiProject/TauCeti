/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Deriv
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Volume

/-!
# The relative volume of a family of metrics

For a family of metrics `g_t` whose inner products depend `C^k` jointly on `(t, x)`, and a
reference metric `g` whose inner products are `C^k`, the relative density
`(t, x) ↦ J(g, g_t)(x)` is `C^k`; this applies in particular to `g = g_{t₀}`. On a compact
manifold, the relative volume
`V(t) = V(g₀, g_t)` with respect to any fixed metric `g₀` is then `C^k` in `t`. For `k = 1` and
`k = 2` its first two derivatives at `t₀` are computed by differentiation under the integral
sign, with the density and the volume taken relative to `g_{t₀}`:

`V'(t₀) = ∫ ∂_t J(g_{t₀}, g_t) dV_{g_{t₀}}` and `V''(t₀) = ∫ ∂_t² J(g_{t₀}, g_t) dV_{g_{t₀}}`,

the derivatives of `J` being taken at `t = t₀`. Changing the reference metric `g₀` changes `V`
by a constant.

## Main results

* `Bundle.ContMDiffRiemannianMetric.contDiffAt_relativeVolume`,
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume` and
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_deriv_relativeVolume`: regularity and the first
  two derivatives of the relative volume of a family of metrics on a compact manifold.
-/

public section

open Bundle MeasureTheory Set Function TauCeti
open scoped Manifold ContDiff Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n n' : ℕ∞ω}

section Family

/-! ### Families of metrics -/

variable {g₀ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {g : ℝ → ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x)} {t₀ : ℝ}

/-- The integrand `(t, x) ↦ J(g_{t₀}, g_t)(x) - 1` of the relative volume with respect to
`g_{t₀}`, on the copy of `M` carrying `g_{t₀}`, is `C^k` at `(t₀, x)` for every `x` when the
inner products of `g_t` are `C^k` jointly in `(t, x)` at every point `(t₀, x)`. -/
private theorem contMDiffAt_relativeVolume_integrand {k : ℕ∞ω} [IsManifold I (k + 1) M]
    (hg : ∀ x : M, ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) k
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x)) (x : WithMetric (g t₀)) :
    ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) k
      (uncurry fun (t : ℝ) (y : WithMetric (g t₀)) ↦
        relativeVolumeDensity (g t₀) (g t) y.ofWithMetric - 1) (t₀, x) :=
  ((contMDiffAt_uncurry_relativeVolumeDensity
    ((hg x.ofWithMetric).comp x.ofWithMetric (contMDiffAt_const.prodMk contMDiffAt_id))
    (hg x.ofWithMetric)).comp (t₀, x) (contMDiffAt_fst.prodMk
      ((WithMetric.contMDiff_ofWithMetric (g := g t₀)).contMDiffAt.comp _ contMDiffAt_snd))).sub
    contMDiffAt_const

variable [CompactSpace M]

/-- On a compact manifold, the relative volume of `g_t` with respect to `g₀` differs from the
relative volume with respect to `g_{t₀}` by a constant. -/
private theorem relativeVolume_eq_add_const :
    (fun t ↦ relativeVolume g₀ (g t)) =
      fun t ↦ relativeVolume (g t₀) (g t) + relativeVolume g₀ (g t₀) :=
  funext fun t ↦ by rw [add_comm, relativeVolume_add_relativeVolume]

/-- **Regularity of the relative volume of a family of metrics.** On a compact manifold, if the
inner products of a family of metrics `g_t` are `C^k` jointly in `(t, x)` at every point
`(t₀, x)`, then the relative volume of `g_t` with respect to any fixed metric `g₀` is a `C^k`
function of `t` at `t₀`. -/
theorem contDiffAt_relativeVolume [T2Space M] {k : ℕ∞} [IsManifold I (k + 1) M]
    (hg : ∀ x : M, ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) k
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x)) :
    ContDiffAt ℝ k (fun t ↦ relativeVolume g₀ (g t)) t₀ := by
  have : IsManifold I k M := IsManifold.of_le (n := (k : ℕ∞ω) + 1) le_self_add
  rw [relativeVolume_eq_add_const (t₀ := t₀)]
  simp only [relativeVolume_def]
  exact (contMDiffAt_parametric_integral (I := 𝓘(ℝ)) (J := I)
    (contMDiffAt_relativeVolume_integrand hg)).contDiffAt.add contDiffAt_const

/-- **The first variation of the relative volume of a family of metrics.** On a compact manifold,
if the inner products of a family of metrics `g_t` are `C^1` jointly in `(t, x)` at every point
`(t₀, x)`, then the relative volume of `g_t` with respect to any fixed metric `g₀` has derivative
`∫ ∂_t J(g_{t₀}, g_t) dV_{g_{t₀}}` at `t₀`. -/
theorem hasDerivAt_relativeVolume [IsManifold I 2 M]
    (hg : ∀ x : M, ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x)) :
    HasDerivAt (fun t ↦ relativeVolume g₀ (g t))
      (∫ x, deriv (fun s ↦ relativeVolumeDensity (g t₀) (g s) x.ofWithMetric) t₀
        ∂riemannianVolume I (WithMetric (g t₀))) t₀ := by
  have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  rw [relativeVolume_eq_add_const (t₀ := t₀)]
  simpa only [relativeVolume_def, deriv_sub_const] using
    (hasDerivAt_parametric_integral (J := I) (contMDiffAt_relativeVolume_integrand hg)).add_const
      (relativeVolume g₀ (g t₀))

/-- **The second variation of the relative volume of a family of metrics.** On a compact manifold,
if the inner products of a family of metrics `g_t` are `C^2` jointly in `(t, x)` at every point
`(t₀, x)`, then the derivative of the relative volume of `g_t` with respect to any fixed metric
`g₀` has derivative `∫ ∂_t² J(g_{t₀}, g_t) dV_{g_{t₀}}` at `t₀`. -/
theorem hasDerivAt_deriv_relativeVolume [IsManifold I 3 M]
    (hg : ∀ x : M, ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x)) :
    HasDerivAt (deriv fun t ↦ relativeVolume g₀ (g t))
      (∫ x, deriv (fun s ↦ deriv (fun r ↦ relativeVolumeDensity (g t₀) (g r) x.ofWithMetric) s)
        t₀ ∂riemannianVolume I (WithMetric (g t₀))) t₀ := by
  have : IsManifold I (2 + 1) M := IsManifold.of_le (n := 3) (by norm_num)
  have : IsManifold I 2 M := IsManifold.of_le (n := 3) (by norm_num)
  rw [relativeVolume_eq_add_const (t₀ := t₀)]
  simpa only [relativeVolume_def, deriv_sub_const, deriv_add_const'] using
    hasDerivAt_deriv_parametric_integral (J := I) (μ := riemannianVolume I (WithMetric (g t₀)))
      (contMDiffAt_relativeVolume_integrand hg)

end Family

end Bundle.ContMDiffRiemannianMetric
