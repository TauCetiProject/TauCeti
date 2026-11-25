/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Volume
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic

/-!
# The relative volume of a compactly supported variation of a metric

On a manifold `M` that need not be compact, let `g_t` be a family of metrics that agrees with a
fixed metric `g₀` outside one compact set `K`, for all `t` near `t₀`. The relative density
`J(g₀, g_t)` is then `1` off `K`, so the relative volume `V(t) = ∫ (J(g₀, g_t) - 1) dV_{g₀}` is
finite without `M` having finite volume, and it is `C^k` in `t` at `t₀` when the inner products of
`g₀` are `C^k` at the points of `K` and those of `g_t` are `C^k` jointly in `(t, x)` at the points
`(t₀, x)` with `x ∈ K` (`Bundle.ContMDiffRiemannianMetric.contDiffAt_relativeVolume_of_isCompact`).
This is the noncompact case of the relative-volume functional, whose compact case is
`Bundle.ContMDiffRiemannianMetric.contDiffAt_relativeVolume`.

For a jointly smooth family of immersions `F_t : M → N` into a Riemannian manifold `(N, h)` with
`F_t = F_{t₀}` outside a compact set `K` for `t` near `t₀`, the induced metrics `F_t^* h` agree
with `F_{t₀}^* h` outside `K`, so the relative volume of `F_t^* h` with respect to `F_{t₀}^* h` is
`C^k` at `t₀` for every `k ≤ n`
(`Bundle.ContMDiffRiemannianMetric.contDiffAt_relativeVolume_pullback_of_isCompact`), the
noncompact case of `Bundle.ContMDiffRiemannianMetric.contDiff_relativeVolume_pullback`.
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
  · exact contMDiffAt_relativeVolume_integrand (hg₀ _ ha) (hg _ ha)
  · filter_upwards [hgK] with t ht a ha
    rw [relativeVolumeDensity_congr g₀ (g t) (g₁ := g₀) (g₂ := g₀) rfl (ht _ ha),
      relativeVolumeDensity_self, sub_self]

section Immersion

/-! ### Families of immersions -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  (h : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) {Φ : ℝ → M → N}

omit [LindelofSpace M] in
/-- Two maps that agree near `x` induce the same pullback metric at `x`. -/
private theorem pullback_inner_eq_of_eventuallyEq {f₁ f₂ : M → N}
    (hf₁ : ContMDiff I J (n + 1) f₁) (hf₂ : ContMDiff I J (n + 1) f₂)
    (hinj₁ : ∀ x, Injective (mfderiv I J f₁ x)) (hinj₂ : ∀ x, Injective (mfderiv I J f₂ x))
    {x : M} (hx : f₁ =ᶠ[𝓝 x] f₂) :
    (h.pullback f₁ hf₁ hinj₁).inner x = (h.pullback f₂ hf₂ hinj₂).inner x := by
  ext v w
  rw [pullback_inner, pullback_inner, hx.mfderiv_eq, hx.eq_of_nhds]
  rfl

/-- **Regularity of the relative volume of a compactly supported family of immersions.** Let
`F_t : M → N` be a jointly `C^(n+1)` family of immersions of a manifold `M`, not necessarily
compact, into a manifold with a `C^n` metric `h`, with `F_t = F_{t₀}` outside a compact set `K`
for all `t` near `t₀`. Then the relative volume of `F_t^* h` with respect to `F_{t₀}^* h` is `C^k`
at `t₀` for every `k ≤ n`. -/
theorem contDiffAt_relativeVolume_pullback_of_isCompact [T2Space M] {k : ℕ∞}
    [IsManifold I (k + 1) M] (hk : (k : ℕ∞ω) ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) {K : Set M} (hK : IsCompact K)
    (hΦK : ∀ᶠ t in 𝓝 t₀, ∀ x ∉ K, Φ t x = Φ t₀ x) :
    ContDiffAt ℝ k (fun t ↦ relativeVolume
      (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
      (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t))) t₀ := by
  refine contDiffAt_relativeVolume_of_isCompact hK (fun x _ ↦ ?_) (fun x _ ↦ ?_) ?_
  · exact ((h.contMDiffAt_uncurry_pullback hΦ hinj (t₀, x)).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)).of_le hk
  · exact (h.contMDiffAt_uncurry_pullback hΦ hinj (t₀, x)).of_le hk
  · filter_upwards [hΦK] with t ht x hx
    refine h.pullback_inner_eq_of_eventuallyEq _ _ _ _ ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact ht y hy

end Immersion

end Bundle.ContMDiffRiemannianMetric
