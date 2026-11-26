/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.CompactSupport
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Family

/-!
# The relative volume of a family of immersions

The metrics `g_t = F_t^* h` induced by a jointly smooth family of immersions `F_t : M → N` into a
Riemannian manifold `(N, h)` form a family of metrics to which
`TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Family` applies. On a compact
manifold, their relative volume with respect to any fixed metric `g₀`, such as `F_0^* h`, is
therefore as regular in `t` as the family allows, with first two derivatives given by
differentiation under the integral sign. The family is not required to fix the boundary.

On a manifold that need not be compact, if `F_t = F_{t₀}` outside a compact set `K` for `t` near
`t₀`, the induced metrics `F_t^* h` agree with `F_{t₀}^* h` outside `K`, so
`TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.CompactSupport` applies instead.

## Main results

* `Bundle.ContMDiffRiemannianMetric.contDiff_relativeVolume_pullback`,
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback` and
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_deriv_relativeVolume_pullback`: regularity and the
  first two derivatives of the relative volume of a family of immersions of a compact manifold.
* `Bundle.ContMDiffRiemannianMetric.contDiffAt_relativeVolume_pullback_of_isCompact`,
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback_of_isCompact` and
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_deriv_relativeVolume_pullback_of_isCompact`:
  regularity and the first two derivatives of the relative volume of a family of immersions of a
  manifold, not necessarily compact, that is constant outside a compact set.
-/

public section

open Bundle MeasureTheory Set Function TauCeti Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n n' : ℕ∞ω}

section Immersion

/-! ### Families of immersions -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  (h : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) {Φ : ℝ → M → N}
  {n₀ : ℕ∞ω} {g₀ : ContMDiffRiemannianMetric I n₀ E (fun x : M ↦ TangentSpace I x)}

/-- **Regularity of the relative volume of a compactly supported family of immersions.** Let
`F_t : M → N` be a jointly `C^(n+1)` family of immersions of a manifold `M`, not necessarily
compact, into a manifold with a `C^n` metric `h`, with `F_t = F_{t₀}` outside a compact set `K`
for all `t` near `t₀`. Then the relative volume of `F_t^* h` with respect to `F_{t₀}^* h` is `C^k`
at `t₀` for every `k ≤ n`. -/
theorem contDiffAt_relativeVolume_pullback_of_isCompact [LindelofSpace M] [T2Space M] {k : ℕ∞}
    [IsManifold I (k + 1) M] (hk : (k : ℕ∞ω) ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) {t₀ : ℝ} {K : Set M} (hK : IsCompact K)
    (hΦK : ∀ᶠ t in 𝓝 t₀, ∀ x ∉ K, Φ t x = Φ t₀ x) :
    ContDiffAt ℝ k (fun t ↦ relativeVolume
      (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
      (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t))) t₀ :=
  contDiffAt_relativeVolume_of_isCompact hK
    (fun x _ ↦ ((h.contMDiffAt_uncurry_pullback hΦ hinj (t₀, x)).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)).of_le hk)
    (fun x _ ↦ (h.contMDiffAt_uncurry_pullback hΦ hinj (t₀, x)).of_le hk)
    (h.eventually_forall_notMem_pullback_inner_eq hΦ hinj hK.isClosed hΦK)

/-- **The first variation of the relative volume of a compactly supported family of
immersions.** Let `F_t : M → N` be a jointly `C^(n+1)` family of immersions of a manifold `M`, not
necessarily compact, into a manifold with a `C^n` metric `h`, `n ≥ 1`, with `F_t = F_{t₀}` outside a
compact set `K` for `t` near `t₀`. Then the relative volume of `F_t^* h` with respect to
`F_{t₀}^* h` has derivative `∫ ∂_t J(F_{t₀}^* h, F_t^* h) dV_{F_{t₀}^* h}` at `t₀`, where `J` is
the relative volume density. -/
theorem hasDerivAt_relativeVolume_pullback_of_isCompact [LindelofSpace M] [T2Space M]
    [IsManifold I 2 M] (hn : 1 ≤ n) (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) {t₀ : ℝ} {K : Set M} (hK : IsCompact K)
    (hΦK : ∀ᶠ t in 𝓝 t₀, ∀ x ∉ K, Φ t x = Φ t₀ x) :
    HasDerivAt (fun t ↦ relativeVolume
        (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
        (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)))
      (∫ x, deriv (fun s ↦ relativeVolumeDensity
          (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
          (h.pullback (Φ s) (hΦ.curry_right (x := s)) (hinj s)) x.ofWithMetric) t₀
        ∂riemannianVolume I (WithMetric (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))))
      t₀ :=
  hasDerivAt_relativeVolume_of_isCompact hK
    (fun x _ ↦ ((h.contMDiffAt_uncurry_pullback hΦ hinj (t₀, x)).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)).of_le hn)
    (fun x _ ↦ (h.contMDiffAt_uncurry_pullback hΦ hinj (t₀, x)).of_le hn)
    (h.eventually_forall_notMem_pullback_inner_eq hΦ hinj hK.isClosed hΦK)

/-- **The second variation of the relative volume of a compactly supported family of
immersions.** Let `F_t : M → N` be a jointly `C^(n+1)` family of immersions of a manifold `M`, not
necessarily compact, into a manifold with a `C^n` metric `h`, `n ≥ 2`, with `F_t = F_{t₀}` outside a
compact set `K` for `t` near `t₀`. Then the derivative of the relative volume of `F_t^* h` with
respect to `F_{t₀}^* h` has derivative `∫ ∂_t² J(F_{t₀}^* h, F_t^* h) dV_{F_{t₀}^* h}` at `t₀`. -/
theorem hasDerivAt_deriv_relativeVolume_pullback_of_isCompact [LindelofSpace M] [T2Space M]
    [IsManifold I 3 M] (hn : 2 ≤ n) (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) {t₀ : ℝ} {K : Set M} (hK : IsCompact K)
    (hΦK : ∀ᶠ t in 𝓝 t₀, ∀ x ∉ K, Φ t x = Φ t₀ x) :
    HasDerivAt (deriv fun t ↦ relativeVolume
        (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
        (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)))
      (∫ x, deriv (fun s ↦ deriv (fun r ↦ relativeVolumeDensity
          (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
          (h.pullback (Φ r) (hΦ.curry_right (x := r)) (hinj r)) x.ofWithMetric) s) t₀
        ∂riemannianVolume I (WithMetric (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))))
      t₀ :=
  hasDerivAt_deriv_relativeVolume_of_isCompact hK
    (fun x _ ↦ ((h.contMDiffAt_uncurry_pullback hΦ hinj (t₀, x)).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)).of_le hn)
    (fun x _ ↦ (h.contMDiffAt_uncurry_pullback hΦ hinj (t₀, x)).of_le hn)
    (h.eventually_forall_notMem_pullback_inner_eq hΦ hinj hK.isClosed hΦK)

variable [CompactSpace M]

/-- **Regularity of the relative volume of a family of immersions.** For a jointly `C^(n+1)`
family of immersions `F_t` of a compact manifold into a manifold with a `C^n` metric `h`, the
relative volume of `F_t^* h` with respect to any fixed metric `g₀`, such as `F_0^* h`, is a `C^k`
function of `t` for every `k ≤ n`. -/
theorem contDiff_relativeVolume_pullback [T2Space M] {k : ℕ∞} [IsManifold I (k + 1) M]
    (hk : (k : ℕ∞ω) ≤ n) (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) :
    ContDiff ℝ k fun t ↦
      relativeVolume g₀ (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_relativeVolume fun _ ↦
    (h.contMDiffAt_uncurry_pullback hΦ hinj _).of_le hk

/-- **The first variation of the relative volume of a family of immersions.** For a jointly
`C^(n+1)` family of immersions `F_t` of a compact manifold into a manifold with a `C^n` metric `h`,
`n ≥ 1`, the relative volume of `F_t^* h` with respect to any fixed metric `g₀`, such as
`F_0^* h`, has derivative `∫ ∂_t J(F_{t₀}^* h, F_t^* h) dV_{F_{t₀}^* h}` at every `t₀`, where `J`
is the relative volume density. -/
theorem hasDerivAt_relativeVolume_pullback [IsManifold I 2 M] (hn : 1 ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ relativeVolume g₀ (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)))
      (∫ x, deriv (fun s ↦ relativeVolumeDensity
          (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
          (h.pullback (Φ s) (hΦ.curry_right (x := s)) (hinj s)) x.ofWithMetric) t₀
        ∂riemannianVolume I (WithMetric (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))))
      t₀ :=
  hasDerivAt_relativeVolume fun _ ↦ (h.contMDiffAt_uncurry_pullback hΦ hinj _).of_le hn

/-- **The second variation of the relative volume of a family of immersions.** For a jointly
`C^(n+1)` family of immersions `F_t` of a compact manifold into a manifold with a `C^n` metric `h`,
`n ≥ 2`, the derivative of the relative volume of `F_t^* h` with respect to any fixed metric
`g₀`, such as `F_0^* h`, has derivative `∫ ∂_t² J(F_{t₀}^* h, F_t^* h) dV_{F_{t₀}^* h}` at every
`t₀`, where `J` is the relative volume density. -/
theorem hasDerivAt_deriv_relativeVolume_pullback [IsManifold I 3 M] (hn : 2 ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) (t₀ : ℝ) :
    HasDerivAt (deriv fun t ↦
        relativeVolume g₀ (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)))
      (∫ x, deriv (fun s ↦ deriv (fun r ↦ relativeVolumeDensity
          (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
          (h.pullback (Φ r) (hΦ.curry_right (x := r)) (hinj r)) x.ofWithMetric) s) t₀
        ∂riemannianVolume I (WithMetric (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))))
      t₀ :=
  hasDerivAt_deriv_relativeVolume fun _ ↦ (h.contMDiffAt_uncurry_pullback hΦ hinj _).of_le hn

end Immersion

end Bundle.ContMDiffRiemannianMetric
