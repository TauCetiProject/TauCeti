/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Family

/-!
# The relative volume of a family of immersions

The metrics `g_t = F_t^* h` induced by a jointly smooth family of immersions `F_t : M → N` into a
Riemannian manifold `(N, h)` form a family of metrics to which
`TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Family` applies. On a compact
manifold, their relative volume with respect to any fixed metric `g₀`, such as `F_0^* h`, is
therefore as regular in `t` as the family allows, with first two derivatives given by
differentiation under the integral sign. The family is not required to fix the boundary.

## Main results

* `Bundle.ContMDiffRiemannianMetric.contDiff_relativeVolume_pullback`,
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback` and
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_deriv_relativeVolume_pullback`: regularity and the
  first two derivatives of the relative volume of a family of immersions of a compact manifold.
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

section Immersion

/-! ### Families of immersions -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  (h : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) {Φ : ℝ → M → N}
  {n₀ : ℕ∞ω} {g₀ : ContMDiffRiemannianMetric I n₀ E (fun x : M ↦ TangentSpace I x)}

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
