/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Deriv
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Basic

/-!
# The relative volume and its dependence on a family of metrics

Let `g` and `g'` be two Riemannian metrics on a manifold `M`, and let
`J = Bundle.ContMDiffRiemannianMetric.relativeVolumeDensity g g'` be the relative volume
density, so that `dV_{g'} = J dV_g`. The *relative volume* of `g'` with respect to `g` is

`V(g, g') = ∫ (J - 1) dV_g`.

On a compact manifold it is `Vol(g') - Vol(g)`. The integrand vanishes wherever `g'` agrees
with `g`, so the relative volume also makes sense for variations with compact support on
a noncompact manifold, where the total volumes may be infinite.

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

The motivating family is that of the metrics `g_t = F_t^* h` induced by a jointly smooth family
of immersions `F_t : M → N` into a Riemannian manifold `(N, h)`, measured relative to
`g_0 = F_0^* h`. The manifold `M` may have boundary and corners, no orientation is used, and the
family is not required to fix the boundary.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.relativeVolume`: the relative volume `∫ (J - 1) dV_g`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.relativeVolume_eq_sub`: on a compact manifold the relative
  volume is the difference of the total volumes.
* `Bundle.ContMDiffRiemannianMetric.relativeVolume_add_relativeVolume`: on a compact manifold,
  relative volumes add up along a chain of metrics.
* `Bundle.ContMDiffRiemannianMetric.contDiffAt_relativeVolume`,
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume` and
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_deriv_relativeVolume`: regularity and the first
  two derivatives of the relative volume of a family of metrics on a compact manifold.
* `Bundle.ContMDiffRiemannianMetric.contDiff_relativeVolume_pullback`,
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback` and
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_deriv_relativeVolume_pullback`: the same for a
  family of immersions of a compact manifold.
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

section RelativeVolume

variable [LindelofSpace M]

/-- The **relative volume** of a Riemannian metric `g'` with respect to a Riemannian metric `g`:
the integral `∫ (J - 1) dV_g` of the relative volume density `J` of `g'` with respect to `g`,
minus one, against the Riemannian volume of `g`. -/
def relativeVolume
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x)) : ℝ :=
  ∫ x, (relativeVolumeDensity g g' x.ofWithMetric - 1) ∂riemannianVolume I (WithMetric g)

variable (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
  (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))

/-- The definition of the relative volume. -/
theorem relativeVolume_def :
    relativeVolume g g' =
      ∫ x, (relativeVolumeDensity g g' x.ofWithMetric - 1) ∂riemannianVolume I (WithMetric g) :=
  (rfl)

/-- The relative volume of a metric with respect to itself is zero. -/
@[simp]
theorem relativeVolume_self : relativeVolume g g = 0 := by
  simp [relativeVolume_def]

end RelativeVolume

section CompactSpace

variable [CompactSpace M] (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
  (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))

/-- **The relative volume on a compact manifold.** On a compact manifold, the relative volume of
`g'` with respect to `g` is the difference `Vol(g') - Vol(g)` of the total volumes. -/
theorem relativeVolume_eq_sub :
    relativeVolume g g' =
      riemannianTotalVolume I (WithMetric g') - riemannianTotalVolume I (WithMetric g) := by
  have hJ : Integrable (fun x : WithMetric g ↦ relativeVolumeDensity g g' x.ofWithMetric)
      (riemannianVolume I (WithMetric g)) := by
    simpa only [smul_eq_mul, mul_one] using
      (integrable_riemannianVolume_iff_integrable_relativeVolumeDensity_smul g g'
        fun _ ↦ (1 : ℝ)).1 (integrable_const 1)
  rw [relativeVolume_def, integral_sub hJ (integrable_const 1),
    riemannianTotalVolume_eq_integral_relativeVolumeDensity, integral_const_riemannianVolume,
    one_mul]

variable {n'' : ℕ∞ω} (g'' : ContMDiffRiemannianMetric I n'' E (fun x : M ↦ TangentSpace I x))

/-- On a compact manifold, relative volumes add up along a chain of three metrics. -/
theorem relativeVolume_add_relativeVolume :
    relativeVolume g g' + relativeVolume g' g'' = relativeVolume g g'' := by
  rw [relativeVolume_eq_sub, relativeVolume_eq_sub, relativeVolume_eq_sub]
  ring

end CompactSpace

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

section Immersion

/-! ### Families of immersions -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  (h : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) {Φ : ℝ → M → N}

variable [CompactSpace M]

/-- **Regularity of the relative volume of a family of immersions.** For a jointly `C^(n+1)`
family of immersions `F_t` of a compact manifold into a manifold with a `C^n` metric `h`, the
relative volume of `F_t^* h` with respect to `F_0^* h` is a `C^k` function of `t` for every
`k ≤ n`. -/
theorem contDiff_relativeVolume_pullback [T2Space M] {k : ℕ∞} [IsManifold I (k + 1) M]
    (hk : (k : ℕ∞ω) ≤ n) (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) :
    ContDiff ℝ k fun t ↦ relativeVolume (h.pullback (Φ 0) (hΦ.curry_right (x := 0)) (hinj 0))
      (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_relativeVolume fun _ ↦
    (h.contMDiffAt_uncurry_pullback hΦ hinj _).of_le hk

/-- **The first variation of the relative volume of a family of immersions.** For a jointly
`C^(n+1)` family of immersions `F_t` of a compact manifold into a manifold with a `C^n` metric `h`,
`n ≥ 1`, the relative volume of `F_t^* h` with respect to `F_0^* h` has derivative
`∫ ∂_t J(F_{t₀}^* h, F_t^* h) dV_{F_{t₀}^* h}` at every `t₀`, where `J` is the relative volume
density. -/
theorem hasDerivAt_relativeVolume_pullback [IsManifold I 2 M] (hn : 1 ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ relativeVolume (h.pullback (Φ 0) (hΦ.curry_right (x := 0)) (hinj 0))
        (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)))
      (∫ x, deriv (fun s ↦ relativeVolumeDensity
          (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
          (h.pullback (Φ s) (hΦ.curry_right (x := s)) (hinj s)) x.ofWithMetric) t₀
        ∂riemannianVolume I (WithMetric (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))))
      t₀ :=
  hasDerivAt_relativeVolume fun _ ↦ (h.contMDiffAt_uncurry_pullback hΦ hinj _).of_le hn

/-- **The second variation of the relative volume of a family of immersions.** For a jointly
`C^(n+1)` family of immersions `F_t` of a compact manifold into a manifold with a `C^n` metric `h`,
`n ≥ 2`, the derivative of the relative volume of `F_t^* h` with respect to `F_0^* h` has
derivative `∫ ∂_t² J(F_{t₀}^* h, F_t^* h) dV_{F_{t₀}^* h}` at every `t₀`, where `J` is the
relative volume density. -/
theorem hasDerivAt_deriv_relativeVolume_pullback [IsManifold I 3 M] (hn : 2 ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) (t₀ : ℝ) :
    HasDerivAt (deriv fun t ↦ relativeVolume (h.pullback (Φ 0) (hΦ.curry_right (x := 0)) (hinj 0))
        (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)))
      (∫ x, deriv (fun s ↦ deriv (fun r ↦ relativeVolumeDensity
          (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
          (h.pullback (Φ r) (hΦ.curry_right (x := r)) (hinj r)) x.ofWithMetric) s) t₀
        ∂riemannianVolume I (WithMetric (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))))
      t₀ :=
  hasDerivAt_deriv_relativeVolume fun _ ↦ (h.contMDiffAt_uncurry_pullback hΦ hinj _).of_le hn

end Immersion

end Bundle.ContMDiffRiemannianMetric
