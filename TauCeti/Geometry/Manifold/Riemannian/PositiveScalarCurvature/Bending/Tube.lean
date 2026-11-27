/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Bending.Cylinder
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Bending.Reparametrization

/-!
# Bending a metric which satisfies the tube estimates

Near a sphere `S^k` of codimension `q = n - k` in a Riemannian `n`-manifold, write the metric as
`dr² + g r`, where `r` is the distance to the sphere and `g r` is the metric induced on the distance
tube of radius `r`, read on a fixed manifold `M` of dimension `n - 1`. Here this is a metric `G` on
`M × ℝ` which is the cylinder metric `g τ + dτ²` at every point `(y, τ)`. In a basis of the model
space let `A` be the Gram matrix of `g s` at `y`, and `A'` its derivative in `s`. We use the sign
convention in which the round sphere of radius `s` has principal curvatures `-1 / s`; in it
`-tr (A⁻¹ A') / 2` is the sum of the principal curvatures of the tube `M × {s}`.
The *tube estimates* are
`(q - 1) (q - 2) / s² - C / s - C ≤ Scal(g s)` and `tr (A⁻¹ A') ≤ 2 (q - 1) / s + C`
for `0 < s < r₀`, with an error constant `C`. For the round tubes
`g s = g_N + s² g_(S^(q - 1))` of a product of a metric `g_N` with the flat normal disc,
`Scal(g s) = Scal(g_N) + (q - 1) (q - 2) / s²` and `tr (A⁻¹ A') = 2 (q - 1) / s`, so they hold
with `C = 0` when `Scal(g_N) ≥ 0`. For a general metric they follow, through the Gauss equation,
from the estimates that `q - 1` principal curvatures of the tube of radius `s` are `-1 / s + O(1)`
and the others are `O(1)`.

A smooth metric `G` on all of `M × ℝ` cannot satisfy the tube estimates for every small `s > 0`
when `q ≥ 3`: the scalar curvature of `g s` stays bounded as `s → 0`. So the results below only
ask for the estimates at the radii which the bending curve visits, which are at least the radius
`ρ > 0` of its final vertical part. Below `ρ` the metric `G` may be changed freely; for instance
the round tubes `g s = g_N + f(s)² g_(S^(q - 1))`, with `f` smooth and positive and `f s = s` for
`s ≥ ρ`, satisfy the estimates on `[ρ, r₀)` with `C = 0` when `Scal(g_N) ≥ 0`.

A unit speed Gromov–Lawson bending curve `u ↦ (r u, h u)` (`TauCeti.IsGromovLawsonBendingCurve`
with speed `1`) sweeps out a hypersurface of `M × ℝ × ℝ`, with the metric `G + dh²`, whose induced
metric is the reparametrised cylinder `du² + g (r u)`, that is `G.compTime` along `r`. Its scalar
curvature is `cos² θ Scal(G) + sin² θ Scal(g r) - k sin θ tr (A⁻¹ A')`
(`Bundle.ContMDiffRiemannianMetric.scalarCurvature_compTime_of_forall_inner_eq_cylinder`), where
`θ` is the angle and `k` the curvature of the curve. If `Scal(G) ≥ R₀` and the tube estimates hold,
this is at least the expression which the bending inequality for the lower bound `R₀` and the
error constant `C + R₀` makes positive; the extra `R₀` absorbs the loss `R₀ sin² θ` in the first
term. So the bent metric has positive scalar curvature
(`TauCeti.IsGromovLawsonBendingCurve.hasPositiveScalarCurvature_compTime`).

The bent metric is `G` reflected in the slice `τ = r 0` for `u ≤ 0`, where `r u = r 0 - u`, and it
is the product of `g ρ` with the line for `u` large, where `r u = ρ` for a radius `ρ < r₀`.
The reparametrisation depends only on `q`, `R₀`, `C` and `r₀`, and it works for every metric `G`
which satisfies the estimates on `[ρ, r₀)` (`TauCeti.exists_hasPositiveScalarCurvature_compTime`).
This is the metric which the Gromov–Lawson surgery construction glues to the original metric on
one side and to a handle on the other.

## Main results

* `TauCeti.IsGromovLawsonBendingCurve.scalarCurvature_compTime_pos`: the bent metric has positive
  scalar curvature at `(y, u)` when the ambient scalar curvature at `(y, r u)` is at least `R₀` and
  the tube estimates hold at `(y, r u)` inside the tube of radius `r₀`.
* `TauCeti.IsGromovLawsonBendingCurve.hasPositiveScalarCurvature_compTime`: the bent metric has
  positive scalar curvature when the estimates hold at the radii which the curve visits.
* `TauCeti.exists_hasPositiveScalarCurvature_compTime`: a reparametrisation `φ` of the cylinder,
  which is the reflection `φ u = φ 0 - u` for `u ≤ 0` with `φ 0 < r₀`, and constant equal to some
  `0 < ρ < r₀` for large `u`, such that the bent metric of every `G` satisfying the estimates on
  `[ρ, r₀)` has positive scalar curvature.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A.
* J. Rosenberg, S. Stolz, *Metrics of positive scalar curvature and connections with surgery*,
  Surveys on surgery theory, Vol. 2, Ann. of Math. Stud. 149 (2001), 353–386, Section 3.
-/

public section

noncomputable section

open Bundle Matrix Real Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
    (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)}
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {R₀ C r₀ : ℝ}

namespace IsGromovLawsonBendingCurve

variable {r h θ : ℝ → ℝ}

/-- **Bending under the tube estimates, pointwise.** Let `G` be a metric on `M × ℝ` which is the
cylinder metric `g τ + dτ²` at every point, and let `(r, h)` be a unit speed bending curve in
codimension `q` for the lower bound `R₀` and the error constant `C + R₀`. Let `y : M`, `u : ℝ`
and `s = r u`, and suppose that the scalar curvature of `G` at `(y, s)` is at least `R₀` and that,
if `s < r₀`, the tube estimates `(q - 1) (q - 2) / s² - C / s - C ≤ Scal(g s)(y)` and
`tr (A⁻¹ A') ≤ 2 (q - 1) / s + C` hold, where `A` is the Gram matrix of `g s` at `y` in a basis `b`
and `A'` its derivative in `s`. Then the bent metric `du² + g (r u)` has positive scalar curvature
at `(y, u)`. -/
theorem scalarCurvature_compTime_pos (hγ : IsGromovLawsonBendingCurve q R₀ (C + R₀) r₀ r h θ 1)
    (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p) (b : Module.Basis ι ℝ E) (y : M)
    (u : ℝ) (hR : R₀ ≤ G.scalarCurvature (y, r u))
    (hg : r u < r₀ →
      ((q : ℝ) - 1) * ((q : ℝ) - 2) / r u ^ 2 - C / r u - C ≤ (g (r u)).scalarCurvature y)
    (hA : r u < r₀ → ((of fun i j ↦ (g (r u)).inner y (b i) (b j))⁻¹ *
      of fun i j ↦ deriv (fun s ↦ (g s).inner y (b i) (b j)) (r u)).trace ≤
        2 * ((q : ℝ) - 1) / r u + C) :
    0 < (G.compTime hγ.contDiff_radius).scalarCurvature (y, u) := by
  have hR₀ : 0 < R₀ := by simpa [hγ.angle_of_nonpos le_rfl] using hγ.scalar_pos 0
  -- With unit speed, `r' = -cos θ` and `r'' = θ' sin θ`.
  have hr' : deriv r = fun u ↦ -cos (θ u) :=
    funext fun u ↦ by simpa using (hγ.hasDerivAt_radius u).deriv
  have hθ := (hγ.contDiff_angle.differentiable (by simp) u).hasDerivAt
  have hr'' : iteratedDeriv 2 r u = sin (θ u) * deriv θ u := by
    have h : HasDerivAt (fun u ↦ -cos (θ u)) (sin (θ u) * deriv θ u) u :=
      ((hasDerivAt_cos (θ u)).comp u hθ).neg.congr_deriv (by ring)
    rw [iteratedDeriv_succ, iteratedDeriv_one, hr', h.deriv]
  rw [ContMDiffRiemannianMetric.scalarCurvature_compTime_of_forall_inner_eq_cylinder hG
    hγ.contDiff_radius b y u, hr', hr'', neg_sq, cos_sq', sub_sub_cancel]
  set T := ((of fun i j ↦ (g (r u)).inner y (b i) (b j))⁻¹ *
    of fun i j ↦ deriv (fun s ↦ (g s).inner y (b i) (b j)) (r u)).trace
  have hs : 0 ≤ sin (θ u) := sin_nonneg_of_nonneg_of_le_pi (hγ.angle_nonneg u)
    (by linarith [hγ.angle_le_pi_div_two u, pi_pos])
  have hc : 0 ≤ 1 - sin (θ u) ^ 2 := sub_nonneg.2 (sin_sq_le_one _)
  have h₁ := mul_le_mul_of_nonneg_left hR hc
  by_cases hu : r u < r₀
  · -- Inside the tube, the tube estimates turn the bending inequality into positivity.
    have hk : 0 ≤ deriv θ u := hγ.monotone_angle.deriv_nonneg
    have hρ := hγ.radius_pos u
    have h₂ := mul_le_mul_of_nonneg_left (hg hu) (sq_nonneg (sin (θ u)))
    have h₃ : sin (θ u) * deriv θ u * T ≤ sin (θ u) * deriv θ u * (2 * ((q : ℝ) - 1) / r u + C) :=
      mul_le_mul_of_nonneg_left (hA hu) (mul_nonneg hs hk)
    have h₄ : 0 ≤ R₀ * sin (θ u) ^ 2 / r u := by positivity
    have h₅ : 0 ≤ R₀ * sin (θ u) * deriv θ u := by positivity
    have hpos := hγ.scalar_pos u
    simp only [Pi.one_apply, div_one] at hpos
    linear_combination hpos + h₁ + h₂ + h₃ + h₄ + h₅
  · -- Outside the tube the curve is still the `r`-axis, where the bent metric is `G`.
    rw [hγ.angle_of_nonpos (hγ.neg_of_le_radius (not_lt.1 hu)).le] at h₁ ⊢
    simp only [sin_zero] at h₁ ⊢
    linarith

/-- **Bending under the tube estimates.** Let `G` be a metric on `M × ℝ` which is the cylinder
metric `g τ + dτ²` at every point, and let `(r, h)` be a unit speed bending curve in codimension `q`
for the lower bound `R₀` and the error constant `C + R₀`. Suppose that at every radius `s = r u`
which the curve visits the scalar curvature of `G` is at least `R₀`, and, if `s < r₀`, the tube
estimates `(q - 1) (q - 2) / s² - C / s - C ≤ Scal(g s)` and `tr (A⁻¹ A') ≤ 2 (q - 1) / s + C` hold,
where `A` is a Gram matrix of `g s` and `A'` its derivative in `s`. Then the bent metric
`du² + g (r u)` has positive scalar curvature.

The estimates are only asked for at the radii `r u`, which are bounded below by the radius of the
final vertical part of the curve: a smooth `G` cannot satisfy them for all small `s > 0`. -/
theorem hasPositiveScalarCurvature_compTime
    (hγ : IsGromovLawsonBendingCurve q R₀ (C + R₀) r₀ r h θ 1)
    (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p) (b : Module.Basis ι ℝ E)
    (hR : ∀ y u, R₀ ≤ G.scalarCurvature (y, r u))
    (hg : ∀ y u, r u < r₀ →
      ((q : ℝ) - 1) * ((q : ℝ) - 2) / r u ^ 2 - C / r u - C ≤ (g (r u)).scalarCurvature y)
    (hA : ∀ y u, r u < r₀ → ((of fun i j ↦ (g (r u)).inner y (b i) (b j))⁻¹ *
      of fun i j ↦ deriv (fun s ↦ (g s).inner y (b i) (b j)) (r u)).trace ≤
        2 * ((q : ℝ) - 1) / r u + C) :
    (G.compTime hγ.contDiff_radius).HasPositiveScalarCurvature := by
  rw [ContMDiffRiemannianMetric.hasPositiveScalarCurvature_iff]
  rintro ⟨y, u⟩
  exact hγ.scalarCurvature_compTime_pos hG b y u (hR y u) (hg y u) (hA y u)

end IsGromovLawsonBendingCurve

/-- **The bent metric.** For every codimension `q ≥ 3`, lower bound `R₀ > 0`, error constant `C`
and tube radius `r₀ > 0` there are a smooth `φ : ℝ → ℝ` and a radius `0 < ρ < r₀` with
`ρ ≤ φ u` for all `u`, `φ u = φ 0 - u` for `u ≤ 0` with `φ 0 < r₀`, and `φ` constant equal to `ρ`
on a half-line `[u₁, ∞)`, with the following property. Let `G` be a metric on `M × ℝ` which is the
cylinder metric `g τ + dτ²` at every point, with scalar curvature at least `R₀` at every point
`(y, s)` with `s ≥ ρ`, and suppose that the tube estimates
`(q - 1) (q - 2) / s² - C / s - C ≤ Scal(g s)` and `tr (A⁻¹ A') ≤ 2 (q - 1) / s + C` hold for
`ρ ≤ s < r₀`. Then the metric `g (φ u) + du²` has positive scalar curvature. So the bent metric is
`G` reflected in the slice `τ = φ 0` for `u ≤ 0`, and it is the product of `g ρ` with the line for
`u ≥ u₁`. -/
theorem exists_hasPositiveScalarCurvature_compTime (hq : 3 ≤ q) (hR₀ : 0 < R₀) (C : ℝ)
    (hr₀ : 0 < r₀) :
    ∃ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (ρ : ℝ), 0 < ρ ∧ ρ < r₀ ∧ (∀ u, ρ ≤ φ u) ∧ φ 0 < r₀ ∧
      (∀ u ≤ 0, φ u = φ 0 - u) ∧ (∃ u₁, ∀ u, u₁ ≤ u → φ u = ρ) ∧
      ∀ (G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
          (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p))
        (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
        (b : Module.Basis ι ℝ E), (∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p) →
        (∀ y, ∀ s ∈ Ici ρ, R₀ ≤ G.scalarCurvature (y, s)) →
        (∀ y, ∀ s ∈ Ico ρ r₀,
          ((q : ℝ) - 1) * ((q : ℝ) - 2) / s ^ 2 - C / s - C ≤ (g s).scalarCurvature y) →
        (∀ y, ∀ s ∈ Ico ρ r₀, ((of fun i j ↦ (g s).inner y (b i) (b j))⁻¹ *
          of fun i j ↦ deriv (fun s ↦ (g s).inner y (b i) (b j)) s).trace ≤
            2 * ((q : ℝ) - 1) / s + C) →
        (G.compTime hφ).HasPositiveScalarCurvature := by
  obtain ⟨r, h, θ, hγ⟩ := exists_isGromovLawsonBendingCurve_speed_eq_one hq hR₀ (C + R₀) hr₀
  obtain ⟨u₁, ρ, hρ, hρr₀, hu₁⟩ := hγ.exists_radius_eq
  have hρr (u : ℝ) : ρ ≤ r u :=
    (hu₁ _ (le_max_right u u₁)).2 ▸ hγ.antitone_radius (le_max_left u u₁)
  refine ⟨r, hγ.contDiff_radius, ρ, hρ, hρr₀, hρr, hγ.radius_zero_lt,
    fun u hu ↦ hγ.radius_of_nonpos hu, ⟨u₁, fun u hu ↦ (hu₁ u hu).2⟩,
    fun G g b hG hR hg hA ↦ ?_⟩
  exact hγ.hasPositiveScalarCurvature_compTime hG b (fun y u ↦ hR y _ (hρr u))
    (fun y u hu ↦ hg y _ ⟨hρr u, hu⟩) (fun y u hu ↦ hA y _ ⟨hρr u, hu⟩)

end TauCeti
