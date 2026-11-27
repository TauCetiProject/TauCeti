/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Scaling
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Exponential
import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Isometry

/-!
# Normal balls under constant rescaling of a metric

Multiplying a smooth Riemannian metric `g` by a positive constant `c` leaves the exponential map
unchanged while scaling tangent norms by `√c`. Consequently, an open tangent ball `Metric.ball 0 r`
is a normal domain at `p` for `c • g` if and only if `Metric.ball 0 (r / √c)` is a normal domain
at `p` for `g`.

## Main results

* `TauCeti.WithMetric.isNormalDomain_ball_rescale_const_iff`: normal tangent balls under constant
  rescaling `g ↦ c g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5.
-/

public section

open Bundle Manifold Metric Set TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.WithMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  [I.Boundaryless] [T2Space M]

/-- Forward implication for normal tangent balls under constant rescaling of `g` by `c > 0`. -/
private theorem isNormalDomain_ball_rescale_const_of_div {c : ℝ} (hc : 0 < c) {p : M} {r : ℝ}
    (h : IsNormalDomain I (WithMetric g) (toWithMetric g p) (Metric.ball 0 (r / √c))) :
    IsNormalDomain I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
      (toWithMetric _ p) (Metric.ball 0 r) := by
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  set p₀ : WithMetric g := toWithMetric g p
  have hsqrt : 0 < √c := Real.sqrt_pos.2 hc
  let Φ : WithMetric g ≃ₘ^∞⟮I, I⟯ WithMetric g_c := diffeomorphWithMetric g g_c ∞
  have hΦ : Φ p₀ = toWithMetric g_c p := by simp [Φ, p₀]
  let L : TangentSpace I p₀ ≃L[ℝ] TangentSpace I (Φ p₀) :=
    Φ.mfderivToContinuousLinearEquiv (by simp) p₀
  have hball : L '' Metric.ball 0 (r / √c) = Metric.ball (0 : TangentSpace I (Φ p₀)) r := by
    ext w
    simp only [mem_image, mem_ball_zero_iff]
    refine ⟨?_, fun hw ↦ ⟨L.symm w, ?_, L.apply_symm_apply w⟩⟩
    · rintro ⟨v, hv, rfl⟩
      rw [norm_mfderiv_diffeomorphWithMetric_rescale_const g hc p₀ v]
      exact (lt_div_iff₀' hsqrt).1 hv
    · have hnorm_symm : ‖L.symm w‖ = ‖w‖ / √c := by
        rw [eq_div_iff hsqrt.ne', mul_comm, ← norm_mfderiv_diffeomorphWithMetric_rescale_const g hc,
          L.apply_symm_apply]
      rw [hnorm_symm]
      exact div_lt_div_of_pos_right hw hsqrt
  exact hΦ ▸ hball ▸ h.image_of_diffeomorph Φ L
    (fun _ hv ↦
      mfderiv_diffeomorphWithMetric_rescale_const_mem_expDomain g hc (h.subset_expDomain hv))
    (fun v _ ↦ riemannianExp_mfderiv_diffeomorphWithMetric_rescale_const g hc p₀ v)

/-- **Normal tangent balls under constant metric rescaling.** Multiplying `g` by `c > 0` scales the
radius of normal tangent balls by `√c`. -/
theorem isNormalDomain_ball_rescale_const_iff {c : ℝ} (hc : 0 < c) (p : M) (r : ℝ) :
    IsNormalDomain I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (toWithMetric _ p) (Metric.ball 0 r) ↔
      IsNormalDomain I (WithMetric g) (toWithMetric g p) (Metric.ball 0 (r / √c)) := by
  refine ⟨fun h ↦ ?_, isNormalDomain_ball_rescale_const_of_div g hc⟩
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  set g' := g_c.rescale (fun _ ↦ c⁻¹) contMDiff_const fun _ ↦ inv_pos.2 hc
  have hr_eq : (r / √c) / √c⁻¹ = r := by
    rw [Real.sqrt_inv, div_inv_eq_mul, div_mul_cancel₀ _ (Real.sqrt_pos.2 hc).ne']
  let Ψ := riemannianIsometryOfInnerEq g' g fun x v w ↦ by simp [g', g_c, inv_mul_cancel₀ hc.ne']
  exact (riemannianIsometryOfInnerEq_apply g' g _ (toWithMetric g' p) : Ψ _ = _) ▸
    (Ψ.isNormalDomain_ball_iff (toWithMetric g' p) (r / √c)).2
      (isNormalDomain_ball_rescale_const_of_div g_c (inv_pos.2 hc) (hr_eq.symm ▸ h))

end TauCeti.WithMetric

end
