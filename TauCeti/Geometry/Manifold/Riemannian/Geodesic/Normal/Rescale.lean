/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Scaling
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Rescale
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
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

private theorem tangent_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {α : Sort*} (F : ∀ b : M, TangentSpace I b → α)
    {b₁ b₂ : M} (hb : b₁ = b₂) {u₁ : TangentSpace I b₁} {u₂ : TangentSpace I b₂}
    (hu : HEq u₁ u₂) : F b₁ u₁ = F b₂ u₂ := by
  cases hb; cases eq_of_heq hu; rfl

/-- Forward implication for normal tangent balls under constant rescaling of `g` by `c > 0`. -/
private theorem isNormalDomain_ball_rescale_const_of_div {c : ℝ} (hc : 0 < c) {p : M} {r : ℝ}
    (h : IsNormalDomain I (WithMetric g) (toWithMetric g p) (Metric.ball 0 (r / √c))) :
    IsNormalDomain I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
      (toWithMetric _ p) (Metric.ball 0 r) := by
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  set p₀ : WithMetric g := toWithMetric g p
  set p_c : WithMetric g_c := toWithMetric g_c p
  have hsqrt : 0 < √c := Real.sqrt_pos.2 hc
  let Φ : WithMetric g ≃ₘ^∞⟮I, I⟯ WithMetric g_c := diffeomorphWithMetric g g_c ∞
  have hΦ : Φ p₀ = p_c := by simp [Φ, p₀, p_c]
  let L : TangentSpace I p₀ ≃L[ℝ] TangentSpace I (Φ p₀) :=
    Φ.mfderivToContinuousLinearEquiv (by simp) p₀
  have hΦ_of : (Φ p₀).ofWithMetric = p₀.ofWithMetric := by simp [Φ, p₀]
  have hL_of (v : TangentSpace I p₀) :
      mfderiv I I ofWithMetric (Φ p₀) (L v) = mfderiv I I ofWithMetric p₀ v := by
    rw [hΦ, mfderiv_ofWithMetric_apply, mfderiv_ofWithMetric_apply]
    exact DFunLike.congr_fun ((Diffeomorph.mfderivToContinuousLinearEquiv_coe _ (by simp)).trans
      (mfderiv_diffeomorphWithMetric g_c ∞ p₀)) v
  have hnorm (v : TangentSpace I p₀) : ‖L v‖ = √c * ‖v‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 <| by
      rw [mul_pow, Real.sq_sqrt hc.le, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, inner_def, inner_def]
      dsimp only [g_c]
      rw [ContMDiffRiemannianMetric.rescale_inner]
      congr 1
      exact tangent_congr (fun b u ↦ g.inner b u u) hΦ_of (heq_of_eq (hL_of v))
  have hball : L '' Metric.ball 0 (r / √c) = Metric.ball (0 : TangentSpace I (Φ p₀)) r := by
    ext w
    simp only [mem_image, mem_ball_zero_iff]
    refine ⟨?_, fun hw ↦ ⟨L.symm w, ?_, L.apply_symm_apply w⟩⟩
    · rintro ⟨v, hv, rfl⟩
      rw [hnorm]
      exact (lt_div_iff₀' hsqrt).1 hv
    · have hnorm_symm : ‖L.symm w‖ = ‖w‖ / √c := by
        rw [eq_div_iff hsqrt.ne', mul_comm, ← hnorm, L.apply_symm_apply]
      rw [hnorm_symm]
      exact div_lt_div_of_pos_right hw hsqrt
  have hdom : MapsTo L (Metric.ball 0 (r / √c)) (expDomain I (WithMetric g_c) (Φ p₀)) := by
    intro v hv
    have hmem :
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩;
          mfderiv I I ofWithMetric p₀ v ∈ expDomain I M p₀.ofWithMetric) := by
      rw [g.expDomain_rescale_const hc p₀.ofWithMetric]
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g
      rw [← mem_expDomain_iff g g.inner_riemannianBundle]
      exact h.subset_expDomain hv
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
      Bundle.instIsContMDiffRiemannianBundle g_c
    rw [mem_expDomain_iff g_c g_c.inner_riemannianBundle]
    exact (tangent_congr (fun b u ↦ u ∈ expDomain I M b) hΦ_of (heq_of_eq (hL_of v))).mpr hmem
  have hexp (v : TangentSpace I p₀) (_ : v ∈ Metric.ball 0 (r / √c)) :
      riemannianExp I (WithMetric g_c) (Φ p₀) (L v) = Φ (riemannianExp I (WithMetric g) p₀ v) := by
    refine ofWithMetric_injective ?_
    have hexp_c :
        (riemannianExp I (WithMetric g_c) (Φ p₀) (L v)).ofWithMetric =
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩;
            riemannianExp I M (Φ p₀).ofWithMetric (mfderiv I I ofWithMetric (Φ p₀) (L v))) :=
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g_c
      ofWithMetric_riemannianExp g_c g_c.inner_riemannianBundle (Φ p₀) (L v)
    have hexp_eq :
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩;
          riemannianExp I M (Φ p₀).ofWithMetric (mfderiv I I ofWithMetric (Φ p₀) (L v))) =
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          riemannianExp I M p₀.ofWithMetric (mfderiv I I ofWithMetric p₀ v)) := by
      trans (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩;
          riemannianExp I M p₀.ofWithMetric (mfderiv I I ofWithMetric p₀ v))
      · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩
        exact tangent_congr (fun b u ↦ riemannianExp I M b u) hΦ_of (heq_of_eq (hL_of v))
      · exact g.riemannianExp_rescale_const hc p₀.ofWithMetric (mfderiv I I ofWithMetric p₀ v)
    have hexp_g :
        (riemannianExp I (WithMetric g) p₀ v).ofWithMetric =
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
            riemannianExp I M p₀.ofWithMetric (mfderiv I I ofWithMetric p₀ v)) :=
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g
      ofWithMetric_riemannianExp g g.inner_riemannianBundle p₀ v
    rw [hexp_c, hexp_eq, ← hexp_g]
    simp [Φ]
  exact hΦ ▸ hball ▸ h.image_of_diffeomorph Φ L hdom hexp

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
