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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- `ofWithMetric` sends the differential of `diffeomorphWithMetric` back to
`mfderiv I I ofWithMetric`. -/
private theorem mfderiv_ofWithMetric_diffeomorphWithMetric
    (g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (x : WithMetric g) (v : TangentSpace I x) :
    mfderiv I I ofWithMetric (diffeomorphWithMetric g g' ∞ x)
        ((diffeomorphWithMetric g g' ∞).mfderivToContinuousLinearEquiv (by simp) x v) =
      mfderiv I I ofWithMetric x v := by
  rw [mfderiv_ofWithMetric_apply, mfderiv_ofWithMetric_apply]
  exact DFunLike.congr_fun ((Diffeomorph.mfderivToContinuousLinearEquiv_coe _ (by simp)).trans
    (mfderiv_diffeomorphWithMetric g' ∞ x)) v

omit [I.Boundaryless] [T2Space M] in
/-- Tangent norm scaling under `diffeomorphWithMetric` for constant metric rescaling. -/
private theorem norm_mfderiv_diffeomorphWithMetric_rescale_const
    {c : ℝ} (hc : 0 < c) (x : WithMetric g) (v : TangentSpace I x) :
    ‖(diffeomorphWithMetric g (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)
        ∞).mfderivToContinuousLinearEquiv (by simp) x v‖ = √c * ‖v‖ := by
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [mul_pow, Real.sq_sqrt hc.le, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_def, inner_def]
  dsimp only [g_c]
  rw [ContMDiffRiemannianMetric.rescale_inner]
  congr 1
  exact tangent_congr (fun b u ↦ g.inner b u u) (by simp)
    (heq_of_eq (mfderiv_ofWithMetric_diffeomorphWithMetric g g_c x v))

omit [I.Boundaryless] [T2Space M] in
/-- Exponential-domain transport under `diffeomorphWithMetric` for constant metric rescaling. -/
private theorem mfderiv_diffeomorphWithMetric_rescale_const_mem_expDomain
    {c : ℝ} (hc : 0 < c) {x : WithMetric g} {v : TangentSpace I x}
    (hv : v ∈ expDomain I (WithMetric g) x) :
    (diffeomorphWithMetric g (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)
        ∞).mfderivToContinuousLinearEquiv (by simp) x v ∈
      expDomain I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (diffeomorphWithMetric g (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) ∞ x) := by
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  have hmem :
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩;
        mfderiv I I ofWithMetric x v ∈ expDomain I M x.ofWithMetric) := by
    rw [g.expDomain_rescale_const hc x.ofWithMetric]
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
      Bundle.instIsContMDiffRiemannianBundle g
    rw [← mem_expDomain_iff g g.inner_riemannianBundle]
    exact hv
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle g_c
  rw [mem_expDomain_iff g_c g_c.inner_riemannianBundle]
  have h_of : (diffeomorphWithMetric g g_c ∞ x).ofWithMetric = x.ofWithMetric := by simp
  exact (tangent_congr (fun b u ↦ u ∈ expDomain I M b) h_of
    (heq_of_eq (mfderiv_ofWithMetric_diffeomorphWithMetric g g_c x v))).mpr hmem

/-- Exponential equivariance under `diffeomorphWithMetric` for constant metric rescaling. -/
private theorem riemannianExp_mfderiv_diffeomorphWithMetric_rescale_const
    {c : ℝ} (hc : 0 < c) (x : WithMetric g) (v : TangentSpace I x) :
    riemannianExp I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (diffeomorphWithMetric g (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) ∞ x)
        ((diffeomorphWithMetric g (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)
          ∞).mfderivToContinuousLinearEquiv (by simp) x v) =
      diffeomorphWithMetric g (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) ∞
        (riemannianExp I (WithMetric g) x v) := by
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  set Φ := diffeomorphWithMetric g g_c ∞
  refine ofWithMetric_injective ?_
  have hexp_c :
      (riemannianExp I (WithMetric g_c) (Φ x)
          (Φ.mfderivToContinuousLinearEquiv (by simp) x v)).ofWithMetric =
        (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩;
          riemannianExp I M (Φ x).ofWithMetric
            (mfderiv I I ofWithMetric (Φ x)
              (Φ.mfderivToContinuousLinearEquiv (by simp) x v))) :=
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
      Bundle.instIsContMDiffRiemannianBundle g_c
    ofWithMetric_riemannianExp g_c g_c.inner_riemannianBundle (Φ x) _
  have hexp_eq :
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩;
        riemannianExp I M (Φ x).ofWithMetric
          (mfderiv I I ofWithMetric (Φ x)
            (Φ.mfderivToContinuousLinearEquiv (by simp) x v))) =
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
        riemannianExp I M x.ofWithMetric (mfderiv I I ofWithMetric x v)) := by
    trans (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩;
        riemannianExp I M x.ofWithMetric (mfderiv I I ofWithMetric x v))
    · let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g_c.toRiemannianMetric⟩
      exact tangent_congr (fun b u ↦ riemannianExp I M b u) (by simp [Φ])
        (heq_of_eq (mfderiv_ofWithMetric_diffeomorphWithMetric g g_c x v))
    · exact g.riemannianExp_rescale_const hc x.ofWithMetric (mfderiv I I ofWithMetric x v)
  have hexp_g :
      (riemannianExp I (WithMetric g) x v).ofWithMetric =
        (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
          riemannianExp I M x.ofWithMetric (mfderiv I I ofWithMetric x v)) :=
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
      Bundle.instIsContMDiffRiemannianBundle g
    ofWithMetric_riemannianExp g g.inner_riemannianBundle x v
  rw [hexp_c, hexp_eq, ← hexp_g]
  simp [Φ]

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
