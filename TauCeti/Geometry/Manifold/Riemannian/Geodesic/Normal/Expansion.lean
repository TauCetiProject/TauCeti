/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Jet
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Calculus.SecondOrderExpansion
import TauCeti.Analysis.Calculus.TaylorIntegral

/-!
# Uniform quadratic expansion of the exponential metric

The exponential pullback metric has quadratic term
`-⟪R(w,v)v,z⟫ / 3`. Its remainder is bounded by
`C * ‖v‖³ * ‖w‖ * ‖z‖` on a sufficiently small tangent ball, with one constant
for all input vectors. In particular, for orthonormal `T,Y`,
`‖d exp_(tT)(tY)‖² = t² - K(T,Y) * t⁴ / 3 + O(|t|⁵)`.

The curvature coefficient comes from the Jacobi-field calculation in
`Geodesic.Normal.Jet`. Applying the native second-order Taylor estimate to the
bilinear-form-valued pullback `riemannianExpPullbackMetric` gives uniformity in the two metric
inputs. Its value and smoothness at the origin, the vanishing of its first derivative there, and its
second derivative on a repeated direction are recorded as public lemmas.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 5 and 10
  (normal coordinates and Jacobi fields).
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The dual norm on a tangent space, cached: nested operator-space synthesis otherwise exceeds
the default instance-search limits. -/
local instance instNormedAddCommGroupTangentSpaceDual (p : M) :
    NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) :=
  inferInstance

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The dual normed-space structure on a tangent space, cached alongside its norm. -/
local instance instNormedSpaceTangentSpaceDual (p : M) :
    NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) :=
  inferInstance

variable (I M) in
/-- The exponential pullback metric at `p`, as a map from `T_pM` to the fixed space of continuous
bilinear forms on `T_pM`: `v` is sent to `(w, z) ↦ ⟪d exp_p(v) w, d exp_p(v) z⟫`. -/
def riemannianExpPullbackMetric (p : M) (v : TangentSpace I p) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let L := mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
  (innerSL ℝ).bilinearComp L L

omit [I.Boundaryless] [T2Space M] in
/-- Evaluating the exponential pullback metric on two vectors. -/
@[simp]
theorem riemannianExpPullbackMetric_apply (p : M) (v w z : TangentSpace I p) :
    riemannianExpPullbackMetric I M p v w z =
      inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z) := (rfl)

/-- At the origin, the exponential pullback metric is the metric of `T_pM`. -/
@[simp]
theorem riemannianExpPullbackMetric_zero (p : M) :
    riemannianExpPullbackMetric I M p 0 = innerSL ℝ := by
  ext w z
  simp only [riemannianExpPullbackMetric_apply, mfderiv_riemannianExp_apply_zero]
  rw [riemannianExp_zero, innerSL_apply_apply]

/-- The exponential pullback metric is smooth at the origin, as a map to the fixed space of
continuous bilinear forms. -/
theorem contDiffAt_riemannianExpPullbackMetric (p : M) :
    ContDiffAt ℝ ∞ (riemannianExpPullbackMetric I M p) 0 := by
  apply contMDiffAt_iff_contDiffAt.mp
  apply contMDiffAt_clm_apply.mpr
  intro w
  apply contMDiffAt_clm_apply.mpr
  intro z
  rw [funext fun v ↦ riemannianExpPullbackMetric_apply p v w z]
  exact contMDiffAt_iff_contDiffAt.mpr
    (((contMDiffOn_riemannianExp (I := I) p).contDiffOn_inner_mfderiv (m := ∞) (by simp)
      (isOpen_expDomain p) w z).contDiffAt
        ((isOpen_expDomain p).mem_nhds (zero_mem_expDomain p)))

/-- Near the origin, the pullback metric is computed by normal coordinate fields. -/
private theorem riemannianExpPullbackMetric_eventuallyEq (p : M) {U : Set (TangentSpace I p)}
    (h : IsNormalDomain I M p U) (w z : TangentSpace I p) :
    (fun v ↦ riemannianExpPullbackMetric I M p v w z) =ᶠ[𝓝 0]
      fun v ↦ inner ℝ (normalCoordinateField I M p U w (riemannianExp I M p v))
        (normalCoordinateField I M p U z (riemannianExp I M p v)) := by
  filter_upwards [h.isOpen.mem_nhds h.zero_mem] with v hv
  rw [riemannianExpPullbackMetric_apply, h.normalCoordinateField_riemannianExp hv,
    h.normalCoordinateField_riemannianExp hv]

/-- The first derivative of the exponential pullback metric vanishes at the origin. -/
@[simp]
theorem fderiv_riemannianExpPullbackMetric_zero (p : M) :
    fderiv ℝ (riemannianExpPullbackMetric I M p) 0 = 0 := by
  have hf := (contDiffAt_riemannianExpPullbackMetric (I := I) p).differentiableAt (by simp)
  ext v w z
  rw [← fderiv_clm_apply_const_apply₂ hf w z v]
  obtain ⟨r, _, h⟩ := exists_isNormalDomain_ball (I := I) p
  rw [(riemannianExpPullbackMetric_eventuallyEq p h w z).fderiv_eq]
  have hc0 : HasMFDerivAt I 𝓘(ℝ)
      (fun q ↦ inner ℝ (normalCoordinateField I M p (Metric.ball 0 r) w q)
        (normalCoordinateField I M p (Metric.ball 0 r) z q)) (riemannianExp I M p 0) 0 := by
    rw [riemannianExp_zero, ← h.mfderiv_inner_normalCoordinateField_self w z]
    exact (mdifferentiableAt_inner
      (h.mdifferentiableAt_normalCoordinateField w h.self_mem_image)
      (h.mdifferentiableAt_normalCoordinateField z h.self_mem_image)).hasMFDerivAt
  have hzero := hc0.comp (0 : TangentSpace I p) (hasMFDerivAt_riemannianExp_zero (I := I) p)
  have hzF : HasFDerivAt
      ((fun q ↦ inner ℝ (normalCoordinateField I M p (Metric.ball 0 r) w q)
        (normalCoordinateField I M p (Metric.ball 0 r) z q)) ∘ riemannianExp I M p)
      (0 : TangentSpace I p →L[ℝ] ℝ) 0 := by
    -- The chain rule gives the derivative `0 ∘L NormedSpace.fromTangentSpace 0`, typed with the
    -- tangent spaces of the models `𝓘(ℝ, TangentSpace I p)` and `𝓘(ℝ)`; `convert!` unfolds
    -- these to `TangentSpace I p` and `ℝ` and identifies the composite with the zero map.
    convert! hzero.hasFDerivAt using 1
  simpa only [zero_apply, Function.comp_def] using congrArg (fun L ↦ L v) hzF.fderiv

/-- The second derivative of the exponential pullback metric at the origin, on a repeated
direction `v`, is `-(2/3) ⟪R(w,v)v,z⟫`. -/
theorem fderiv_fderiv_riemannianExpPullbackMetric_apply_self (p : M) (v w z : TangentSpace I p) :
    fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p)) 0 v v w z =
      -(2 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z := by
  have hf : ContDiffAt ℝ 3 (riemannianExpPullbackMetric I M p) 0 :=
    (contDiffAt_riemannianExpPullbackMetric (I := I) p).of_le (by simp)
  let f := fun u ↦ riemannianExpPullbackMetric I M p u w z
  have hfn : ContDiffAt ℝ 2 f 0 :=
    ((hf.clm_apply contDiffAt_const).clm_apply contDiffAt_const).of_le (by norm_num)
  -- Restrict `f` to the line `s ↦ s • v` through the origin.
  have hline := ContDiffAt.deriv_deriv_comp_add_smul (f := f) (x := 0) (t := (0 : ℝ)) (y := v)
    (by simpa using hfn)
  simp only [zero_add, zero_smul] at hline
  rw [← fderiv_fderiv_clm_apply_const_apply₂
    (hf.eventually (by simp) |>.mono fun u hu ↦ hu.differentiableAt (by simp))
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) w z v v, ← hline]
  simpa only [f, riemannianExpPullbackMetric_apply] using
    deriv_deriv_inner_mfderiv_riemannianExp_zero (I := I) p v w z

/-- Taylor's estimate in operator norm, on a ball in the natural exponential domain. -/
private theorem exists_riemannianExpPullbackMetric_remainder_bound (p : M) :
    ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ expDomain I M p ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r,
        ‖riemannianExpPullbackMetric I M p v - riemannianExpPullbackMetric I M p 0 -
          (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p)) 0 v v‖ ≤
            C * ‖v‖ ^ 3 := by
  have hf : ContDiffAt ℝ 3 (riemannianExpPullbackMetric I M p) 0 :=
    (contDiffAt_riemannianExpPullbackMetric (I := I) p).of_le (by simp)
  have ht := hf.isBigO_sub_taylor_two
  obtain ⟨C, hC, hb⟩ := Asymptotics.isBigO_iff'.mp ht
  simp only [sub_zero, fderiv_riemannianExpPullbackMetric_zero, zero_apply,
    Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 3)] at hb
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hb.and ((isOpen_expDomain (I := I) p).mem_nhds (zero_mem_expDomain p)))
  exact ⟨r, hr, C, hC, fun v hv ↦ (hball v hv).2, fun v hv ↦ (hball v hv).1⟩

/-- **Uniform quadratic expansion of the exponential metric.** The error is bounded by
`C ‖v‖³ ‖w‖ ‖z‖` on one tangent ball, independently of `w` and `z`. The ball lies in the
natural exponential domain; no completeness assumption is needed. -/
theorem exists_abs_inner_mfderiv_riemannianExp_sub_le (p : M) :
    ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ expDomain I M p ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w z : TangentSpace I p,
        |inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z) - inner ℝ w z +
          (1 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z| ≤
            C * ‖v‖ ^ 3 * ‖w‖ * ‖z‖ := by
  obtain ⟨r, hr, C, hC, hdom, hb⟩ := exists_riemannianExpPullbackMetric_remainder_bound (I := I) p
  refine ⟨r, hr, C, hC, hdom, fun v hv w z ↦ ?_⟩
  let A := riemannianExpPullbackMetric I M p v - riemannianExpPullbackMetric I M p 0 -
    (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p)) 0 v v
  have heval : A w z =
      inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z) - inner ℝ w z +
        (1 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z := by
    simp only [A, sub_apply, smul_apply, smul_eq_mul, riemannianExpPullbackMetric_zero,
      riemannianExpPullbackMetric_apply, fderiv_fderiv_riemannianExpPullbackMetric_apply_self]
    rw [innerSL_apply_apply]
    ring
  rw [← heval, ← Real.norm_eq_abs]
  exact (A.le_opNorm₂ w z).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hb v hv) (norm_nonneg w)) (norm_nonneg z))

/-- **The angular squared-length expansion.** One radius and one error constant work for
all orthonormal pairs at `p`, for positive and negative times. The curvature term has the
sign for which the unit round sphere has positive sectional curvature. -/
theorem exists_abs_norm_sq_mfderiv_riemannianExp_sub_le (p : M) :
    ∃ r > 0, ∃ C > 0, ∀ T Y : TangentSpace I p, Orthonormal ℝ ![T, Y] →
      ∀ t : ℝ, |t| < r → t • T ∈ expDomain I M p ∧
        |‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • T) (t • Y)‖ ^ 2 -
            t ^ 2 + (1 / 3 : ℝ) * (leviCivitaConnection I M).sectionalCurvature
              (isMetricCompatible_leviCivitaConnection I) p T Y * t ^ 4| ≤ C * |t| ^ 5 := by
  obtain ⟨r, hr, C, hC, hdom, hb⟩ := exists_abs_inner_mfderiv_riemannianExp_sub_le (I := I) p
  refine ⟨r, hr, C, hC, fun T Y h t ht ↦ ?_⟩
  have hT : ‖T‖ = 1 := h.norm_eq_one 0
  have hY : ‖Y‖ = 1 := h.norm_eq_one 1
  have hv : t • T ∈ Metric.ball (0 : TangentSpace I p) r := by
    simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, hT, mul_one] using ht
  refine ⟨hdom hv, ?_⟩
  have he := hb (t • T) hv (t • Y) (t • Y)
  have hK : inner ℝ ((leviCivitaConnection I M).curvatureTensor p Y T T) Y =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) p T Y := by
    rw [(isMetricCompatible_leviCivitaConnection I).inner_curvatureTensor_swap_pairs
      (torsion_leviCivitaConnection_eq_zero I) p Y T T Y]
    exact (sectionalCurvature_eq_of_orthonormal _ _ p T Y h).symm
  simp only [LinearMap.map_smul, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    hT, hY, mul_one, one_pow, hK] at he
  convert he using 1 <;> ring_nf

end TauCeti.Manifold
