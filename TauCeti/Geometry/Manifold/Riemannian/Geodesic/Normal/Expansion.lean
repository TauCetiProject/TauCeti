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
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.Calculus.SecondOrderExpansion

/-!
# Uniform quadratic expansion of the exponential metric

The exponential pullback metric has quadratic term
`-⟪R(w,v)v,z⟫ / 3`. Its remainder is bounded by
`C * ‖v‖³ * ‖w‖ * ‖z‖` on a sufficiently small tangent ball, with one constant
for all input vectors. In particular, for orthonormal `T,Y`,
`‖d exp_(tT)(tY)‖² = t² - K(T,Y) * t⁴ / 3 + O(|t|⁵)`.

The curvature coefficient comes from the Jacobi-field calculation in
`Geodesic.Normal.Jet`. Applying the native second-order Taylor estimate to the
bilinear-form-valued pullback gives uniformity in the two metric inputs.

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

/-- The bilinear-form-valued exponential pullback, used to control both inputs uniformly. -/
private def expMetric (p : M) (v : TangentSpace I p) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let L := mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
  (ContinuousLinearMap.precomp ℝ L).comp ((innerSL ℝ).comp L)

omit [I.Boundaryless] [T2Space M] in
private theorem expMetric_apply (p : M) (v w z : TangentSpace I p) :
    expMetric (I := I) p v w z =
      inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z) := (rfl)

/-- Smoothness as a map to the fixed space of continuous bilinear forms. -/
private theorem contDiffAt_expMetric (p : M) :
    let _ : NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) := inferInstance
    let _ : NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) := inferInstance
    ContDiffAt ℝ ∞ (expMetric (I := I) p) 0 := by
  -- Cache the dual norm to keep nested operator-space synthesis within the default limits.
  let _ : NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  apply contMDiffAt_iff_contDiffAt.mp
  apply contMDiffAt_clm_apply.mpr
  intro w
  apply contMDiffAt_clm_apply.mpr
  intro z
  rw [funext fun v ↦ expMetric_apply p v w z]
  exact contMDiffAt_iff_contDiffAt.mpr
    (((contMDiffOn_riemannianExp (I := I) p).contDiffOn_inner_mfderiv (m := ∞) (by simp)
      (isOpen_expDomain p) w z).contDiffAt
        ((isOpen_expDomain p).mem_nhds (zero_mem_expDomain p)))

/-- Near the origin, the pullback metric is computed by normal coordinate fields. -/
private theorem expMetric_eventuallyEq (p : M) {U : Set (TangentSpace I p)}
    (h : IsNormalDomain I M p U) (w z : TangentSpace I p) :
    (fun v ↦ expMetric (I := I) p v w z) =ᶠ[𝓝 0]
      fun v ↦ inner ℝ (normalCoordinateField I M p U w (riemannianExp I M p v))
        (normalCoordinateField I M p U z (riemannianExp I M p v)) := by
  filter_upwards [h.isOpen.mem_nhds h.zero_mem] with v hv
  rw [expMetric_apply, h.normalCoordinateField_riemannianExp hv,
    h.normalCoordinateField_riemannianExp hv]

/-- The differential of the bilinear-form-valued metric vanishes at the origin. -/
private theorem fderiv_expMetric_zero (p : M) :
    let _ : NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) := inferInstance
    let _ : NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) := inferInstance
    fderiv ℝ (expMetric (I := I) p) 0 = 0 := by
  let _ : NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  have hf := (contDiffAt_expMetric (I := I) p).differentiableAt (by simp)
  ext v w z
  rw [← fderiv_clm_apply_const_apply₂ hf w z v]
  obtain ⟨r, _, h⟩ := exists_isNormalDomain_ball (I := I) p
  rw [(expMetric_eventuallyEq p h w z).fderiv_eq]
  have hcoeff := mdifferentiableAt_inner
    (h.mdifferentiableAt_normalCoordinateField w h.self_mem_image)
    (h.mdifferentiableAt_normalCoordinateField z h.self_mem_image)
  have hc0 : HasMFDerivAt I 𝓘(ℝ)
      (fun q ↦ inner ℝ (normalCoordinateField I M p (Metric.ball 0 r) w q)
        (normalCoordinateField I M p (Metric.ball 0 r) z q)) p 0 := by
    rw [← h.mfderiv_inner_normalCoordinateField_self w z]
    exact hcoeff.hasMFDerivAt
  have hc0' : HasMFDerivAt I 𝓘(ℝ)
      (fun q ↦ inner ℝ (normalCoordinateField I M p (Metric.ball 0 r) w q)
        (normalCoordinateField I M p (Metric.ball 0 r) z q)) (riemannianExp I M p 0) 0 := by
    exact (congrArg (fun q ↦ HasMFDerivAt I 𝓘(ℝ)
      (fun q' ↦ inner ℝ (normalCoordinateField I M p (Metric.ball 0 r) w q')
        (normalCoordinateField I M p (Metric.ball 0 r) z q')) q 0)
      (riemannianExp_zero (I := I) p)).mpr hc0
  have hzero := hc0'.comp (0 : TangentSpace I p) (hasMFDerivAt_riemannianExp_zero (I := I) p)
  have hzF : HasFDerivAt
      ((fun q ↦ inner ℝ (normalCoordinateField I M p (Metric.ball 0 r) w q)
        (normalCoordinateField I M p (Metric.ball 0 r) z q)) ∘ riemannianExp I M p)
      (0 : TangentSpace I p →L[ℝ] ℝ) 0 := by
    convert! hzero.hasFDerivAt using 1
  simpa only [zero_apply, Function.comp_def] using congrArg (fun L ↦ L v) hzF.fderiv

/-- The second differential on a repeated direction is the radial second derivative. -/
private theorem fderiv_fderiv_expMetric_apply_self (p : M) (v w z : TangentSpace I p) :
    let _ : NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) := inferInstance
    let _ : NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) := inferInstance
    fderiv ℝ (fderiv ℝ (expMetric (I := I) p)) 0 v v w z =
      -(2 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z := by
  let _ : NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  dsimp only
  have hf : ContDiffAt ℝ 3 (expMetric (I := I) p) 0 :=
    (contDiffAt_expMetric (I := I) p).of_le (by simp)
  let f := fun u ↦ expMetric (I := I) p u w z
  have hfn : ContDiffAt ℝ 2 f 0 :=
    ((hf.clm_apply contDiffAt_const).clm_apply contDiffAt_const).of_le (by norm_num)
  have hsecond := iteratedDeriv_two_comp (f := f)
    (γ := fun t : ℝ ↦ (0 : TangentSpace I p) + t • v) (t := 0)
    (by simpa using hfn) (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  rw [TauCeti.deriv_const_add_smul, TauCeti.iteratedDeriv_two_const_add_smul] at hsecond
  simp only [zero_add, zero_smul, Pi.zero_apply, map_zero, add_zero] at hsecond
  have heval : (fun u ↦ fderiv ℝ f u v) =ᶠ[𝓝 (0 : TangentSpace I p)]
      (fun u ↦ fderiv ℝ (expMetric (I := I) p) u v w z) := by
    filter_upwards [hf.eventually (by simp)] with u hu
    exact fderiv_clm_apply_const_apply₂ (hu.differentiableAt (by simp)) w z v
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdfv := hdf.clm_apply (differentiableAt_const v)
  have hcalc := congrArg (fun L : TangentSpace I p →L[ℝ] ℝ ↦ L v) (heval.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_clm_apply_const_apply (hfn.hasFDerivAt_fderiv (by norm_num)).differentiableAt v v,
    fderiv_clm_apply_const_apply₂ hdfv w z v,
    fderiv_clm_apply_const_apply hdf v v] at hcalc
  rw [← hcalc, ← hsecond]
  simpa only [f, Function.comp_def, expMetric_apply, iteratedDeriv_succ,
    iteratedDeriv_zero] using deriv_deriv_inner_mfderiv_riemannianExp_zero (I := I) p v w z

/-- Taylor's estimate in operator norm, on a ball in the natural exponential domain. -/
private theorem exists_expMetric_remainder_bound (p : M) :
    let _ : NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) := inferInstance
    let _ : NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) := inferInstance
    ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ expDomain I M p ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r,
        ‖expMetric (I := I) p v - expMetric (I := I) p 0 -
          (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ (expMetric (I := I) p)) 0 v v‖ ≤ C * ‖v‖ ^ 3 := by
  let _ : NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  dsimp only
  have hf : ContDiffAt ℝ 3 (expMetric (I := I) p) 0 :=
    (contDiffAt_expMetric (I := I) p).of_le (by simp)
  have ht := hf.isBigO_sub_taylor_two
  obtain ⟨C, hC, hb⟩ := Asymptotics.isBigO_iff'.mp ht
  simp only [sub_zero, fderiv_expMetric_zero, zero_apply,
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
  let _ : NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  obtain ⟨r, hr, C, hC, hdom, hb⟩ := exists_expMetric_remainder_bound (I := I) p
  refine ⟨r, hr, C, hC, hdom, fun v hv w z ↦ ?_⟩
  let A := expMetric (I := I) p v - expMetric (I := I) p 0 -
    (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ (expMetric (I := I) p)) 0 v v
  have heval : A w z =
      inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z) - inner ℝ w z +
        (1 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z := by
    simp only [A, sub_apply, smul_apply, smul_eq_mul, expMetric_apply,
      mfderiv_riemannianExp_apply_zero, fderiv_fderiv_expMetric_apply_self]
    rw [riemannianExp_zero]
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
