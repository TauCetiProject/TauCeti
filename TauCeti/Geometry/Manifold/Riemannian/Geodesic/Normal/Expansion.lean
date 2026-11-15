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
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Calculus.SecondOrderExpansion
import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.LinearAlgebra.Multilinear.Polarization

/-!
# Uniform quadratic and cubic expansions of the exponential metric

The exponential pullback metric at `p` has Taylor expansion
`⟪w, z⟫ - ⅓ ⟪R(w, v)v, z⟫ - ⅙ ⟪(∇_v R)(w, v)v, z⟫` at the origin, with quadratic remainder bounded
by `C * ‖v‖³ * ‖w‖ * ‖z‖` and cubic remainder bounded by `C * ‖v‖⁴ * ‖w‖ * ‖z‖` on a sufficiently
small tangent ball, using one constant for all input vectors and requiring no completeness
assumption. On any normal domain `U`, both expansions transfer to the normal-coordinate metric
coefficients `⟪X_w(exp_p v), X_z(exp_p v)⟫` and to orthonormal frames, and for orthonormal `T, Y`
they yield the angular squared-length expansions
`‖d exp_p(t T)(t Y)‖² = t² - ⅓ K(T, Y) t⁴ + O(|t|⁵)` and
`t² - ⅓ K(T, Y) t⁴ - ⅙ ⟪(∇_T R)(Y, T)T, Y⟫ t⁵ + O(|t|⁶)`. When `(∇R)_p = 0` (for example on a
locally symmetric space), the cubic term vanishes and the quadratic expansion is already accurate
to `O(‖v‖⁴)`.

The curvature and curvature-derivative coefficients come from the Jacobi-field jet calculations in
`Geodesic.Normal.Jet`. Applying the completeness-free multivariate Taylor estimates to the
bilinear-form-valued pullback `riemannianExpPullbackMetric` gives uniformity in the two metric
inputs; polarizing its second and third derivatives gives `D²(exp_p^* g)_0` and `D³(exp_p^* g)_0`
on arbitrary directions.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018, Chapters 5,
  7, and 10 (normal coordinates, curvature symmetries, and Jacobi fields).
* L. Brewin, *Riemann normal coordinate expansions using Cadabra*, Classical and Quantum Gravity
  26 (2009), 175017, §5 and eq. (11.1) (cubic normal-coordinate metric expansion).
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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The operator norm on continuous bilinear forms on a tangent space, cached so third Fréchet
derivatives of `riemannianExpPullbackMetric` elaborate within default instance-search limits. -/
local instance instNormedAddCommGroupTangentSpaceBilin (p : M) :
    NormedAddCommGroup (TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) :=
  inferInstance

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The normed-space structure on continuous bilinear forms on a tangent space, cached alongside
its norm. -/
local instance instNormedSpaceTangentSpaceBilin (p : M) :
    NormedSpace ℝ (TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) :=
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

/-- The first derivative of the exponential pullback metric vanishes at the origin. -/
@[simp]
theorem fderiv_riemannianExpPullbackMetric_zero (p : M) :
    fderiv ℝ (riemannianExpPullbackMetric I M p) 0 = 0 := by
  have hf := (contDiffAt_riemannianExpPullbackMetric (I := I) p).differentiableAt (by simp)
  ext v w z
  rw [← fderiv_clm_apply_const_apply₂ hf w z v]
  obtain ⟨r, _, h⟩ := exists_isNormalDomain_ball (I := I) p
  rw [funext fun u ↦ riemannianExpPullbackMetric_apply p u w z,
    (h.eventuallyEq_inner_mfderiv_riemannianExp w z).fderiv_eq]
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

/-- **Polarized second derivative of the exponential pullback metric at the origin.** Evaluating
`D²(exp_p^* g)_0` on two directions `u₁, u₂` gives `-⅓ (⟪R(w, u₁)u₂, z⟫ + ⟪R(w, u₂)u₁, z⟫)`. -/
theorem fderiv_fderiv_riemannianExpPullbackMetric_zero_apply
    (p : M) (u₁ u₂ w z : TangentSpace I p) :
    fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p)) 0 u₁ u₂ w z =
      -(1 / 3 : ℝ) *
        (inner ℝ ((leviCivitaConnection I M).curvatureTensor p w u₁ u₂) z +
          inner ℝ ((leviCivitaConnection I M).curvatureTensor p w u₂ u₁) z) := by
  have hself := fderiv_fderiv_riemannianExpPullbackMetric_apply_self (I := I) p (u₁ + u₂) w z
  have hsymm : fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p)) 0 u₂ u₁ w z =
      fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p)) 0 u₁ u₂ w z :=
    congrArg (fun L ↦ L w z)
      ((contDiffAt_riemannianExpPullbackMetric (I := I) p).isSymmSndFDerivAt (by simp) u₂ u₁)
  simp only [map_add, add_apply, LinearMap.add_apply, inner_add_left,
    fderiv_fderiv_riemannianExpPullbackMetric_apply_self, hsymm] at hself
  linarith

/-- An operator-norm `O(‖v‖ ^ k)` approximation `P` to `riemannianExpPullbackMetric` at `0` yields a
uniform pointwise bound on a tangent ball inside `expDomain`. -/
private theorem exists_ball_abs_inner_mfderiv_riemannianExp_sub_le_of_isBigO (p : M)
    (P : TangentSpace I p → TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) (k : ℕ)
    (hP : (fun v ↦ riemannianExpPullbackMetric I M p v - P v) =O[𝓝 0] fun v ↦ ‖v‖ ^ k) :
    ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ expDomain I M p ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w z : TangentSpace I p,
        |inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z) - P v w z| ≤
            C * ‖v‖ ^ k * ‖w‖ * ‖z‖ := by
  obtain ⟨C, hC, hb⟩ := Asymptotics.isBigO_iff'.mp hP
  simp only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) k)] at hb
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hb.and ((isOpen_expDomain (I := I) p).mem_nhds (zero_mem_expDomain p)))
  refine ⟨r, hr, C, hC, fun v hv ↦ (hball v hv).2, fun v hv w z ↦ ?_⟩
  rw [← riemannianExpPullbackMetric_apply, ← sub_apply, ← sub_apply, ← Real.norm_eq_abs]
  exact ((riemannianExpPullbackMetric I M p v - P v).le_opNorm₂ w z).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hball v hv).1 (norm_nonneg w)) (norm_nonneg z))

omit [I.Boundaryless] in
/-- Transfers a uniform ball bound on `⟪d exp_p(v) w, d exp_p(v) z⟫` to normal coordinate vector
fields on a smaller ball inside `U`. -/
private theorem exists_abs_inner_normalCoordinateField_of_expDomain_bound
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U) (k : ℕ)
    (Q : TangentSpace I p → TangentSpace I p → TangentSpace I p → ℝ)
    (hb : ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ expDomain I M p ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w z : TangentSpace I p,
        |inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z) - inner ℝ w z +
          (1 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z +
          Q v w z| ≤ C * ‖v‖ ^ k * ‖w‖ * ‖z‖) :
    ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ U ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w z : TangentSpace I p,
        |inner ℝ (normalCoordinateField I M p U w (riemannianExp I M p v))
            (normalCoordinateField I M p U z (riemannianExp I M p v)) - inner ℝ w z +
          (1 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z +
          Q v w z| ≤ C * ‖v‖ ^ k * ‖w‖ * ‖z‖ := by
  obtain ⟨r₁, hr₁, C, hC, _, hb⟩ := hb
  obtain ⟨r₂, hr₂, hU⟩ := Metric.isOpen_iff.mp h.isOpen 0 h.zero_mem
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, C, hC,
    (Metric.ball_subset_ball (min_le_right r₁ r₂)).trans hU, fun v hv w z ↦ ?_⟩
  have hvU : v ∈ U := hU (Metric.ball_subset_ball (min_le_right r₁ r₂) hv)
  rw [h.normalCoordinateField_riemannianExp hvU, h.normalCoordinateField_riemannianExp hvU]
  exact hb v (Metric.ball_subset_ball (min_le_left r₁ r₂) hv) w z

omit [I.Boundaryless] in
/-- Specializes a uniform ball bound on `⟪d exp_p(v) w, d exp_p(v) z⟫` (with an optional
higher-order correction `Q v w z`) to `(v, w, z) = (t • T, t • Y, t • Y)` for an orthonormal pair
`T, Y`. -/
private theorem exists_abs_norm_sq_mfderiv_riemannianExp_of_ball_bound (p : M) (k : ℕ)
    (Q : TangentSpace I p → TangentSpace I p → TangentSpace I p → ℝ)
    (hb : ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ expDomain I M p ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w z : TangentSpace I p,
        |inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z) - inner ℝ w z +
          (1 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z +
          Q v w z| ≤ C * ‖v‖ ^ k * ‖w‖ * ‖z‖) :
    ∃ r > 0, ∃ C > 0, ∀ T Y : TangentSpace I p, Orthonormal ℝ ![T, Y] →
      ∀ t : ℝ, |t| < r → t • T ∈ expDomain I M p ∧
        |‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • T) (t • Y)‖ ^ 2 -
            t ^ 2 + (1 / 3 : ℝ) * (leviCivitaConnection I M).sectionalCurvature
              (isMetricCompatible_leviCivitaConnection I) p T Y * t ^ 4 +
            Q (t • T) (t • Y) (t • Y)| ≤ C * |t| ^ (k + 2) := by
  obtain ⟨r, hr, C, hC, hdom, hb⟩ := hb
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
    hT, hY, mul_one, hK] at he
  convert he using 1
  · congr 1
    ring
  · rw [pow_succ, pow_succ]
    ring

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
  have hf : ContDiffAt ℝ 3 (riemannianExpPullbackMetric I M p) 0 :=
    (contDiffAt_riemannianExpPullbackMetric (I := I) p).of_le (by simp)
  obtain ⟨r, hr, C, hC, hdom, hb⟩ := exists_ball_abs_inner_mfderiv_riemannianExp_sub_le_of_isBigO p
    (fun v ↦ riemannianExpPullbackMetric I M p 0 +
      (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p)) 0 v v) 3
    (by simpa only [sub_zero, fderiv_riemannianExpPullbackMetric_zero, zero_apply,
      sub_add_eq_sub_sub] using hf.isBigO_sub_taylor_two)
  refine ⟨r, hr, C, hC, hdom, fun v hv w z ↦ ?_⟩
  convert hb v hv w z using 2
  simp only [add_apply, smul_apply, smul_eq_mul, riemannianExpPullbackMetric_zero,
    fderiv_fderiv_riemannianExpPullbackMetric_apply_self]
  rw [innerSL_apply_apply]
  ring

namespace IsNormalDomain

/-- **Uniform quadratic expansion of normal-coordinate metric coefficients.** On a small tangent
ball inside any normal domain `U`, `⟪X_w(exp_p v), X_z(exp_p v)⟫` equals
`⟪w, z⟫ - ⅓ ⟪R(w, v)v, z⟫` up to `C ‖v‖³ ‖w‖ ‖z‖`. -/
theorem exists_abs_inner_normalCoordinateField_sub_le
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U) :
    ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ U ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w z : TangentSpace I p,
        |inner ℝ (normalCoordinateField I M p U w (riemannianExp I M p v))
            (normalCoordinateField I M p U z (riemannianExp I M p v)) - inner ℝ w z +
          (1 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z| ≤
            C * ‖v‖ ^ 3 * ‖w‖ * ‖z‖ := by
  simpa only [add_zero] using exists_abs_inner_normalCoordinateField_of_expDomain_bound h 3
    (fun _ _ _ ↦ 0)
    (by simpa only [add_zero] using exists_abs_inner_mfderiv_riemannianExp_sub_le (I := I) p)

/-- **Coordinate form of the quadratic normal-coordinate metric expansion.** On a small tangent
ball inside any normal domain `U`, the metric coefficients of any orthonormal family `(e_i)`
satisfy `g_{ij}(exp_p v) = δ_{ij} - ⅓ ⟪R(e_i, v)v, e_j⟫ + O(‖v‖³)`, with one radius and one
constant independent of the orthonormal family and indices. -/
theorem exists_abs_inner_normalCoordinateField_orthonormal_sub_le
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    (ι : Type*) [DecidableEq ι] :
    ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ U ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r,
        ∀ {e : ι → TangentSpace I p}, Orthonormal ℝ e → ∀ i j : ι,
          |inner ℝ (normalCoordinateField I M p U (e i) (riemannianExp I M p v))
              (normalCoordinateField I M p U (e j) (riemannianExp I M p v)) -
            (if i = j then 1 else 0) +
            (1 / 3 : ℝ) *
              inner ℝ ((leviCivitaConnection I M).curvatureTensor p (e i) v v) (e j)| ≤
              C * ‖v‖ ^ 3 := by
  obtain ⟨r, hr, C, hC, hU, hb⟩ := h.exists_abs_inner_normalCoordinateField_sub_le
  refine ⟨r, hr, C, hC, hU, fun v hv {e} he i j ↦ ?_⟩
  simpa only [orthonormal_iff_ite.mp he i j, he.norm_eq_one, mul_one] using hb v hv (e i) (e j)

end IsNormalDomain

/-- **The angular squared-length expansion.** One radius and one error constant work for
all orthonormal pairs at `p`, for positive and negative times. The curvature term has the
sign for which the unit round sphere has positive sectional curvature. -/
theorem exists_abs_norm_sq_mfderiv_riemannianExp_sub_le (p : M) :
    ∃ r > 0, ∃ C > 0, ∀ T Y : TangentSpace I p, Orthonormal ℝ ![T, Y] →
      ∀ t : ℝ, |t| < r → t • T ∈ expDomain I M p ∧
        |‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • T) (t • Y)‖ ^ 2 -
            t ^ 2 + (1 / 3 : ℝ) * (leviCivitaConnection I M).sectionalCurvature
              (isMetricCompatible_leviCivitaConnection I) p T Y * t ^ 4| ≤ C * |t| ^ 5 := by
  simpa only [add_zero] using exists_abs_norm_sq_mfderiv_riemannianExp_of_ball_bound p 3
    (fun _ _ _ ↦ 0)
    (by simpa only [add_zero] using exists_abs_inner_mfderiv_riemannianExp_sub_le (I := I) p)

/-- The third derivative of the exponential pullback metric at the origin, on a repeated
direction `v`, is `-⟪(∇_v R)(w,v)v,z⟫`. -/
theorem fderiv_fderiv_fderiv_riemannianExpPullbackMetric_apply_self
    (p : M) (v w z : TangentSpace I p) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p))) 0 v v v w z =
      -inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
        (leviCivitaConnection I M) p v w v v) z := by
  have hf : ContDiffAt ℝ 3 (riemannianExpPullbackMetric I M p) 0 :=
    (contDiffAt_riemannianExpPullbackMetric (I := I) p).of_le (by simp)
  let L := (ContinuousLinearMap.apply ℝ ℝ z).comp
    (ContinuousLinearMap.apply ℝ (TangentSpace I p →L[ℝ] ℝ) w)
  have hcomp := congrArg (fun M ↦ M (fun _ : Fin 3 ↦ v))
    (L.iteratedFDeriv_comp_left hf (i := 3) le_rfl)
  simp only [L, Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, TauCeti.iteratedFDeriv_three_apply]
    at hcomp
  let f := fun u ↦ riemannianExpPullbackMetric I M p u w z
  have hfn : ContDiffAt ℝ 3 f 0 :=
    (hf.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  -- Restrict `f` to the line `s ↦ s • v` through the origin.
  have hline := ContDiffAt.deriv_deriv_deriv_comp_add_smul (f := f) (x := 0) (t := (0 : ℝ)) (y := v)
    (by simpa using hfn)
  simp only [zero_add, zero_smul] at hline
  rw [← hcomp, ← hline]
  simpa only [f, riemannianExpPullbackMetric_apply] using
    deriv_deriv_deriv_inner_mfderiv_riemannianExp_zero (I := I) p v w z

/-- **Polarized third derivative of the exponential pullback metric at the origin.** Evaluating
`D³(exp_p^* g)_0` on three directions `u₁, u₂, u₃` gives `-⅙` times the sum of
`⟪(∇_a R)(w, b)c, z⟫` over the six permutations of `(u₁, u₂, u₃)`. -/
theorem fderiv_fderiv_fderiv_riemannianExpPullbackMetric_zero_apply
    (p : M) (u₁ u₂ u₃ w z : TangentSpace I p) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p))) 0 u₁ u₂ u₃ w z =
      -(1 / 6 : ℝ) *
        (inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
            (leviCivitaConnection I M) p u₁ w u₂ u₃) z +
          inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
            (leviCivitaConnection I M) p u₁ w u₃ u₂) z +
          inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
            (leviCivitaConnection I M) p u₂ w u₁ u₃) z +
          inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
            (leviCivitaConnection I M) p u₂ w u₃ u₁) z +
          inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
            (leviCivitaConnection I M) p u₃ w u₁ u₂) z +
          inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
            (leviCivitaConnection I M) p u₃ w u₂ u₁) z) := by
  have hg := contDiffAt_riemannianExpPullbackMetric (I := I) p
  let S (a b c : TangentSpace I p) : ℝ :=
    fderiv ℝ (fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p))) 0 a b c w z
  let R3 (a b c : TangentSpace I p) : ℝ :=
    -inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
      (leviCivitaConnection I M) p a w b c) z
  have hS := TauCeti.map_add_add_sub_map_add_of_map_add S
    (fun _ _ _ _ ↦ by simp [S]) (fun _ _ _ _ ↦ by simp [S]) (fun _ _ _ _ ↦ by simp [S]) u₁ u₂ u₃
  have hR := TauCeti.map_add_add_sub_map_add_of_map_add R3
    (fun _ _ _ _ ↦ by simp [R3, inner_add_left]; ring)
    (fun _ _ _ _ ↦ by simp [R3, inner_add_left]; ring)
    (fun _ _ _ _ ↦ by simp [R3, inner_add_left]; ring) u₁ u₂ u₃
  have hdiag (v : TangentSpace I p) : S v v v = R3 v v v :=
    fderiv_fderiv_fderiv_riemannianExpPullbackMetric_apply_self p v w z
  have hsymm12 (a b c : TangentSpace I p) : S a b c = S b a c :=
    congrArg (fun L ↦ L c w z)
      ((hg.fderiv_right (m := 2) (by simp)).isSymmSndFDerivAt (by simp) a b)
  have hsymm23 (a b c : TangentSpace I p) : S a b c = S a c b :=
    congrArg (fun L ↦ L w z) (fderiv_fderiv_fderiv_apply_comm hg (by simp) a b c)
  have hsum : 6 * S u₁ u₂ u₃ =
      R3 u₁ u₂ u₃ + R3 u₁ u₃ u₂ + R3 u₂ u₁ u₃ + R3 u₂ u₃ u₁ + R3 u₃ u₁ u₂ + R3 u₃ u₂ u₁ := by
    have heq : S u₁ u₂ u₃ + S u₁ u₃ u₂ + S u₂ u₁ u₃ + S u₂ u₃ u₁ + S u₃ u₁ u₂ + S u₃ u₂ u₁ =
        R3 u₁ u₂ u₃ + R3 u₁ u₃ u₂ + R3 u₂ u₁ u₃ + R3 u₂ u₃ u₁ + R3 u₃ u₁ u₂ + R3 u₃ u₂ u₁ := by
      rw [← hS, ← hR]
      simp only [hdiag]
    have h321 : S u₃ u₂ u₁ = S u₁ u₂ u₃ :=
      (hsymm23 u₃ u₂ u₁).trans ((hsymm12 u₃ u₁ u₂).trans (hsymm23 u₁ u₃ u₂))
    rw [hsymm23 u₁ u₃ u₂, hsymm12 u₂ u₁ u₃, hsymm23 u₂ u₃ u₁, hsymm12 u₂ u₁ u₃,
      hsymm12 u₃ u₁ u₂, hsymm23 u₁ u₃ u₂, h321] at heq
    linarith
  dsimp only [S, R3] at hsum
  linarith

/-- If the covariant derivative of the Riemann curvature tensor vanishes at `p` (for instance on a
locally symmetric space), the third derivative of the exponential pullback metric at the origin
vanishes. -/
theorem
    fderiv_fderiv_fderiv_riemannianExpPullbackMetric_zero_eq_zero_of_derivCurvatureTensor_eq_zero
    {p : M}
    (hR : (leviCivitaConnection I M).derivCurvatureTensor (leviCivitaConnection I M) p = 0) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p))) 0 = 0 := by
  ext u₁ u₂ u₃ w z
  simp [fderiv_fderiv_fderiv_riemannianExpPullbackMetric_zero_apply, hR]

/-- **Uniform cubic expansion of the exponential metric.** On a small tangent ball in the natural
exponential domain, `⟪d exp_p(v) w, d exp_p(v) z⟫` equals
`⟪w, z⟫ - ⅓ ⟪R(w, v)v, z⟫ - ⅙ ⟪(∇_v R)(w, v)v, z⟫` up to `C ‖v‖⁴ ‖w‖ ‖z‖`, with one radius and one
constant for all input vectors and no completeness assumption. -/
theorem exists_abs_inner_mfderiv_riemannianExp_sub_add_derivCurvatureTensor_le (p : M) :
    ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ expDomain I M p ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w z : TangentSpace I p,
        |inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z) - inner ℝ w z +
          (1 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z +
          (1 / 6 : ℝ) * inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
            (leviCivitaConnection I M) p v w v v) z| ≤
            C * ‖v‖ ^ 4 * ‖w‖ * ‖z‖ := by
  have hf : ContDiffAt ℝ 4 (riemannianExpPullbackMetric I M p) 0 :=
    (contDiffAt_riemannianExpPullbackMetric (I := I) p).of_le (by simp)
  obtain ⟨r, hr, C, hC, hdom, hb⟩ := exists_ball_abs_inner_mfderiv_riemannianExp_sub_le_of_isBigO p
    (fun v ↦ riemannianExpPullbackMetric I M p 0 +
      (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p)) 0 v v +
      (6⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ (fderiv ℝ (riemannianExpPullbackMetric I M p))) 0 v v v) 4
    (by simpa only [sub_zero, fderiv_riemannianExpPullbackMetric_zero, zero_apply,
      sub_add_eq_sub_sub] using hf.isBigO_sub_taylor_three)
  refine ⟨r, hr, C, hC, hdom, fun v hv w z ↦ ?_⟩
  convert hb v hv w z using 2
  simp only [add_apply, smul_apply, smul_eq_mul, riemannianExpPullbackMetric_zero,
    fderiv_fderiv_riemannianExpPullbackMetric_apply_self,
    fderiv_fderiv_fderiv_riemannianExpPullbackMetric_apply_self]
  rw [innerSL_apply_apply]
  ring

/-- **Quartic accuracy of the quadratic metric expansion when `(∇R)_p = 0`.** At a point where the
covariant derivative of the Riemann curvature tensor vanishes (for instance on any locally
symmetric space), the quadratic normal-coordinate expansion already has `O(‖v‖⁴)` remainder. -/
theorem
    exists_abs_inner_mfderiv_riemannianExp_sub_le_mul_norm_pow_four_of_derivCurvatureTensor_eq_zero
    {p : M}
    (hR : (leviCivitaConnection I M).derivCurvatureTensor (leviCivitaConnection I M) p = 0) :
    ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ expDomain I M p ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w z : TangentSpace I p,
        |inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z) - inner ℝ w z +
          (1 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z| ≤
            C * ‖v‖ ^ 4 * ‖w‖ * ‖z‖ := by
  obtain ⟨r, hr, C, hC, hdom, hb⟩ :=
    exists_abs_inner_mfderiv_riemannianExp_sub_add_derivCurvatureTensor_le (I := I) p
  refine ⟨r, hr, C, hC, hdom, fun v hv w z ↦ ?_⟩
  simpa [hR] using hb v hv w z

namespace IsNormalDomain

/-- **Uniform cubic expansion of normal-coordinate metric coefficients.** On a small tangent ball
inside any normal domain `U`, `⟪X_w(exp_p v), X_z(exp_p v)⟫` equals
`⟪w, z⟫ - ⅓ ⟪R(w, v)v, z⟫ - ⅙ ⟪(∇_v R)(w, v)v, z⟫` up to `C ‖v‖⁴ ‖w‖ ‖z‖`. -/
theorem exists_abs_inner_normalCoordinateField_sub_add_derivCurvatureTensor_le
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U) :
    ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ U ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w z : TangentSpace I p,
        |inner ℝ (normalCoordinateField I M p U w (riemannianExp I M p v))
            (normalCoordinateField I M p U z (riemannianExp I M p v)) - inner ℝ w z +
          (1 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z +
          (1 / 6 : ℝ) * inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
            (leviCivitaConnection I M) p v w v v) z| ≤
            C * ‖v‖ ^ 4 * ‖w‖ * ‖z‖ :=
  exists_abs_inner_normalCoordinateField_of_expDomain_bound h 4 _
    (exists_abs_inner_mfderiv_riemannianExp_sub_add_derivCurvatureTensor_le (I := I) p)

/-- **Coordinate form of the cubic normal-coordinate metric expansion.** On a small tangent ball
inside any normal domain `U`, the metric coefficients of any orthonormal family `(e_i)` satisfy
`g_{ij}(exp_p v) = δ_{ij} - ⅓ ⟪R(e_i, v)v, e_j⟫ - ⅙ ⟪(∇_v R)(e_i, v)v, e_j⟫ + O(‖v‖⁴)`, with one
radius and one constant independent of the orthonormal family and indices. -/
theorem exists_abs_inner_normalCoordinateField_orthonormal_sub_add_derivCurvatureTensor_le
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    (ι : Type*) [DecidableEq ι] :
    ∃ r > 0, ∃ C > 0, Metric.ball (0 : TangentSpace I p) r ⊆ U ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r,
        ∀ {e : ι → TangentSpace I p}, Orthonormal ℝ e → ∀ i j : ι,
          |inner ℝ (normalCoordinateField I M p U (e i) (riemannianExp I M p v))
              (normalCoordinateField I M p U (e j) (riemannianExp I M p v)) -
            (if i = j then 1 else 0) +
            (1 / 3 : ℝ) *
              inner ℝ ((leviCivitaConnection I M).curvatureTensor p (e i) v v) (e j) +
            (1 / 6 : ℝ) * inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
              (leviCivitaConnection I M) p v (e i) v v) (e j)| ≤
              C * ‖v‖ ^ 4 := by
  obtain ⟨r, hr, C, hC, hU, hb⟩ :=
    h.exists_abs_inner_normalCoordinateField_sub_add_derivCurvatureTensor_le
  refine ⟨r, hr, C, hC, hU, fun v hv {e} he i j ↦ ?_⟩
  simpa only [orthonormal_iff_ite.mp he i j, he.norm_eq_one, mul_one] using hb v hv (e i) (e j)

end IsNormalDomain

/-- **The fifth-order angular squared-length expansion.** One radius and one error constant work
for all orthonormal pairs at `p`, for positive and negative times, giving `O(|t|⁶)` remainder. -/
theorem exists_abs_norm_sq_mfderiv_riemannianExp_sub_add_derivCurvatureTensor_le (p : M) :
    ∃ r > 0, ∃ C > 0, ∀ T Y : TangentSpace I p, Orthonormal ℝ ![T, Y] →
      ∀ t : ℝ, |t| < r → t • T ∈ expDomain I M p ∧
        |‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • T) (t • Y)‖ ^ 2 -
            t ^ 2 + (1 / 3 : ℝ) * (leviCivitaConnection I M).sectionalCurvature
              (isMetricCompatible_leviCivitaConnection I) p T Y * t ^ 4 +
            (1 / 6 : ℝ) * inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
              (leviCivitaConnection I M) p T Y T T) Y * t ^ 5| ≤ C * |t| ^ 6 := by
  obtain ⟨r, hr, C, hC, hb⟩ := exists_abs_norm_sq_mfderiv_riemannianExp_of_ball_bound p 4
    (fun v w z ↦ (1 / 6 : ℝ) * inner ℝ ((leviCivitaConnection I M).derivCurvatureTensor
      (leviCivitaConnection I M) p v w v v) z)
    (exists_abs_inner_mfderiv_riemannianExp_sub_add_derivCurvatureTensor_le (I := I) p)
  refine ⟨r, hr, C, hC, fun T Y h t ht ↦ (hb T Y h t ht).imp_right fun he ↦ ?_⟩
  convert he using 2
  simp only [LinearMap.map_smul, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  ring

end TauCeti.Manifold
