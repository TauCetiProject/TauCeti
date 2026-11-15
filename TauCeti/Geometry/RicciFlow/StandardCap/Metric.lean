/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Distance
public import TauCeti.Geometry.RicciFlow.StandardCap.SectionalCurvature
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Normed.Operator.Coercive
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Coercive
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge
import TauCeti.Geometry.Manifold.Riemannian.Restriction.Real
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Topology.EMetricSpace.LocalComparison
import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# The complete smooth standard cap metric

Let `f : ℝ → ℝ` be a standard cap profile (`TauCeti.IsStandardCapProfile f`) and `V` a real inner
product space. Decomposing `v ∈ V` away from `0` into radial and spherical parts rewrites the
warped-product metric `dr² + f(r)² g_(Sⁿ)` (`r = ‖x‖`) in global Cartesian form

`g_x(v, w) = (f ‖x‖ / ‖x‖)² ⟪v, w⟫ + ((1 - (f ‖x‖ / ‖x‖)²) / ‖x‖²) ⟪x, v⟫ ⟪x, w⟫`,

extended to `⟪v, w⟫` at `x = 0`. Using the smooth radial-square quotients `TauCeti.capAngularQuot`
and `TauCeti.capRadialQuot`, `g` extends smoothly across `0 ∈ V`, and satisfies:

* `g_x(v, v) ≤ ‖v‖²`, `(f B / B)² ‖v‖² ≤ g_x(v, v)` on `{‖x‖ ≤ B}`, and
  `⟪x, v⟫² / (1 + ‖x‖²) ≤ g_x(v, v)`;
* polar coordinates (`TauCeti.radialSphereDiffeomorph`) define a Riemannian isometry from
  `hf.puncturedMetric V` onto the restriction of `hf.metric V` to `V ∖ {0}`;
* for finite-dimensional `V`, `WithMetric (hf.metric V)` is metrically and geodesically complete,
  has nonnegative sectional and scalar curvature everywhere, constant sectional curvature `1 / 4`
  and scalar curvature `d (d - 1) / 4` near `0`, and scalar curvature `(d - 1) (d - 2) / 2` on the
  cylindrical end (`3 / 2` and `1` when `d = 3`);
* if a continuous Riemannian metric on `V` (`dim V ≥ 2`) restricts on concentric spheres to
  `f(r)² g_(Sⁿ)` for small `r > 0`, then `|f(r)| → 0` as `r → 0⁺`, ruling out `f(0) > 0`.

## Main definitions and results

* `TauCeti.IsStandardCapProfile.metric`, `TauCeti.IsStandardCapProfile.polarRiemannianIsometry`.
* `TauCeti.IsStandardCapProfile.completeSpace_withMetric`,
  `TauCeti.IsStandardCapProfile.completeSpace_withMetric_metricSpace`,
  `TauCeti.IsStandardCapProfile.isGeodesicallyCompleteAt_withMetric`.
* `TauCeti.IsStandardCapProfile.sectionalCurvature_withMetric_nonneg`,
  `TauCeti.IsStandardCapProfile.exists_hasSectionalCurvatureAt_withMetric_round`,
  `TauCeti.IsStandardCapProfile.scalarCurvature_metric_nonneg`,
  `TauCeti.IsStandardCapProfile.exists_scalarCurvature_metric_eq_round`,
  `TauCeti.IsStandardCapProfile.exists_scalarCurvature_metric_eq_cylinder`,
  `TauCeti.exists_standardCapMetric`.
* `TauCeti.tendsto_abs_of_spherical_pullback`, `TauCeti.eq_zero_of_spherical_pullback`.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Math. Monogr. 3 (2007),
  Definition 12.1; G. Perelman, arXiv:math/0303109 (2003), §2; P. Petersen, *Riemannian Geometry*,
  3rd ed. (2016), §1.4.4.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold Metric Module Real Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace Manifold Matrix NNReal Topology

namespace TauCeti

section BilinForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private def realInnerCLM (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ

@[simp]
private theorem realInnerCLM_apply (x y : V) : realInnerCLM V x y = ⟪x, y⟫_ℝ := (rfl)

private def capBilinForm (f : ℝ → ℝ) (x : V) : V →L[ℝ] V →L[ℝ] ℝ :=
  capAngularQuot f (‖x‖ ^ 2) • realInnerCLM V +
    capRadialQuot f (‖x‖ ^ 2) • (realInnerCLM V x).smulRight (realInnerCLM V x)

private theorem capBilinForm_apply (f : ℝ → ℝ) (x v w : V) :
    capBilinForm f x v w = capAngularQuot f (‖x‖ ^ 2) * ⟪v, w⟫_ℝ +
      capRadialQuot f (‖x‖ ^ 2) * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) := by
  simp [capBilinForm, mul_comm ⟪x, v⟫_ℝ ⟪x, w⟫_ℝ]

private theorem contDiff_capBilinForm {f : ℝ → ℝ} (hf : IsStandardCapProfile f) :
    ContDiff ℝ ∞ (capBilinForm f : V → V →L[ℝ] V →L[ℝ] ℝ) := by
  let _ : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
  let _ : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  have hnsq : ContDiff ℝ ∞ (fun x : V ↦ ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hinner : ContDiff ℝ ∞ (realInnerCLM V) := (innerSL ℝ (E := V)).contDiff
  exact ((hf.contDiff_capAngularQuot.comp hnsq).smul contDiff_const).add
    ((hf.contDiff_capRadialQuot.comp hnsq).smul (hinner.smulRight hinner))

private theorem capBilinForm_symm (f : ℝ → ℝ) (x v w : V) :
    capBilinForm f x v w = capBilinForm f x w v := by
  rw [capBilinForm_apply, capBilinForm_apply, real_inner_comm w v, mul_comm ⟪x, w⟫_ℝ ⟪x, v⟫_ℝ]

private theorem capBilinForm_self_of_ne_zero (f : ℝ → ℝ) {x : V} (hx : x ≠ 0) (v : V) :
    capBilinForm f x v v =
      (f ‖x‖ / ‖x‖) ^ 2 * (‖v‖ ^ 2 - ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2) + ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2 := by
  have hpos := norm_pos_iff.2 hx
  rw [capBilinForm_apply, capAngularQuot_sq_of_pos f hpos, capRadialQuot_sq_of_pos f hpos,
    real_inner_self_eq_norm_sq]
  field_simp [pow_ne_zero 2 hpos.ne']; ring

private theorem sq_inner_div_norm_sq_le (x v : V) : ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [div_le_iff₀' (pow_pos (norm_pos_iff.2 hx) 2), ← mul_pow]
    exact sq_le_sq.2 ((abs_real_inner_le_norm x v).trans_eq
      (abs_of_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg v))).symm)

private theorem capBilinForm_self_le {f : ℝ → ℝ} (hf : IsStandardCapProfile f) (x v : V) :
    capBilinForm f x v v ≤ ‖v‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [capBilinForm_apply]
  · rw [capBilinForm_self_of_ne_zero f hx v]
    nlinarith [hf.sq_div_self_le_one ‖x‖, sub_nonneg.2 (sq_inner_div_norm_sq_le x v)]

private theorem sq_div_self_mul_le_capBilinForm_self {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
    {x : V} (hx : x ≠ 0) (v : V) :
    (f ‖x‖ / ‖x‖) ^ 2 * ‖v‖ ^ 2 ≤ capBilinForm f x v v := by
  have hrad : 0 ≤ ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2 := by positivity
  rw [capBilinForm_self_of_ne_zero f hx v]
  nlinarith [hf.sq_div_self_le_one ‖x‖]

private theorem isCoercive_capBilinForm {f : ℝ → ℝ} (hf : IsStandardCapProfile f) (x : V) :
    IsCoercive (capBilinForm f x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨1, one_pos, fun v ↦ by simp [capBilinForm_apply, sq]⟩
  · refine ⟨(f ‖x‖ / ‖x‖) ^ 2, sq_pos_of_pos (hf.div_self_pos (norm_ne_zero_iff.2 hx)), fun v ↦ ?_⟩
    simpa only [sq, mul_assoc] using sq_div_self_mul_le_capBilinForm_self hf hx v

private theorem le_capBilinForm_self_of_norm_le {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
    {B : ℝ} {x : V} (hx : ‖x‖ ≤ B) (v : V) :
    (f B / B) ^ 2 * ‖v‖ ^ 2 ≤ capBilinForm f x v v := by
  rcases eq_or_lt_of_le ((norm_nonneg x).trans hx) with rfl | hB
  · obtain rfl := norm_le_zero_iff.1 hx; simp [capBilinForm_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp only [capBilinForm_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, capAngularQuot_zero, one_mul, inner_zero_left, mul_zero, add_zero,
        real_inner_self_eq_norm_sq]
      nlinarith [hf.sq_div_self_le_one B, sq_nonneg ‖v‖]
    · have hanti := hf.antitoneOn_div_self (mem_Ioi.2 (norm_pos_iff.2 hx0)) (mem_Ioi.2 hB) hx
      exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hf.div_self_pos hB.ne').le hanti 2)
        (sq_nonneg ‖v‖)).trans (sq_div_self_mul_le_capBilinForm_self hf hx0 v)

private theorem sq_inner_div_le_capBilinForm_self (f : ℝ → ℝ) (x v : V) :
    ⟪x, v⟫_ℝ ^ 2 / (1 + ‖x‖ ^ 2) ≤ capBilinForm f x v v := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [capBilinForm_apply]
  · have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
    rw [capBilinForm_self_of_ne_zero f hx v]
    exact (div_le_div_of_nonneg_left (sq_nonneg _) hpos (by linarith)).trans (le_add_of_nonneg_left
      (mul_nonneg (sq_nonneg _) (sub_nonneg.2 (sq_inner_div_norm_sq_le x v))))

end BilinForm

namespace IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)

/-- The **standard cap metric** on `V` associated to `f`: Euclidean at `0` and equal to
`dr² + f(r)² g_(Sⁿ)` in polar coordinates `x = r • u` away from `0`. -/
def metric (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    ContMDiffRiemannianMetric 𝓘(ℝ, V) ∞ V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) :=
  coerciveRiemannianMetric (capBilinForm f) (contDiff_capBilinForm hf) (capBilinForm_symm f)
    (isCoercive_capBilinForm hf)

section Basic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem metric_inner_eq_capBilinForm (x : V) (v w : TangentSpace 𝓘(ℝ, V) x) :
    (hf.metric V).inner x v w =
      capBilinForm f x (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) :=
  coerciveRiemannianMetric_inner _ _ _ _ x v w

/-- At the tip `0 ∈ V`, the standard cap metric coincides with the Euclidean inner product. -/
@[simp]
theorem metric_inner_zero (v w : TangentSpace 𝓘(ℝ, V) (0 : V)) :
    (hf.metric V).inner 0 v w =
      ⟪NormedSpace.fromTangentSpace (0 : V) v, NormedSpace.fromTangentSpace (0 : V) w⟫_ℝ := by
  rw [hf.metric_inner_eq_capBilinForm, capBilinForm_apply]; simp

/-- Away from `0 ∈ V`, the standard cap metric splits into angular and radial parts. -/
theorem metric_inner_of_ne_zero {x : V} (hx : x ≠ 0) (v w : TangentSpace 𝓘(ℝ, V) x) :
    (hf.metric V).inner x v w =
      (f ‖x‖ / ‖x‖) ^ 2 * ⟪NormedSpace.fromTangentSpace x v, NormedSpace.fromTangentSpace x w⟫_ℝ +
        (1 - (f ‖x‖ / ‖x‖) ^ 2) / ‖x‖ ^ 2 *
          (⟪x, NormedSpace.fromTangentSpace x v⟫_ℝ * ⟪x, NormedSpace.fromTangentSpace x w⟫_ℝ) := by
  have hpos := norm_pos_iff.2 hx
  rw [hf.metric_inner_eq_capBilinForm, capBilinForm_apply, capAngularQuot_sq_of_pos f hpos,
    capRadialQuot_sq_of_pos f hpos]

/-- The standard cap metric is everywhere bounded above by the Euclidean norm squared. -/
theorem metric_inner_self_le (x : V) (v : TangentSpace 𝓘(ℝ, V) x) :
    (hf.metric V).inner x v v ≤ ‖NormedSpace.fromTangentSpace x v‖ ^ 2 := by
  rw [hf.metric_inner_eq_capBilinForm]; exact capBilinForm_self_le hf x _

/-- On `{‖x‖ ≤ B}`, the standard cap metric dominates `(f B / B)²` times the Euclidean norm
squared. -/
theorem le_metric_inner_self_of_norm_le {B : ℝ} {x : V} (hx : ‖x‖ ≤ B)
    (v : TangentSpace 𝓘(ℝ, V) x) :
    (f B / B) ^ 2 * ‖NormedSpace.fromTangentSpace x v‖ ^ 2 ≤ (hf.metric V).inner x v v := by
  rw [hf.metric_inner_eq_capBilinForm]; exact le_capBilinForm_self_of_norm_le hf hx _

/-- The radial component `⟪x, v⟫² / (1 + ‖x‖²)` is globally bounded above by `hf.metric V`. -/
theorem sq_inner_div_le_metric_inner_self (x : V) (v : TangentSpace 𝓘(ℝ, V) x) :
    ⟪x, NormedSpace.fromTangentSpace x v⟫_ℝ ^ 2 / (1 + ‖x‖ ^ 2) ≤ (hf.metric V).inner x v v := by
  rw [hf.metric_inner_eq_capBilinForm]; exact sq_inner_div_le_capBilinForm_self f x _

end Basic

section PolarIsometry

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)]

private theorem puncturedMetric_inner_eq_metric_inner_polar
    (p : standardCapRadialDomain × sphere (0 : V) 1)
    (v w : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    (hf.puncturedMetric (n := n) V).inner p v w =
      (hf.metric V).inner ((p.1 : ℝ) • (p.2 : V))
        (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
          (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p v)
        (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
          (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p w) := by
  have hr : 0 < (p.1 : ℝ) := p.1.property
  have hu : ‖(p.2 : V)‖ = 1 := norm_eq_of_mem_sphere p.2
  have hu2 : ⟪(p.2 : V), (p.2 : V)⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hx0 : (p.1 : ℝ) • (p.2 : V) ≠ 0 := smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere p.2)
  have hnorm : ‖(p.1 : ℝ) • (p.2 : V)‖ = (p.1 : ℝ) := by
    rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le]
  have horth_v := inner_coe_mvfderiv_subtypeVal_sphere p.2 (Manifold.tangentSpaceProdEquiv p v).2
  have horth_w := inner_coe_mvfderiv_subtypeVal_sphere p.2 (Manifold.tangentSpaceProdEquiv p w).2
  have horth_v' : ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.2
      (Manifold.tangentSpaceProdEquiv p v).2, (p.2 : V)⟫_ℝ = 0 := by rwa [real_inner_comm]
  have hfv (z : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
      NormedSpace.fromTangentSpace ((p.1 : ℝ) • (p.2 : V))
        (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
          (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p z) =
      mvfderiv (𝓘(ℝ).prod (𝓡 n))
        (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p z := rfl
  rw [hf.puncturedMetric_inner, Manifold.inner_restrictOpenTangentSpace_real,
    ContMDiffRiemannianMetric.ofLE_inner, sphereRoundMetric_inner,
    hf.metric_inner_of_ne_zero hx0, hfv v, hfv w,
    mvfderiv_radial_smul_coe_sphere_apply, mvfderiv_radial_smul_coe_sphere_apply, hnorm]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    horth_v, horth_w, horth_v', hu2, mul_zero, zero_add, add_zero, mul_one]
  field_simp [hr.ne']; ring

/-- The warped-product punctured metric `dr² + f(r)² g_(Sⁿ)` is the pullback along polar
coordinates `radialSphereDiffeomorph V` of the standard cap metric restricted to `V ∖ {0}`. -/
theorem puncturedMetric_eq_pullback :
    hf.puncturedMetric (n := n) V =
      ((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).pullback
        (radialSphereDiffeomorph (n := n) V)
        ((radialSphereDiffeomorph (n := n) V).contMDiff.of_le (by simp))
        (fun _ ↦
          ((radialSphereDiffeomorph (n := n) V).isInvertible_mfderiv (by simp)).injective) := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  ext p v w
  have hcomp : ((Subtype.val : puncturedSpace V → V) ∘ radialSphereDiffeomorph (n := n) V) =
      fun q ↦ (q.1 : ℝ) • (q.2 : V) := funext coe_radialSphereDiffeomorph_apply
  have hdf (z : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
      NormedSpace.fromTangentSpace (radialSphereDiffeomorph (n := n) V p : V)
          (Manifold.tangentSpaceOpenEquiv (radialSphereDiffeomorph (n := n) V p)
            (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) (radialSphereDiffeomorph (n := n) V) p z)) =
        mvfderiv (𝓘(ℝ).prod (𝓡 n))
          (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p z := by
    have h1 : Manifold.tangentSpaceOpenEquiv (radialSphereDiffeomorph (n := n) V p)
        (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) (radialSphereDiffeomorph (n := n) V) p z) =
        mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
          ((Subtype.val : puncturedSpace V → V) ∘ radialSphereDiffeomorph (n := n) V) p z := by
      rw [mfderiv_comp_apply p ((contMDiff_subtype_val (n := 1)).mdifferentiableAt one_ne_zero)
        ((radialSphereDiffeomorph (n := n) V).contMDiff.mdifferentiableAt (by simp)),
        Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe]
    rw [h1]
    change mvfderiv (𝓘(ℝ).prod (𝓡 n))
      ((Subtype.val : puncturedSpace V → V) ∘ radialSphereDiffeomorph (n := n) V) p z = _
    rw [hcomp]
  rw [hf.puncturedMetric_inner_eq_metric_inner_polar V p v w, hf.metric_inner_eq_capBilinForm,
    ContMDiffRiemannianMetric.pullback_inner,
    ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
    hf.metric_inner_eq_capBilinForm, hdf v, hdf w, coe_radialSphereDiffeomorph_apply]
  rfl

/-- **Polar coordinates are a Riemannian isometry** from `hf.puncturedMetric V` on `(0, ∞) × Sⁿ`
onto the standard cap metric restricted to the punctured space `V ∖ {0}`. -/
def polarRiemannianIsometry :
    letI : RiemannianBundle
      (fun p : standardCapRadialDomain × sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : puncturedSpace V ↦ TangentSpace 𝓘(ℝ, V) x) :=
      ⟨((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).toRiemannianMetric⟩
    RiemannianIsometry (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (standardCapRadialDomain × sphere (0 : V) 1) (puncturedSpace V) :=
  letI : RiemannianBundle _ := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  letI : RiemannianBundle _ :=
    ⟨((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).toRiemannianMetric⟩
  { toDiffeomorph := radialSphereDiffeomorph (n := n) V
    inner_mfderiv' := fun p v w ↦ by
      have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
      change ((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).inner _ _ _ =
        (hf.puncturedMetric (n := n) V).inner p v w
      rw [hf.puncturedMetric_eq_pullback V, ContMDiffRiemannianMetric.pullback_inner] }

@[simp]
theorem coe_polarRiemannianIsometry (p : standardCapRadialDomain × sphere (0 : V) 1) :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : puncturedSpace V ↦ TangentSpace 𝓘(ℝ, V) x) :=
      ⟨((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).toRiemannianMetric⟩
    (hf.polarRiemannianIsometry (n := n) V p : V) = (p.1 : ℝ) • (p.2 : V) :=
  coe_radialSphereDiffeomorph_apply p

private theorem isLocalRiemannianIsometry_toWithMetric_polar :
    letI : RiemannianBundle _ := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    letI : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
    IsLocalRiemannianIsometry (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (fun p : standardCapRadialDomain × sphere (0 : V) 1 ↦
        WithMetric.toWithMetric (hf.metric V) ((p.1 : ℝ) • (p.2 : V))) := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  let _ : RiemannianBundle _ := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  let _ : RiemannianBundle _ :=
    ⟨((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).toRiemannianMetric⟩
  let _ : RiemannianBundle _ := ⟨(hf.metric V).toRiemannianMetric⟩
  have hto : IsLocalRiemannianIsometry 𝓘(ℝ, V) 𝓘(ℝ, V) (WithMetric.toWithMetric (hf.metric V)) :=
    { contMDiff := WithMetric.contMDiff_toWithMetric
      isInvertible_mfderiv := fun x ↦ by
        rw [WithMetric.mfderiv_toWithMetric]; exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
      inner_mfderiv := fun x v w ↦ by
        rw [WithMetric.inner_def, WithMetric.ofWithMetric_toWithMetric,
          WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric,
          WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric]
        rfl }
  have hfn : (WithMetric.toWithMetric (hf.metric V) ∘ Subtype.val ∘
      ⇑(hf.polarRiemannianIsometry (n := n) V)) =
      fun p ↦ WithMetric.toWithMetric (hf.metric V) ((p.1 : ℝ) • (p.2 : V)) :=
    funext fun p ↦ congrArg _ (coe_polarRiemannianIsometry hf V p)
  rw [← hfn]
  exact hto.comp (((hf.metric V).isLocalRiemannianIsometry_restrictOpenTangentSpace
    (puncturedSpace V)).comp (hf.polarRiemannianIsometry (n := n) V).isLocalRiemannianIsometry)

end PolarIsometry

/-! ### Metric and geodesic completeness of the standard cap -/

section Completeness

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
include hf

/-- Because `g_x(v, v) ≤ ‖v‖²` everywhere, the Riemannian extended distance on
`WithMetric (hf.metric V)` is at most the Euclidean extended distance on `V`. -/
theorem riemannianEDist_toWithMetric_le (x y : V) :
    Manifold.riemannianEDist 𝓘(ℝ, V)
      (WithMetric.toWithMetric (hf.metric V) x)
      (WithMetric.toWithMetric (hf.metric V) y) ≤ edist x y := by
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, V)) x y,
    ← one_mul (Manifold.riemannianEDist 𝓘(ℝ, V) x y), ← ENNReal.coe_one]
  refine TauCeti.Manifold.riemannianEDist_le_mul (C := (1 : NNReal))
    WithMetric.contMDiff_toWithMetric one_ne_zero (fun z v ↦ ?_) x y
  rw [NNReal.coe_one, one_mul]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [← real_inner_self_eq_norm_sq, WithMetric.inner_def, WithMetric.ofWithMetric_toWithMetric,
    WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric, norm_tangentSpace_vectorSpace]
  exact hf.metric_inner_self_le z v

private theorem norm_mvfderiv_japaneseBracket_le (p : WithMetric (hf.metric V))
    (v : TangentSpace 𝓘(ℝ, V) p) :
    ‖mvfderiv 𝓘(ℝ, V) (fun q : WithMetric (hf.metric V) ↦ √(1 + ‖q.ofWithMetric‖ ^ 2)) p v‖ₑ ≤
      (1 : ℝ≥0) * ‖v‖ₑ := by
  set ψ : V → ℝ := fun x ↦ √(1 + ‖x‖ ^ 2)
  have hpos (x : V) : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hderiv (x : V) : HasFDerivAt ψ ((1 / (2 * √(1 + ‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x :=
    (((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_add 1).sqrt (hpos x).ne'
  rw [ENNReal.coe_one, one_mul, ← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  let w := NormedSpace.fromTangentSpace p.ofWithMetric
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v)
  have hmv : mvfderiv 𝓘(ℝ, V) (ψ ∘ WithMetric.ofWithMetric) p v =
      ⟪p.ofWithMetric, w⟫_ℝ / √(1 + ‖p.ofWithMetric‖ ^ 2) := by
    rw [WithMetric.mvfderiv_comp_ofWithMetric_apply, mvfderiv_eq_fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, (hderiv p.ofWithMetric).fderiv]
    simp only [_root_.smul_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
    field_simp [(Real.sqrt_pos.2 (hpos p.ofWithMetric)).ne']
    rfl
  change ‖mvfderiv 𝓘(ℝ, V) (ψ ∘ WithMetric.ofWithMetric) p v‖ ≤ ‖v‖
  rw [hmv]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (hpos _).le, ← real_inner_self_eq_norm_sq v,
    WithMetric.inner_def]
  exact hf.sq_inner_div_le_metric_inner_self p.ofWithMetric _

/-- Points at Riemannian extended distance at most `R` from the tip `0` have Euclidean norm at most
`R + 1`. -/
theorem norm_ofWithMetric_le_of_riemannianEDist_le {p : WithMetric (hf.metric V)} {R : ℝ}
    (hR : 0 ≤ R)
    (hp : Manifold.riemannianEDist 𝓘(ℝ, V) p (WithMetric.toWithMetric (hf.metric V) 0) ≤
      ENNReal.ofReal R) :
    ‖p.ofWithMetric‖ ≤ R + 1 := by
  let ψ : WithMetric (hf.metric V) → ℝ := fun q ↦ √(1 + ‖q.ofWithMetric‖ ^ 2)
  have hψ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℝ) 1 ψ :=
    (((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun x ↦ by positivity).contMDiff).comp
      WithMetric.contMDiff_ofWithMetric
  have hed := Manifold.edist_le_mul_riemannianEDist hψ one_ne_zero
    hf.norm_mvfderiv_japaneseBracket_le p (WithMetric.toWithMetric (hf.metric V) 0)
  rw [ENNReal.coe_one, one_mul, edist_dist] at hed
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hed.trans hp)
  rw [ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_ofReal hR, Real.dist_eq] at hle
  have h0 : ψ (WithMetric.toWithMetric (hf.metric V) 0) = 1 := by simp [ψ]
  have hsqrt : √(1 + ‖p.ofWithMetric‖ ^ 2) ≤ R + 1 := by linarith [(le_abs_self _).trans hle, h0]
  have hsq : ‖p.ofWithMetric‖ ^ 2 ≤ (R + 1) ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
    rw [Real.sq_sqrt (by positivity)] at this
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

private theorem norm_mfderiv_ofWithMetric_le_of_norm_le {B : ℝ} (hB : 0 < B)
    {p : WithMetric (hf.metric V)} (hp : ‖p.ofWithMetric‖ ≤ B) (v : TangentSpace 𝓘(ℝ, V) p) :
    letI := normedAddCommGroupTangentSpaceVectorSpace p.ofWithMetric
    ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v‖ₑ ≤
      ((B / f B).toNNReal : ℝ≥0∞) * ‖v‖ₑ := by
  let _ := normedAddCommGroupTangentSpaceVectorSpace p.ofWithMetric
  set c : NNReal := (B / f B).toNNReal
  have hc : (c : ℝ) = B / f B := Real.coe_toNNReal _ (div_pos hB (hf.apply_pos hB)).le
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul c.coe_nonneg]
  refine ENNReal.ofReal_le_ofReal
    ((pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg c.coe_nonneg (norm_nonneg _))
      two_ne_zero).1 ?_)
  have hb := hf.le_metric_inner_self_of_norm_le hp
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v)
  have hinv : (c : ℝ) ^ 2 * (f B / B) ^ 2 = 1 := by
    rw [hc]; field_simp [(hf.apply_pos hB).ne', hB.ne']
  calc ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v‖ ^ 2
      = (c : ℝ) ^ 2 * ((f B / B) ^ 2 *
          ‖NormedSpace.fromTangentSpace p.ofWithMetric
            (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v)‖ ^ 2) := by
        rw [← mul_assoc, hinv, one_mul]; rfl
    _ ≤ (c : ℝ) ^ 2 * (hf.metric V).inner p.ofWithMetric _ _ :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = ((c : ℝ) * ‖v‖) ^ 2 := by rw [mul_pow, ← real_inner_self_eq_norm_sq, WithMetric.inner_def]

/-- Along a short path in `WithMetric (hf.metric V)` starting in `{d₁ · 0 ≤ R}`, the Euclidean
displacement is controlled by `((R + 3) / f (R + 3))` times the Riemannian distance. -/
private theorem edist_ofWithMetric_le_of_riemannianEDist_lt_one (R : NNReal)
    {x y : WithMetric (hf.metric V)}
    (hx : Manifold.riemannianEDist 𝓘(ℝ, V) x (WithMetric.toWithMetric (hf.metric V) 0) ≤ R)
    (hxy : Manifold.riemannianEDist 𝓘(ℝ, V) x y < 1) :
    edist x.ofWithMetric y.ofWithMetric ≤
      ((((R : ℝ) + 3) / f ((R : ℝ) + 3)).toNNReal : ℝ≥0∞) *
        Manifold.riemannianEDist 𝓘(ℝ, V) x y := by
  set B : ℝ := (R : ℝ) + 3
  have hB : 0 < B := by positivity
  set c : NNReal := (B / f B).toNNReal
  have hδ : ∀ δ : ℝ≥0∞, Manifold.riemannianEDist 𝓘(ℝ, V) x y < δ → δ ≤ 1 →
      edist x.ofWithMetric y.ofWithMetric ≤ (c : ℝ≥0∞) * δ := fun δ hyδ hδ1 ↦ by
    obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hyδ
    have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖(γ t).ofWithMetric‖ ≤ B := fun t ht ↦ by
      have hxt : Manifold.riemannianEDist 𝓘(ℝ, V) (γ t) x ≤ 1 := by
        rw [Manifold.riemannianEDist_comm]
        exact ((Manifold.riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc_right ht.2)) hγ0
          rfl ht.1).trans (Manifold.pathELength_mono le_rfl ht.2)).trans (hlen.le.trans hδ1)
      have hd : Manifold.riemannianEDist 𝓘(ℝ, V) (γ t)
          (WithMetric.toWithMetric (hf.metric V) 0) ≤ ENNReal.ofReal ((R : ℝ) + 1) := by
        calc Manifold.riemannianEDist 𝓘(ℝ, V) (γ t) (WithMetric.toWithMetric (hf.metric V) 0)
            ≤ Manifold.riemannianEDist 𝓘(ℝ, V) (γ t) x +
                Manifold.riemannianEDist 𝓘(ℝ, V) x (WithMetric.toWithMetric (hf.metric V) 0) :=
              Manifold.riemannianEDist_triangle
          _ ≤ 1 + R := add_le_add hxt hx
          _ = ENNReal.ofReal ((R : ℝ) + 1) := by
              rw [ENNReal.ofReal_add R.coe_nonneg zero_le_one, ENNReal.ofReal_coe_nnreal,
                ENNReal.ofReal_one, add_comm]
      exact (hf.norm_ofWithMetric_le_of_riemannianEDist_le (by positivity) hd).trans (by linarith)
    have key := Manifold.enorm_sub_le_mul_pathELength (f := WithMetric.ofWithMetric) zero_le_one
      (hγ.mdifferentiableOn one_ne_zero) (WithMetric.contMDiff_ofWithMetric.comp_contMDiffOn hγ)
      (fun t _ ↦ WithMetric.contMDiff_ofWithMetric.mdifferentiableAt one_ne_zero) fun t ht ↦
        hf.norm_mfderiv_ofWithMetric_le_of_norm_le hB (hnorm t ht) _
    rw [hγ0, hγ1, ← eDist_eq_eNorm_sub, edist_comm] at key
    exact key.trans (by gcongr)
  have : (𝓝[>] (Manifold.riemannianEDist 𝓘(ℝ, V) x y)).NeBot :=
    nhdsGT_neBot_of_exists_gt ⟨1, hxy⟩
  have hlim : Tendsto (fun δ ↦ (c : ℝ≥0∞) * δ) (𝓝[>] (Manifold.riemannianEDist 𝓘(ℝ, V) x y))
      (𝓝 ((c : ℝ≥0∞) * Manifold.riemannianEDist 𝓘(ℝ, V) x y)) :=
    (ENNReal.Tendsto.const_mul tendsto_id (Or.inr ENNReal.coe_ne_top)).mono_left
      nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hxy] with δ hδmem using hδ δ hδmem.1 hδmem.2.le

/-- **Metric completeness of the standard cap (extended distance).** For a finite-dimensional real
inner product space `V`, `WithMetric (hf.metric V)` is a complete space for
`PseudoEMetricSpace.ofRiemannianMetric`. -/
theorem completeSpace_withMetric :
    letI : PseudoEMetricSpace (WithMetric (hf.metric V)) :=
      .ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
    CompleteSpace (WithMetric (hf.metric V)) := by
  let d₀ : PseudoEMetricSpace (WithMetric (hf.metric V)) :=
    PseudoEMetricSpace.induced (WithMetric.ofWithMetric : WithMetric (hf.metric V) → V)
      inferInstance
  let d₁ : PseudoEMetricSpace (WithMetric (hf.metric V)) :=
    .ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  have hd₀_complete : @CompleteSpace (WithMetric (hf.metric V)) d₀.toUniformSpace := by
    let _ : UniformSpace (WithMetric (hf.metric V)) := d₀.toUniformSpace
    exact CompleteSpace.of_comp_eq_id (WithMetric.toWithMetric (hf.metric V))
      WithMetric.ofWithMetric rfl WithMetric.continuous_toWithMetric uniformContinuous_comap
  refine PseudoEMetricSpace.completeSpace_of_continuous_local_edist_bound_at_basepoint d₀ d₁
    (WithMetric.toWithMetric (hf.metric V) 0) hd₀_complete continuous_id
    (fun p ↦ ne_top_of_le_ne_top (edist_ne_top p.ofWithMetric 0)
      (hf.riemannianEDist_toWithMetric_le p.ofWithMetric 0)) fun R ↦ ?_
  set c : NNReal := (((R : ℝ) + 3) / f ((R : ℝ) + 3)).toNNReal
  refine ⟨max c (2 * (R + 1)), fun x y hx hy ↦ ?_⟩
  change Manifold.riemannianEDist 𝓘(ℝ, V) x (WithMetric.toWithMetric (hf.metric V) 0) ≤ R at hx
  change Manifold.riemannianEDist 𝓘(ℝ, V) y (WithMetric.toWithMetric (hf.metric V) 0) ≤ R at hy
  change edist x.ofWithMetric y.ofWithMetric ≤
    ((max c (2 * (R + 1)) : NNReal) : ℝ≥0∞) * Manifold.riemannianEDist 𝓘(ℝ, V) x y
  rcases lt_or_ge (Manifold.riemannianEDist 𝓘(ℝ, V) x y) 1 with hxy | hxy
  · exact (hf.edist_ofWithMetric_le_of_riemannianEDist_lt_one R hx hxy).trans
      (by gcongr; exact le_max_left _ _)
  · have hx_norm := hf.norm_ofWithMetric_le_of_riemannianEDist_le R.coe_nonneg
      (by simpa [ENNReal.ofReal_coe_nnreal] using hx)
    have hy_norm := hf.norm_ofWithMetric_le_of_riemannianEDist_le R.coe_nonneg
      (by simpa [ENNReal.ofReal_coe_nnreal] using hy)
    calc edist x.ofWithMetric y.ofWithMetric
        = ENNReal.ofReal ‖x.ofWithMetric - y.ofWithMetric‖ := by rw [edist_dist, dist_eq_norm]
      _ ≤ ENNReal.ofReal (2 * ((R : ℝ) + 1)) :=
          ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (by linarith))
      _ = ((2 * (R + 1) : NNReal) : ℝ≥0∞) * 1 := by
          push_cast [ENNReal.ofReal_mul]; simp [ENNReal.ofReal_add]
      _ ≤ ((max c (2 * (R + 1)) : NNReal) : ℝ≥0∞) * Manifold.riemannianEDist 𝓘(ℝ, V) x y := by
          gcongr; exact le_max_right _ _

/-- **Metric completeness of the standard cap.** Equipped with its Riemannian `MetricSpace`
structure `MetricSpace.ofRiemannianMetric`, `WithMetric (hf.metric V)` is a complete metric
space. -/
theorem completeSpace_withMetric_metricSpace :
    letI : MetricSpace (WithMetric (hf.metric V)) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
    CompleteSpace (WithMetric (hf.metric V)) :=
  hf.completeSpace_withMetric

/-- **Geodesic completeness of the standard cap.** Every maximal geodesic of `hf.metric V` on a
finite-dimensional real inner product space `V` is defined on all of `ℝ`. -/
theorem isGeodesicallyCompleteAt_withMetric (p : WithMetric (hf.metric V)) :
    Manifold.IsGeodesicallyCompleteAt 𝓘(ℝ, V) (WithMetric (hf.metric V)) p := by
  let _ : MetricSpace (WithMetric (hf.metric V)) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  have : CompleteSpace (WithMetric (hf.metric V)) := hf.completeSpace_withMetric_metricSpace
  exact Manifold.isGeodesicallyCompleteAt_of_completeSpace p

end Completeness

/-! ### Global sectional and scalar curvature of the standard cap -/

section Curvature

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
include hf

private theorem sectionalCurvature_withMetric_of_ne_zero {n : ℕ} [Fact (finrank ℝ V = n + 1)]
    {p : WithMetric (hf.metric V)} (hp : p.ofWithMetric ≠ 0) (X Y : TangentSpace 𝓘(ℝ, V) p) :
    letI : RiemannianBundle _ := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    ∃ (q : standardCapRadialDomain × sphere (0 : V) 1) (u v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) q),
      (q.1 : ℝ) = ‖p.ofWithMetric‖ ∧
      (LinearIndependent ℝ ![u, v] ↔ LinearIndependent ℝ ![X, Y]) ∧
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p X Y =
        (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
          (standardCapRadialDomain × sphere (0 : V) 1)).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) q u v := by
  let _ : RiemannianBundle _ := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  have hloc := hf.isLocalRiemannianIsometry_toWithMetric_polar (n := n) V
  set ψ : standardCapRadialDomain × sphere (0 : V) 1 → WithMetric (hf.metric V) :=
    fun z ↦ WithMetric.toWithMetric (hf.metric V) ((z.1 : ℝ) • (z.2 : V))
  obtain ⟨q, hq_norm, hψq⟩ : ∃ q : standardCapRadialDomain × sphere (0 : V) 1,
      (q.1 : ℝ) = ‖p.ofWithMetric‖ ∧ ψ q = p := by
    refine ⟨(radialSphereDiffeomorph (n := n) V).symm ⟨p.ofWithMetric, mem_puncturedSpace.2 hp⟩,
      by simp, ?_⟩
    have hcoe := congrArg Subtype.val ((radialSphereDiffeomorph (n := n) V).apply_symm_apply
      ⟨p.ofWithMetric, mem_puncturedSpace.2 hp⟩)
    rw [coe_radialSphereDiffeomorph_apply] at hcoe
    exact WithMetric.ext hcoe
  subst hψq
  obtain ⟨e, he⟩ := hloc.exists_linearIsometryEquiv_eq_mfderiv q
  obtain ⟨u, hu⟩ := (hloc.mfderiv_surjective q) X
  obtain ⟨v, hv⟩ := (hloc.mfderiv_surjective q) Y
  refine ⟨q, u, v, hq_norm, ?_, ?_⟩
  · have hcomp : ⇑e.toLinearEquiv.toLinearMap ∘ ![u, v] = ![X, Y] := by
      ext i; fin_cases i <;> simp [he, hu, hv]
    have hli := e.toLinearEquiv.toLinearMap.linearIndependent_iff (LinearEquiv.ker e.toLinearEquiv)
      (v := ![u, v])
    rw [hcomp] at hli; exact hli.symm
  · have hsec := hloc.sectionalCurvature_mfderiv q u v; rwa [hu, hv] at hsec

private theorem sectionalCurvature_withMetric_tip_limit
    {p₀ : WithMetric (hf.metric V)} (hp₀ : p₀.ofWithMetric = 0)
    {X Y : TangentSpace 𝓘(ℝ, V) p₀} (hXY : LinearIndependent ℝ ![X, Y])
    {s : Set (WithMetric (hf.metric V))} (hs : s ∈ 𝓝 p₀) {k : ℝ}
    (hk : ∀ q ∈ s, q.ofWithMetric ≠ 0 → ∀ u v : TangentSpace 𝓘(ℝ, V) q,
      LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) q u v = k) :
    (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p₀ X Y = k := by
  have hcard : 2 ≤ finrank ℝ V := by
    have h := hXY.fintype_card_le_finrank
    rwa [Fintype.card_fin, (tangentSpaceCastModel 𝓘(ℝ, V) p₀).toLinearEquiv.finrank_eq] at h
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (M := V) (by omega)
  have : Nontrivial (WithMetric (hf.metric V)) :=
    (WithMetric.equiv (hf.metric V)).surjective.nontrivial
  obtain ⟨u, hu, hu₀⟩ := FiberBundle.exists_contMDiff_section_eq 𝓘(ℝ, V) V ∞ X
  obtain ⟨v, hv, hv₀⟩ := FiberBundle.exists_contMDiff_section_eq 𝓘(ℝ, V) V ∞ Y
  have hcont :=
    ((leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).contMDiffAt_sectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) (n := (⊤ : ℕ∞)) (hu p₀) (hv p₀)
      (by rwa [hu₀, hv₀])).continuousAt
  have hdet_cont : Continuous fun q ↦
      inner ℝ (u q) (u q) * inner ℝ (v q) (v q) - inner ℝ (u q) (v q) ^ 2 :=
    ((hu.continuous.inner_bundle hu.continuous).mul
      (hv.continuous.inner_bundle hv.continuous)).sub
      ((hu.continuous.inner_bundle hv.continuous).pow 2)
  have hdet₀ :
      inner ℝ (u p₀) (u p₀) * inner ℝ (v p₀) (v p₀) - inner ℝ (u p₀) (v p₀) ^ 2 ≠ 0 := by
    rw [hu₀, hv₀, ← Matrix.real_det_gram_fin_two]
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hXY
  have hev : ∀ᶠ q in 𝓝[≠] p₀,
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) q (u q) (v q) = k := by
    filter_upwards [nhdsWithin_le_nhds (inter_mem hs (hdet_cont.continuousAt.eventually_ne hdet₀)),
      self_mem_nhdsWithin] with q ⟨hqs, hqdet⟩ hqne
    refine hk q hqs (fun h ↦ hqne (WithMetric.ext (h.trans hp₀.symm))) (u q) (v q)
      (Matrix.det_gram_ne_zero_iff_linearIndependent.mp ?_)
    rwa [Matrix.real_det_gram_fin_two]
  have : (𝓝[≠] p₀).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [closure_compl_singleton]; trivial)
  simpa [hu₀, hv₀] using tendsto_nhds_unique
    ((hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev) tendsto_const_nhds

/-- **Near the tip (including at `0`), the standard cap has constant sectional curvature
`1 / 4`.** -/
theorem exists_hasSectionalCurvatureAt_withMetric_round :
    ∃ r₀ > 0, ∀ p : WithMetric (hf.metric V), ‖p.ofWithMetric‖ < r₀ →
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).HasSectionalCurvatureAt
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p (1 / 4) := by
  rcases Nat.eq_zero_or_pos (finrank ℝ V) with hd0 | hdpos
  · refine ⟨1, one_pos, fun p _ ↦
      (leviCivitaConnection 𝓘(ℝ, V)
        (WithMetric (hf.metric V))).hasSectionalCurvatureAt_of_finrank_le_one
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p (1 / 4) ?_⟩
    rw [(tangentSpaceCastModel 𝓘(ℝ, V) p).toLinearEquiv.finrank_eq, hd0]
    exact Nat.zero_le 1
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hdpos.ne'
    let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
    obtain ⟨r₀, hr₀, hpunct⟩ :=
      hf.exists_hasSectionalCurvatureAt_puncturedMetric_round (n := n) (V := V)
    have haway : ∀ q : WithMetric (hf.metric V), ‖q.ofWithMetric‖ < r₀ → q.ofWithMetric ≠ 0 →
        ∀ X Y : TangentSpace 𝓘(ℝ, V) q, LinearIndependent ℝ ![X, Y] →
        (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) q X Y = 1 / 4 := by
      intro q hqr hq0 X Y hXY
      obtain ⟨z, u, v, hz, hli, hsec⟩ :=
        hf.sectionalCurvature_withMetric_of_ne_zero (n := n) hq0 X Y
      let _ : RiemannianBundle
        (fun w : standardCapRadialDomain × sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) w) :=
        ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
      exact hsec.trans ((hpunct z (hz.trans_lt hqr)).sectionalCurvature_eq u v (hli.2 hXY))
    refine ⟨r₀, hr₀, fun p hp ↦ (hasSectionalCurvatureAt_iff _ _ _ _).2 fun X Y hXY ↦ ?_⟩
    rcases eq_or_ne p.ofWithMetric 0 with hp0 | hp0
    · refine hf.sectionalCurvature_withMetric_tip_limit hp0 hXY
        (s := WithMetric.ofWithMetric ⁻¹' Metric.ball (0 : V) r₀) ?_
        fun q hq hq0 u v huv ↦ haway q (by simpa using hq) hq0 u v huv
      exact (Metric.isOpen_ball.preimage WithMetric.continuous_ofWithMetric).mem_nhds
        (by simp [hp0, hr₀])
    · exact haway p hp hp0 X Y hXY

/-- **Every tangent two-plane of the standard cap (including at the tip) has nonnegative sectional
curvature.** -/
theorem sectionalCurvature_withMetric_nonneg (p : WithMetric (hf.metric V))
    (X Y : TangentSpace 𝓘(ℝ, V) p) :
    0 ≤ (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p X Y := by
  by_cases hXY : LinearIndependent ℝ ![X, Y]
  · rcases eq_or_ne p.ofWithMetric 0 with hp0 | hp0
    · obtain ⟨r₀, hr₀, hround⟩ := hf.exists_hasSectionalCurvatureAt_withMetric_round (V := V)
      rw [(hround p (by simp [hp0, hr₀])).sectionalCurvature_eq X Y hXY]; norm_num
    · have hdpos : 0 < finrank ℝ V := by
        have h := hXY.fintype_card_le_finrank
        rw [Fintype.card_fin, (tangentSpaceCastModel 𝓘(ℝ, V) p).toLinearEquiv.finrank_eq] at h
        omega
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hdpos.ne'
      let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
      obtain ⟨z, u, v, -, -, hsec⟩ := hf.sectionalCurvature_withMetric_of_ne_zero (n := n) hp0 X Y
      rw [hsec]; exact hf.sectionalCurvature_puncturedMetric_nonneg (n := n) z u v
  · rw [sectionalCurvature_apply,
      not_not.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr hXY), div_zero]

private theorem scalarCurvature_metric_of_ne_zero {n : ℕ} [Fact (finrank ℝ V = n + 1)]
    {x : V} (hx : x ≠ 0) :
    (hf.metric V).scalarCurvature x =
      (hf.puncturedMetric (n := n) V).scalarCurvature
        ((radialSphereDiffeomorph (n := n) V).symm ⟨x, mem_puncturedSpace.2 hx⟩) := by
  rw [← (hf.metric V).scalarCurvature_restrictOpenTangentSpace (puncturedSpace V)
      ⟨x, mem_puncturedSpace.2 hx⟩,
    hf.puncturedMetric_eq_pullback (n := n) V,
    ContMDiffRiemannianMetric.scalarCurvature_pullback]; simp

private theorem scalarCurvature_metric_of_subsingleton [Subsingleton V] (x : V) :
    (hf.metric V).scalarCurvature x = 0 := by
  let _ : RiemannianBundle (fun z : V ↦ TangentSpace 𝓘(ℝ, V) z) :=
    ⟨(hf.metric V).toRiemannianMetric⟩
  have : Subsingleton (TangentSpace 𝓘(ℝ, V) x) :=
    (tangentSpaceCastModel 𝓘(ℝ, V) x).injective.subsingleton
  rw [ContMDiffRiemannianMetric.scalarCurvature_def, CovariantDerivative.scalarCurvature_apply,
    Subsingleton.elim (CovariantDerivative.ricciTensor _ x) 0, map_zero]

/-- **The standard cap metric has nonnegative scalar curvature everywhere on `V`**, in every
dimension. -/
theorem scalarCurvature_metric_nonneg (x : V) : 0 ≤ (hf.metric V).scalarCurvature x := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [hf.scalarCurvature_metric_of_subsingleton x]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := V)).ne'
    let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
    have hx : x ∈ closure ({0}ᶜ : Set V) := by rw [closure_compl_singleton]; trivial
    refine le_on_closure (fun y (hy : y ≠ 0) ↦ ?_) continuous_const.continuousOn
      (hf.metric V).continuous_scalarCurvature.continuousOn hx
    rw [hf.scalarCurvature_metric_of_ne_zero (n := n) hy]
    exact hf.scalarCurvature_puncturedMetric_nonneg (n := n) _

/-- **Near the tip (including at `0`), the standard cap metric on `V` has scalar curvature
`d (d - 1) / 4`** (`d = finrank ℝ V`), the scalar curvature of the round sphere of radius `2`. -/
theorem exists_scalarCurvature_metric_eq_round :
    ∃ r₀ > 0, ∀ x : V, ‖x‖ < r₀ →
      (hf.metric V).scalarCurvature x =
        (finrank ℝ V : ℝ) * ((finrank ℝ V : ℝ) - 1) / 4 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, one_pos, fun x _ ↦ ?_⟩
    rw [hf.scalarCurvature_metric_of_subsingleton x, finrank_zero_of_subsingleton]; norm_num
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := V)).ne'
    let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
    obtain ⟨r₀, hr₀, hround⟩ :=
      hf.exists_scalarCurvature_puncturedMetric_eq_round (n := n) (V := V)
    have haway : ∀ y : V, y ≠ 0 → ‖y‖ < r₀ →
        (hf.metric V).scalarCurvature y = (finrank ℝ V : ℝ) * ((finrank ℝ V : ℝ) - 1) / 4 := by
      intro y hy hyr
      rw [hf.scalarCurvature_metric_of_ne_zero (n := n) hy, hround _ (by simpa using hyr), hn]
      push_cast; ring
    refine ⟨r₀, hr₀, fun x hx ↦ ?_⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · have : (𝓝[≠] (0 : V)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
        rw [closure_compl_singleton]; trivial)
      have hev : ∀ᶠ y in 𝓝[≠] (0 : V), (hf.metric V).scalarCurvature y =
          (finrank ℝ V : ℝ) * ((finrank ℝ V : ℝ) - 1) / 4 := by
        filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : V) hr₀),
          self_mem_nhdsWithin] with y hyr hy0 using haway y hy0 (by simpa using hyr)
      exact tendsto_nhds_unique (((hf.metric V).continuous_scalarCurvature.continuousAt.tendsto
        |>.mono_left nhdsWithin_le_nhds).congr' hev) tendsto_const_nhds
    · exact haway x hx0 hx

/-- **On a sufficiently far cylindrical end (`R ≤ ‖x‖`), the standard cap metric on `V` has scalar
curvature `(d - 1) (d - 2) / 2`**, the scalar curvature of `ℝ × S^(d - 1)(√2)`. -/
theorem exists_scalarCurvature_metric_eq_cylinder :
    ∃ R > 0, ∀ x : V, R ≤ ‖x‖ →
      (hf.metric V).scalarCurvature x =
        ((finrank ℝ V : ℝ) - 1) * ((finrank ℝ V : ℝ) - 2) / 2 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨1, one_pos, fun x hx ↦ absurd (Subsingleton.elim x 0 ▸ hx) (by simp)⟩
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := V)).ne'
    let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
    obtain ⟨R, hR, hcyl⟩ := hf.exists_scalarCurvature_puncturedMetric_eq_cylinder (n := n) (V := V)
    refine ⟨R, hR, fun x hx ↦ ?_⟩
    rw [hf.scalarCurvature_metric_of_ne_zero (n := n) (norm_pos_iff.1 (hR.trans_le hx)),
      hcyl _ (by simpa using hx), hn]; push_cast; ring

/-- In dimension three, the standard cap metric has scalar curvature `3 / 2` near the tip (including
at `0`). -/
theorem exists_scalarCurvature_metric_eq_three_halves (hd : finrank ℝ V = 3) :
    ∃ r₀ > 0, ∀ x : V, ‖x‖ < r₀ → (hf.metric V).scalarCurvature x = 3 / 2 := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_scalarCurvature_metric_eq_round (V := V)
  exact ⟨r₀, hr₀, fun x hx ↦ by rw [h x hx, hd]; norm_num⟩

/-- In dimension three, the standard cap metric has scalar curvature `1` on its cylindrical end. -/
theorem exists_scalarCurvature_metric_eq_one_of_finrank_eq_three (hd : finrank ℝ V = 3) :
    ∃ R > 0, ∀ x : V, R ≤ ‖x‖ → (hf.metric V).scalarCurvature x = 1 := by
  obtain ⟨R, hR, h⟩ := hf.exists_scalarCurvature_metric_eq_cylinder (V := V)
  exact ⟨R, hR, fun x hx ↦ by rw [h x hx, hd]; norm_num⟩

end Curvature

end IsStandardCapProfile

/-- **Existence of a complete smooth three-dimensional standard cap metric.** On any
three-dimensional real inner product space `V` (in particular `EuclideanSpace ℝ (Fin 3)`), there
exists a standard cap profile `f` whose associated smooth Riemannian metric `hf.metric V` is
complete, has nonnegative sectional and scalar curvature everywhere, has constant sectional
curvature `1 / 4` near the tip `0`, and has scalar curvature `1` on a cylindrical end `R ≤ ‖x‖`. -/
theorem exists_standardCapMetric (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (hd : finrank ℝ V = 3) :
    ∃ (f : ℝ → ℝ) (hf : IsStandardCapProfile f),
      (letI : MetricSpace (WithMetric (hf.metric V)) :=
        MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V));
      CompleteSpace (WithMetric (hf.metric V))) ∧
      (∀ p : WithMetric (hf.metric V), ∀ X Y : TangentSpace 𝓘(ℝ, V) p,
        0 ≤ (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p X Y) ∧
      (∃ r₀ > 0, ∀ p : WithMetric (hf.metric V), ‖p.ofWithMetric‖ < r₀ →
        (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).HasSectionalCurvatureAt
          (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p (1 / 4)) ∧
      (∀ x : V, 0 ≤ (hf.metric V).scalarCurvature x) ∧
      (∃ R > 0, ∀ x : V, R ≤ ‖x‖ → (hf.metric V).scalarCurvature x = 1) := by
  obtain ⟨f, hf⟩ := exists_isStandardCapProfile
  exact ⟨f, hf, hf.completeSpace_withMetric_metricSpace,
    hf.sectionalCurvature_withMetric_nonneg,
    hf.exists_hasSectionalCurvatureAt_withMetric_round, hf.scalarCurvature_metric_nonneg,
    hf.exists_scalarCurvature_metric_eq_one_of_finrank_eq_three hd⟩

/-! ### Tip-obstruction theorem -/

section TipObstruction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem continuous_inner_const_vector
    (g : ContinuousRiemannianMetric V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x)) (w : V) :
    Continuous fun x : V ↦
      g.inner x ((NormedSpace.fromTangentSpace x).symm w)
        ((NormedSpace.fromTangentSpace x).symm w) := by
  let _ : RiemannianBundle (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) :=
    Bundle.instIsContinuousRiemannianBundle g
  let σ : Π x : V, TangentSpace 𝓘(ℝ, V) x := fun x ↦ (NormedSpace.fromTangentSpace x).symm w
  have hσ : CMDiff ∞ (T% σ) :=
    (contMDiff_vectorSpace_iff_contDiff (n := ∞)).2 contDiff_const
  exact hσ.continuous.inner_bundle hσ.continuous

/-- **Tip-obstruction theorem (right-limit form).** Let `V` be a real inner product space of
dimension `n + 1` with `0 < n` (`dim V ≥ 2`), and let `g` be a continuous Riemannian metric on `V`.
If on concentric spheres `u ↦ r • u` of small positive radius `r`, `g` restricts to `f(r)² g_(Sⁿ)`,
then `|f(r)| → 0` as `r → 0⁺`. The hypothesis `0 < n` cannot be dropped: when `n = 0` (`V = ℝ`),
`S⁰` is discrete (`T_u S⁰ = 0`) and `f = 1` describes the flat metric `dx²` across `0`. -/
theorem tendsto_abs_of_spherical_pullback {n : ℕ} [Fact (finrank ℝ V = n + 1)] (hn : 0 < n)
    (g : ContinuousRiemannianMetric V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x)) {f : ℝ → ℝ}
    (hpull : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ (u : sphere (0 : V) 1) (v : TangentSpace (𝓡 n) u),
      g.inner (r • (u : V))
        (mfderiv (𝓡 n) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 ↦ r • (q : V)) u v)
        (mfderiv (𝓡 n) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 ↦ r • (q : V)) u v) =
        f r ^ 2 * (sphereRoundMetric (E := V)).inner u v v) :
    Tendsto (fun r ↦ |f r|) (𝓝[>] 0) (𝓝 0) := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (M := V) (by
    rw [Fact.out (p := finrank ℝ V = n + 1)]; omega)
  obtain ⟨u⟩ : Nonempty (sphere (0 : V) 1) :=
    Set.Nonempty.to_subtype (NormedSpace.sphere_nonempty.2 zero_le_one)
  let v : TangentSpace (𝓡 n) u := EuclideanSpace.single ⟨0, hn⟩ 1
  have hv : v ≠ 0 := by
    change PiLp.single 2 (⟨0, hn⟩ : Fin n) (1 : ℝ) ≠ (0 : EuclideanSpace ℝ (Fin n))
    rw [ne_eq, PiLp.single_eq_zero_iff]; exact one_ne_zero
  have hpos : 0 < (sphereRoundMetric (E := V)).inner u v v :=
    (sphereRoundMetric (E := V)).pos u v hv
  set w : V := mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) u v
  have heq : (fun r : ℝ ↦ f r ^ 2) =ᶠ[𝓝[>] (0 : ℝ)] fun r : ℝ ↦
      r ^ 2 * g.inner (r • (u : V)) ((NormedSpace.fromTangentSpace (r • (u : V))).symm w)
        ((NormedSpace.fromTangentSpace (r • (u : V))).symm w) /
        (sphereRoundMetric (E := V)).inner u v v := by
    filter_upwards [hpull] with r hr
    have hdf : mfderiv (𝓡 n) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 ↦ r • (q : V)) u v =
        r • (NormedSpace.fromTangentSpace (r • (u : V))).symm w := by
      apply (NormedSpace.fromTangentSpace (r • (u : V))).injective
      change mvfderiv (𝓡 n) (r • ((↑) : sphere (0 : V) 1 → V)) u v = _
      rw [mvfderiv_const_smul_field, _root_.smul_apply, map_smul,
        ContinuousLinearEquiv.apply_symm_apply]
    have hpull_r := hr u v
    rw [hdf, map_smul, map_smul, _root_.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← sq] at hpull_r
    exact (eq_div_iff hpos.ne').2 hpull_r.symm
  have hcont_g : Continuous fun r : ℝ ↦
      g.inner (r • (u : V)) ((NormedSpace.fromTangentSpace (r • (u : V))).symm w)
        ((NormedSpace.fromTangentSpace (r • (u : V))).symm w) :=
    (continuous_inner_const_vector g w).comp (continuous_id.smul continuous_const)
  have hlim : Tendsto (fun r : ℝ ↦
      r ^ 2 * g.inner (r • (u : V)) ((NormedSpace.fromTangentSpace (r • (u : V))).symm w)
        ((NormedSpace.fromTangentSpace (r • (u : V))).symm w) /
        (sphereRoundMetric (E := V)).inner u v v) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((((continuous_pow 2).mul hcont_g).div_const _).continuousAt (x := 0)).tendsto
      |>.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun r : ℝ ↦ f r ^ 2) (𝓝[>] 0) (𝓝 0) := hlim.congr' heq.symm
  simpa only [Real.sqrt_zero] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp hsq).congr fun r ↦ Real.sqrt_sq_eq_abs (f r)

/-- **Tip-obstruction theorem.** If `f : ℝ → ℝ` is right-continuous at `0` (in particular, if `f`
is continuous at `0`) and a continuous Riemannian metric `g` on `V` (`dim V = n + 1`, `0 < n`)
restricts on concentric spheres `u ↦ r • u` of small positive radius `r` to `f(r)² g_(Sⁿ)`, then
`f 0 = 0`; in particular `¬ 0 < f 0`. -/
theorem eq_zero_of_spherical_pullback {n : ℕ} [Fact (finrank ℝ V = n + 1)] (hn : 0 < n)
    (g : ContinuousRiemannianMetric V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x)) {f : ℝ → ℝ}
    (hf : ContinuousWithinAt f (Ici 0) 0)
    (hpull : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ (u : sphere (0 : V) 1) (v : TangentSpace (𝓡 n) u),
      g.inner (r • (u : V))
        (mfderiv (𝓡 n) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 ↦ r • (q : V)) u v)
        (mfderiv (𝓡 n) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 ↦ r • (q : V)) u v) =
        f r ^ 2 * (sphereRoundMetric (E := V)).inner u v v) :
    f 0 = 0 := by
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsGT_neBot (0 : ℝ)
  have h1 : Tendsto (fun r ↦ |f r|) (𝓝[>] 0) (𝓝 |f 0|) :=
    (continuous_abs.continuousAt.tendsto.comp hf).mono_left
      (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  exact abs_eq_zero.1 (tendsto_nhds_unique h1 (tendsto_abs_of_spherical_pullback hn g hpull))

end TipObstruction

end TauCeti
