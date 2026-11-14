/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Comparison
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Metric

/-!
# Rauch and Jacobian comparison for the Riemannian exponential map

Let `v ∈ T_p M` lie in the natural domain of the Riemannian exponential map `exp_p`. Along the
radial geodesic `γ(t) = exp_p (t • v)`, the field `t ↦ d(exp_p)_{t • v} (t • w)` is the Jacobi
field with initial value `0` and initial covariant derivative `w`. When `w` is perpendicular to
`v`, Rauch comparison along `γ` bounds `‖d(exp_p)_v w‖` from below by
`curvatureSine (κ * ‖v‖ ^ 2) 1 * ‖w‖` whenever every radial plane along `γ` has sectional curvature
at most `κ` and `‖v‖ < π / √κ` (when `κ > 0`).

Combining this angular bound with Gauss's lemma yields three geometric consequences on `expDomain`
without any completeness or global curvature hypothesis:

1. **Nonsingularity before the model conjugate radius:** `d(exp_p)_v` is injective, so `exp_p` is a
   smooth local diffeomorphism at `v`. When `exp_p` is injective on an open tangent ball
   `ball 0 r ⊆ expDomain` with `r ≤ π / √κ` (for `κ > 0`), that ball is a normal domain.
2. **Exponential Jacobian comparison:** splitting `T_p M` into `ℝ ∙ v` and `(ℝ ∙ v)ᗮ`, Gauss's
   lemma makes `d(exp_p)_v` preserve radial length and radial-angular orthogonality, so the
   geometric Jacobian `normDet` of `d(exp_p)_v` is bounded below by
   `curvatureSine (κ * ‖v‖ ^ 2) 1 ^ (finrank ℝ E - 1)` (equivalently
   `(curvatureSine κ ‖v‖ / ‖v‖) ^ (finrank ℝ E - 1)` when `v ≠ 0`).
3. **Constant-curvature equality:** when radial planes have constant sectional curvature `κ`, the
   Jacobian equals `|curvatureSine (κ * ‖v‖ ^ 2) 1| ^ (finrank ℝ E - 1)` everywhere on `expDomain`.

## Main results

* `TauCeti.Manifold.curvatureSine_mul_norm_le_norm_mfderiv_riemannianExp`,
  `TauCeti.Manifold.div_mul_norm_le_norm_mfderiv_riemannianExp`: angular Rauch lower bounds on
  `‖d(exp_p)_v w‖` for `⟪w, v⟫ = 0`.
* `TauCeti.Manifold.injective_mfderiv_riemannianExp_of_sectionalCurvature_le`,
  `TauCeti.Manifold.isLocalDiffeomorphAt_riemannianExp_of_sectionalCurvature_le`: nonsingularity and
  local invertibility of `exp_p` under a radial upper sectional curvature bound.
* `TauCeti.Manifold.isNormalDomain_ball_of_sectionalCurvature_le`: an injective tangent ball of
  radius `r ≤ π / √κ` (when `κ > 0`) under radial sectional curvature `≤ κ` is a normal domain.
* `TauCeti.Manifold.pow_le_normDet_mfderiv_riemannianExp`,
  `TauCeti.Manifold.div_pow_le_normDet_mfderiv_riemannianExp`: lower bounds on the Jacobian
  `normDet` of `d(exp_p)_v`.
* `TauCeti.Manifold.normDet_mfderiv_riemannianExp_of_hasSectionalCurvatureAt`: exact Jacobian of
  `d(exp_p)_v` in constant sectional curvature.

## References

* K.-K. Kwong, *Quantitative comparison theorems in Riemannian and Kähler geometry*, Theorem 10(2).
* J.-H. Eschenburg, *Comparison Theorems in Riemannian Geometry*, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 10–11.
-/

public section

open Bundle CovariantDerivative Real Set
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v : TangentSpace I p} {κ r : ℝ}

/-! ### Angular Rauch lower bound for the exponential differential -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Translate the radius bound `0 < κ → ‖v‖ < π / √κ` into the rescaled parameter bound
`0 < κ * ‖v‖ ^ 2 → 1 < π / √(κ * ‖v‖ ^ 2)` on `[0, 1]`. -/
private theorem one_lt_pi_div_sqrt_mul_norm_sq (hbound : 0 < κ → ‖v‖ < π / √κ)
    (hpos : 0 < κ * ‖v‖ ^ 2) :
    (1 : ℝ) < π / √(κ * ‖v‖ ^ 2) := by
  have hv2 : 0 < ‖v‖ ^ 2 := by
    by_contra hle
    have h0 : ‖v‖ ^ 2 = 0 := le_antisymm (not_lt.mp hle) (sq_nonneg _)
    rw [h0, mul_zero] at hpos
    exact lt_irrefl 0 hpos
  have hv : 0 < ‖v‖ := (norm_nonneg v).lt_of_ne' fun h0 ↦ by simp [h0] at hv2
  have hκ : 0 < κ := pos_of_mul_pos_left hpos hv2.le
  rw [Real.sqrt_mul hκ.le, Real.sqrt_sq hv.le,
    one_lt_div (mul_pos (Real.sqrt_pos.2 hκ) hv), mul_comm]
  exact (lt_div_iff₀ (Real.sqrt_pos.2 hκ)).mp (hbound hκ)

/-- **Angular Rauch lower bound for `d(exp_p)_v`**, at arbitrary initial velocity `v ∈ expDomain`
(including `v = 0`). If every plane containing the radial velocity along `(0, 1)` has sectional
curvature at most `κ`, `‖v‖ < π / √κ` when `κ > 0`, and `⟪w, v⟫ = 0`, then
`curvatureSine (κ * ‖v‖ ^ 2) 1 * ‖w‖ ≤ ‖d(exp_p)_v w‖`. -/
theorem curvatureSine_mul_norm_le_norm_mfderiv_riemannianExp
    (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ u : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ
        ![u, mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v] →
        (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
          (riemannianExp I M p (t • v)) u
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v) ≤ κ)
    (hbound : 0 < κ → ‖v‖ < π / √κ)
    (w : TangentSpace I p) (hw : ⟪w, v⟫_ℝ = 0) :
    curvatureSine (κ * ‖v‖ ^ 2) 1 * ‖w‖ ≤
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ := by
  have hsub : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.1 hv)
  have hJ := isJacobiFieldOn_mfderiv_riemannianExp (I := I) p v w
  have hvel0 : curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v))
      (geodesicInterval I M p v) 0 = v := by
    rw [curveVelocityWithin_of_mem_nhds
        (isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval),
      curveVelocity_riemannianExp_smul_zero]
  have hK' : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ u : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ ![u, curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v))
        (geodesicInterval I M p v) t] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (riemannianExp I M p (t • v)) u
        (curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v))
          (geodesicInterval I M p v) t) ≤ κ := by
    intro t ht
    have ht_mem : t ∈ geodesicInterval I M p v := hsub (Ioo_subset_Icc_self ht)
    have hvelt : curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v))
        (geodesicInterval I M p v) t =
        mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v := by
      rw [curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds ht_mem),
        curveVelocity_riemannianExp_smul (mem_geodesicInterval_iff_smul_mem_expDomain.mp ht_mem)]
    rw [hvelt]
    exact hK t ht
  have hrauch := hJ.curvatureSine_mul_norm_alongCurveWithin_le_norm_of_sectionalCurvature_le
    zero_le_one hsub
    (by rw [zero_smul ℝ w]; exact (mfderiv 𝓘(ℝ, TangentSpace I p) I
      (riemannianExp I M p) (0 • v)).map_zero)
    (by rw [alongCurveWithin_mfderiv_riemannianExp_zero, hvel0, zero_smul, riemannianExp_zero];
        exact hw)
    hK'
    (by
      rw [hvel0, zero_smul, riemannianExp_zero, sub_zero]
      exact one_lt_pi_div_sqrt_mul_norm_sq hbound)
  -- At time `0`, `exp_p (0 • v) = p` transports the fibre metric back to `TangentSpace I p`.
  rw [alongCurveWithin_mfderiv_riemannianExp_zero, hvel0, sub_zero, zero_smul,
    riemannianExp_zero, one_smul, one_smul] at hrauch
  exact hrauch

/-- **Angular Rauch lower bound for `d(exp_p)_v`**, quotient form for `v ≠ 0`:
`(curvatureSine κ ‖v‖ / ‖v‖) * ‖w‖ ≤ ‖d(exp_p)_v w‖` for `⟪w, v⟫ = 0`. -/
theorem div_mul_norm_le_norm_mfderiv_riemannianExp
    (hv : v ∈ expDomain I M p) (hv0 : v ≠ 0)
    (hK : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ u : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ
        ![u, mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v] →
        (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
          (riemannianExp I M p (t • v)) u
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v) ≤ κ)
    (hbound : 0 < κ → ‖v‖ < π / √κ)
    (w : TangentSpace I p) (hw : ⟪w, v⟫_ℝ = 0) :
    curvatureSine κ ‖v‖ / ‖v‖ * ‖w‖ ≤
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ := by
  rw [← curvatureSine_mul_sq_one κ (norm_ne_zero_iff.mpr hv0)]
  exact curvatureSine_mul_norm_le_norm_mfderiv_riemannianExp hv hK hbound w hw

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
private theorem curvatureSine_mul_norm_sq_one_pos (hbound : 0 < κ → ‖v‖ < π / √κ) :
    0 < curvatureSine (κ * ‖v‖ ^ 2) 1 := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  · have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    rw [curvatureSine_mul_sq_one κ hpos.ne']
    exact div_pos (curvatureSine_pos hpos hbound) hpos

/-! ### Nonsingularity, local diffeomorphism, and normal-ball criterion -/

/-- **Nonsingularity of `exp_p` before the model conjugate radius.** Under radial sectional
curvature at most `κ` along `(0, 1)` and `‖v‖ < π / √κ` (when `κ > 0`), the differential
`d(exp_p)_v` is injective. -/
theorem injective_mfderiv_riemannianExp_of_sectionalCurvature_le
    (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ u : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ
        ![u, mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v] →
        (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
          (riemannianExp I M p (t • v)) u
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v) ≤ κ)
    (hbound : 0 < κ → ‖v‖ < π / √κ) :
    Function.Injective (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v) := by
  let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p v) :=
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
  -- Read `T_v (T_p M)` as `T_p M` so linearity and inner products use the tangent fibre at `p`.
  change Function.Injective L
  refine (injective_iff_map_eq_zero L).2 fun w hw ↦ ?_
  have horth : ⟪w, v⟫_ℝ = 0 := by
    rw [real_inner_comm, ← inner_mfderiv_riemannianExp_radial hv]
    -- Re-express `mfderiv ... v` as `L` across the definitional domain `T_v (T_p M) = T_p M`.
    change ⟪L v, L w⟫_ℝ = 0
    rw [hw, inner_zero_right]
  have hle : curvatureSine (κ * ‖v‖ ^ 2) 1 * ‖w‖ ≤ 0 := by
    have hr := curvatureSine_mul_norm_le_norm_mfderiv_riemannianExp hv hK hbound w horth
    -- Re-express `mfderiv ... v w` as `L w` so `hw : L w = 0` applies.
    change curvatureSine (κ * ‖v‖ ^ 2) 1 * ‖w‖ ≤ ‖L w‖ at hr
    simpa [hw] using hr
  have hc : 0 < curvatureSine (κ * ‖v‖ ^ 2) 1 := curvatureSine_mul_norm_sq_one_pos hbound
  exact norm_le_zero_iff.mp (nonpos_of_mul_nonpos_right hle hc)

/-- Under radial sectional curvature at most `κ` along `(0, 1)` and `‖v‖ < π / √κ` (when `κ > 0`),
`exp_p` is a smooth local diffeomorphism at `v`. -/
theorem isLocalDiffeomorphAt_riemannianExp_of_sectionalCurvature_le
    (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ u : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ
        ![u, mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v] →
        (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
          (riemannianExp I M p (t • v)) u
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v) ≤ κ)
    (hbound : 0 < κ → ‖v‖ < π / √κ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) v := by
  have hinj := injective_mfderiv_riemannianExp_of_sectionalCurvature_le hv hK hbound
  let e := (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).toLinearMap
    |>.linearEquivOfInjective hinj (by simp [TauCeti.finrank_tangentSpace])
  exact isLocalDiffeomorphAt_of_mfderiv_eq (contMDiffOn_riemannianExp (I := I) p)
    (isOpen_expDomain (I := I) p) hv BoundarylessManifold.isInteriorPoint (by simp)
    (e := e.toContinuousLinearEquiv) (by ext; simp [e])

/-- **Normal-ball criterion under an upper sectional curvature bound.** Let `0 < r`, with
`r ≤ π / √κ` when `κ > 0`. If `Metric.ball 0 r ⊆ expDomain I M p`, `exp_p` is injective on
`Metric.ball 0 r`, and radial planes along every ray in `Metric.ball 0 r` have sectional curvature
at most `κ`, then `Metric.ball 0 r` is a normal domain at `p`. Notice `r = π / √κ` is included
because every vector in the open ball satisfies `‖v‖ < r ≤ π / √κ`. -/
theorem isNormalDomain_ball_of_sectionalCurvature_le
    (hr : 0 < r) (hbound : 0 < κ → r ≤ π / √κ)
    (hsub : Metric.ball (0 : TangentSpace I p) r ⊆ expDomain I M p)
    (hinj : InjOn (riemannianExp I M p) (Metric.ball 0 r))
    (hK : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ t ∈ Ioo (0 : ℝ) 1,
      ∀ u : TangentSpace I (riemannianExp I M p (t • v)),
        LinearIndependent ℝ
          ![u, mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v] →
          (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
            (riemannianExp I M p (t • v)) u
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v) ≤ κ) :
    IsNormalDomain I M p (Metric.ball 0 r) where
  isOpen := Metric.isOpen_ball
  zero_mem := Metric.mem_ball_self hr
  starConvex := (convex_ball (0 : TangentSpace I p) r).starConvex (Metric.mem_ball_self hr)
  subset_expDomain := hsub
  injOn := hinj
  isLocalDiffeomorphOn w := isLocalDiffeomorphAt_riemannianExp_of_sectionalCurvature_le
    (hsub w.2) (hK w.1 w.2) fun hκ ↦ (mem_ball_zero_iff.mp w.2).trans_le (hbound hκ)

/-! ### Exponential Jacobian comparison and constant-curvature equality -/

omit [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The orthogonal complement of a nonzero tangent vector at `p` has dimension
`finrank ℝ E - 1`. -/
private theorem finrank_orthogonal_span_tangent {v : TangentSpace I p} (hv0 : v ≠ 0) :
    Module.finrank ℝ (ℝ ∙ v)ᗮ = Module.finrank ℝ E - 1 := by
  have hsum : Module.finrank ℝ (ℝ ∙ v) + Module.finrank ℝ (ℝ ∙ v)ᗮ = Module.finrank ℝ E := by
    simpa only [TauCeti.finrank_tangentSpace] using (ℝ ∙ v).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton (K := ℝ) hv0] at hsum
  omega

/-- Split the `normDet` of `d(exp_p)_v` at a nonzero `v ∈ expDomain` into its restriction to
`(ℝ ∙ v)ᗮ` via Gauss's lemma. -/
private theorem normDet_mfderiv_riemannianExp_eq_orthogonal
    (hv : v ∈ expDomain I M p) (hv0 : v ≠ 0) :
    LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).toLinearMap =
      LinearMap.normDet
        (((mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v :
          TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p v)).toLinearMap) ∘ₗ
          (ℝ ∙ v)ᗮ.subtype) := by
  let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p v) :=
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
  have horth : ∀ w ∈ (ℝ ∙ v)ᗮ, ⟪L v, L w⟫_ℝ = 0 := by
    intro w hw
    have hvw : ⟪v, w⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
    exact (inner_mfderiv_riemannianExp_radial hv).trans hvw
  have hrad : ‖L.toLinearMap v‖ / ‖v‖ = 1 := by
    have hn : ‖L v‖ = ‖v‖ := norm_mfderiv_riemannianExp_radial hv
    simpa only [ContinuousLinearMap.coe_coe, hn] using div_self (norm_ne_zero_iff.mpr hv0)
  -- Read `T_v (T_p M)` as `T_p M` so `LinearMap.normDet` acts on `L.toLinearMap`.
  change L.toLinearMap.normDet = (L.toLinearMap ∘ₗ (ℝ ∙ v)ᗮ.subtype).normDet
  rw [L.toLinearMap.normDet_eq_div_mul_normDet_orthogonal hv0 horth, hrad, one_mul]

/-- At the origin of `T_p M`, the differential of `exp_p` is the identity, so its `normDet` is
`1`. -/
@[simp]
theorem normDet_mfderiv_riemannianExp_zero (p : M) :
    LinearMap.normDet (U := TangentSpace I p)
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0).toLinearMap = 1 := by
  -- Read `T_0 (T_p M)` as `T_p M` so `LinearMap.normDet` and `Matrix.gram` share the domain type.
  let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p 0) :=
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0
  let b := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hsq := L.toLinearMap.normDet_sq_eq_det_gram b
  simp only [RCLike.ofReal_real_eq_id, id_eq, ContinuousLinearMap.coe_coe] at hsq
  have hgram : Matrix.gram ℝ (fun i ↦ L (b i)) = 1 := by
    ext i j
    -- Unfold `L` back to `mfderiv` across `T_0 (T_p M) = T_p M` so
    -- `mfderiv_riemannianExp_apply_zero` matches.
    change ⟪mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 (b i),
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 (b j)⟫_ℝ = _
    rw [mfderiv_riemannianExp_apply_zero, mfderiv_riemannianExp_apply_zero,
      riemannianExp_zero, orthonormal_iff_ite.mp b.orthonormal i j, Matrix.one_apply]
  rw [hgram, Matrix.det_one] at hsq
  -- Re-express the target `normDet` in terms of `L` across `T_0 (T_p M) = T_p M`.
  change L.toLinearMap.normDet = 1
  exact (sq_eq_sq₀ L.toLinearMap.normDet_nonneg zero_le_one).mp (by simpa using hsq)

/-- **Exponential Jacobian comparison** (at arbitrary `v ∈ expDomain`, including `v = 0`): under
radial sectional curvature at most `κ` along `(0, 1)` and `‖v‖ < π / √κ` (when `κ > 0`),
`curvatureSine (κ * ‖v‖ ^ 2) 1 ^ (finrank ℝ E - 1) ≤ (d(exp_p)_v).normDet`. -/
theorem pow_le_normDet_mfderiv_riemannianExp
    (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ u : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ
        ![u, mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v] →
        (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
          (riemannianExp I M p (t • v)) u
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v) ≤ κ)
    (hbound : 0 < κ → ‖v‖ < π / √κ) :
    curvatureSine (κ * ‖v‖ ^ 2) 1 ^ (Module.finrank ℝ E - 1) ≤
      LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).toLinearMap := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp [normDet_mfderiv_riemannianExp_zero]
  · rw [normDet_mfderiv_riemannianExp_eq_orthogonal hv hv0, ← finrank_orthogonal_span_tangent hv0]
    let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p v) :=
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
    refine (L.toLinearMap ∘ₗ (ℝ ∙ v)ᗮ.subtype).pow_finrank_le_normDet_of_norm_le
      (curvatureSine_mul_norm_sq_one_pos hbound).le fun w ↦ ?_
    -- Subtype norm and linear-map application coerce definitionally to `TangentSpace I p`.
    change curvatureSine (κ * ‖v‖ ^ 2) 1 * ‖(w : TangentSpace I p)‖ ≤
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w.1‖
    exact curvatureSine_mul_norm_le_norm_mfderiv_riemannianExp hv hK hbound w.1
      (Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.2)

/-- **Exponential Jacobian comparison**, quotient form for `v ≠ 0`:
`(curvatureSine κ ‖v‖ / ‖v‖) ^ (finrank ℝ E - 1) ≤ (d(exp_p)_v).normDet`. -/
theorem div_pow_le_normDet_mfderiv_riemannianExp
    (hv : v ∈ expDomain I M p) (hv0 : v ≠ 0)
    (hK : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ u : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ
        ![u, mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v] →
        (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
          (riemannianExp I M p (t • v)) u
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v) ≤ κ)
    (hbound : 0 < κ → ‖v‖ < π / √κ) :
    (curvatureSine κ ‖v‖ / ‖v‖) ^ (Module.finrank ℝ E - 1) ≤
      LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).toLinearMap := by
  rw [← curvatureSine_mul_sq_one κ (norm_ne_zero_iff.mpr hv0)]
  exact pow_le_normDet_mfderiv_riemannianExp hv hK hbound

/-- **Exact exponential Jacobian in constant sectional curvature.** Along a radial segment of
constant sectional curvature `κ` in `expDomain I M p`, the Jacobian `normDet` of `d(exp_p)_v` is
`|curvatureSine (κ * ‖v‖ ^ 2) 1| ^ (finrank ℝ E - 1)` (valid even at conjugate vectors). -/
theorem normDet_mfderiv_riemannianExp_of_hasSectionalCurvatureAt
    (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (t • v)) κ) :
    LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).toLinearMap =
      |curvatureSine (κ * ‖v‖ ^ 2) 1| ^ (Module.finrank ℝ E - 1) := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp [normDet_mfderiv_riemannianExp_zero]
  · rw [normDet_mfderiv_riemannianExp_eq_orthogonal hv hv0, ← finrank_orthogonal_span_tangent hv0]
    let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p v) :=
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
    refine (L.toLinearMap ∘ₗ (ℝ ∙ v)ᗮ.subtype).normDet_eq_pow_finrank_of_norm_eq fun w ↦ ?_
    -- Subtype norm and linear-map application coerce definitionally to `TangentSpace I p`.
    change ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w.1‖ =
      |curvatureSine (κ * ‖v‖ ^ 2) 1| * ‖(w : TangentSpace I p)‖
    exact norm_mfderiv_riemannianExp_of_inner_eq_zero_of_hasSectionalCurvatureAt hv hK w.1
      (Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.2)

end TauCeti.Manifold
