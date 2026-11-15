/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Compact
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InjectivityRadius.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InjectivityRadius.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Conjugate.ConstantCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Metric
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Geodesic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Radius

/-!
# The injectivity radius of the round sphere

This file computes the pointwise and global injectivity radius of the unit `n`-sphere
`sphere (0 : E) 1` (`finrank ℝ E = n + 1`) for its native round metric, as well as for the round
sphere of radius `r > 0` (`sphereRoundMetricOfRadius r hr`), and establishes the antipodal
sharpness phenomena at distance `π`.

* In dimension `n = 0`, the zero-sphere consists of two isolated points with zero-dimensional
  tangent spaces, so `inj(p) = ⊤` and `inj(S⁰) = ⊤`.
* For every `n : ℕ` and `p : Sⁿ`, the open tangent ball `Metric.ball 0 π` is a normal domain:
  constant sectional curvature `1` keeps `curvatureSine (‖v‖ ^ 2) 1 ≠ 0` on `‖v‖ < π`, making
  `d(exp_p)_v` injective and hence a local diffeomorphism, while the explicit formula
  `exp_p v = cos ‖v‖ • p + (sin ‖v‖ / ‖v‖) • dι_p v` makes `exp_p` injective on `Metric.ball 0 π`.
* For `1 ≤ n`, every tangent vector `v` of norm `π` satisfies `exp_p v = -p`. Choosing a unit
  tangent vector `u` gives distinct opposite vectors `π • u ≠ -(π • u)` colliding at `-p`, forcing
  `inj(p) ≤ π` and hence `inj(p) = inj(Sⁿ) = ENNReal.ofReal π`.
* Along any radial geodesic `t ↦ exp_p (t • v)` with `‖v‖ = π`, the antipodal parameter `1` has
  conjugate multiplicity `n - 1`: on `S¹` (`n = 1`) there are no conjugate points and `inj(S¹) = π`
  is obstructed purely by antipodal geodesic collision, whereas for `2 ≤ n` the antipode `-p` is
  simultaneously a conjugate point of multiplicity `n - 1` and a collision point of distinct
  minimizing geodesics of length `riemannianEDist (𝓡 n) p (-p) = ENNReal.ofReal π`.
* Rescaling the round metric to radius `r > 0` (`r²` times the unit round metric) scales both
  `inj(p)` and `inj(Sⁿ(r))` to `ENNReal.ofReal (r * π)` when `1 ≤ n` (for instance, multiplying the
  metric by `4`, i.e. `r = 2`, gives injectivity radius `2 * π`).

## Main results

* `TauCeti.expDomain_sphere`, `TauCeti.geodesicInterval_sphere`: completeness of `Sⁿ` without an
  explicit `FiniteDimensional` or `CompactSpace` hypothesis beyond `[Fact (finrank ℝ E = n + 1)]`.
* `TauCeti.injectivityRadiusAt_sphere_zero`, `TauCeti.injectivityRadius_sphere_zero`:
  `inj(p) = ⊤` and `inj(S⁰) = ⊤` in dimension zero.
* `TauCeti.isNormalDomain_ball_sphere_pi`: `Metric.ball 0 Real.pi` is a normal domain at every
  point of `Sⁿ` for every `n : ℕ`.
* `TauCeti.injectivityRadiusAt_sphere_of_one_le`, `TauCeti.injectivityRadius_sphere_of_one_le`:
  `inj(p) = ENNReal.ofReal Real.pi` and `inj(Sⁿ) = ENNReal.ofReal Real.pi` for `1 ≤ n`.
* `TauCeti.injectivityRadiusAt_withMetric_sphereRoundMetricOfRadius`,
  `TauCeti.injectivityRadius_withMetric_sphereRoundMetricOfRadius`,
  `TauCeti.injectivityRadiusAt_sphereRoundMetricOfRadius`,
  `TauCeti.injectivityRadius_sphereRoundMetricOfRadius`: `inj = ENNReal.ofReal (r * Real.pi)` for
  the round sphere of radius `r > 0` (`1 ≤ n`).
* `TauCeti.conjugateMultiplicity_sphere_of_norm_eq_pi`,
  `TauCeti.riemannianEDist_sphere_neg_self`,
  `TauCeti.exists_two_minimizing_geodesics_sphere_antipode`: antipodal conjugate multiplicity
  `n - 1` and non-uniqueness of minimizing geodesics at distance `π` when `1 ≤ n`.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed., World Scientific (2007),
  Definition 4.1.23 and Example 4.1.25, pp. 151–152.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapters 6
  and 10.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapters 5 and 13.
-/

public section

open Bundle CovariantDerivative Function Manifold Metric Module Set TauCeti.Manifold
open scoped ContDiff ENNReal InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-! ### Completeness and ambient inner products of `riemannianExp` -/

/-- The exponential map of the round unit sphere is defined on the whole tangent space at every
point. Stated without requiring callers to synthesize `FiniteDimensional ℝ E` or
`CompactSpace (sphere (0 : E) 1)` from `[Fact (finrank ℝ E = n + 1)]`. -/
@[simp]
theorem expDomain_sphere (p : sphere (0 : E) 1) :
    expDomain (𝓡 n) (sphere (0 : E) 1) p = univ := by
  have : FiniteDimensional ℝ E :=
    Module.finite_of_finrank_pos (by rw [Fact.out (p := finrank ℝ E = n + 1)]; positivity)
  have : CompactSpace (sphere (0 : E) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_sphere (0 : E) 1)
  exact expDomain_eq_univ_of_compactSpace p

/-- Every maximal geodesic of the round unit sphere is defined on all of `ℝ`. -/
@[simp]
theorem geodesicInterval_sphere (p : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p) :
    geodesicInterval (𝓡 n) (sphere (0 : E) 1) p v = univ := by
  rw [geodesicInterval_eq_preimage_expDomain, expDomain_sphere, preimage_univ]

/-- Every radial curve `t ↦ exp_p (t • v)` on the round unit sphere is a global geodesic on
`univ`. -/
theorem isGeodesicCurveOn_riemannianExp_smul_sphere_univ (p : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) p) :
    IsGeodesicCurveOn (𝓡 n)
      (fun t : ℝ ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v)) univ := by
  have h := (isJacobiFieldOn_mfderiv_riemannianExp (I := 𝓡 n) (M := sphere (0 : E) 1) p v 0
    ).isGeodesicCurveOn
  rwa [geodesicInterval_sphere] at h

/-- Along any radial geodesic `t ↦ exp_p (t • v)` on `Sⁿ`, the Riemannian length on `[0, 1]` is
`‖v‖ₑ` (for every `v`, including `‖v‖ ≥ π`). -/
@[simp]
theorem pathELength_riemannianExp_smul_sphere_zero_one (p : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) p) :
    pathELength (𝓡 n) (fun t : ℝ ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v)) 0 1 =
      ‖v‖ₑ := by
  have hcurve : (fun t : ℝ ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v)) =
      maximalGeodesic (𝓡 n) (sphere (0 : E) 1) p v :=
    funext fun t ↦ riemannianExp_smul p v t
  rw [hcurve, pathELength_maximalGeodesic (by simp) (by simp), sub_zero, ENNReal.ofReal_one,
    mul_one]

/-- The ambient inner product of `p` with `exp_p v` on the unit sphere is `cos ‖v‖`. -/
theorem inner_coe_riemannianExp_sphere (p : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p) :
    ⟪(p : E), (riemannianExp (𝓡 n) (sphere (0 : E) 1) p v : E)⟫_ℝ = Real.cos ‖v‖ := by
  have hp : ‖(p : E)‖ = 1 := mem_sphere_zero_iff_norm.1 p.2
  rw [coe_riemannianExp_sphere, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hp, inner_coe_mvfderiv_subtypeVal_sphere,
    one_pow, mul_one, mul_zero, add_zero]

/-- Every tangent vector of norm `π` at `p : Sⁿ` exponentiates to the antipodal point `-p`. -/
theorem riemannianExp_sphere_eq_neg_of_norm_eq_pi {p : sphere (0 : E) 1}
    {v : TangentSpace (𝓡 n) p} (hv : ‖v‖ = Real.pi) :
    riemannianExp (𝓡 n) (sphere (0 : E) 1) p v = -p := by
  rw [Subtype.ext_iff, coe_riemannianExp_sphere, hv, Real.cos_pi, Real.sin_pi, zero_div,
    zero_smul, add_zero, neg_one_smul]
  rfl

/-! ### Dimension zero -/

/-- Each point of the zero-dimensional round sphere `S⁰` has infinite injectivity radius. -/
theorem injectivityRadiusAt_sphere_zero [Fact (finrank ℝ E = 0 + 1)] (p : sphere (0 : E) 1) :
    injectivityRadiusAt (𝓡 0) (sphere (0 : E) 1) p = ⊤ :=
  injectivityRadiusAt_eq_top_of_subsingleton p

/-- The zero-dimensional round sphere `S⁰` has infinite global injectivity radius. -/
theorem injectivityRadius_sphere_zero [Fact (finrank ℝ E = 0 + 1)] :
    injectivityRadius (𝓡 0) (sphere (0 : E) 1) = ⊤ :=
  injectivityRadius_eq_top_of_subsingleton

/-! ### Normal tangent ball of radius `π` -/

/-- For `‖v‖ < π` on the unit sphere, the model sine `curvatureSine (1 * ‖v‖ ^ 2) 1` is nonzero. -/
private theorem curvatureSine_norm_sq_ne_zero_of_norm_lt_pi {p : sphere (0 : E) 1}
    {v : TangentSpace (𝓡 n) p} (hv : ‖v‖ < Real.pi) :
    curvatureSine (1 * ‖v‖ ^ 2) 1 ≠ 0 := by
  rw [one_mul]
  by_cases hv0 : v = 0
  · simp [hv0]
  · have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have hsq : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hpos
    rw [curvatureSine_of_pos hsq, Real.sqrt_sq hpos.le, mul_one]
    exact div_ne_zero (Real.sin_pos_of_pos_of_lt_pi hpos hv).ne' hpos.ne'

/-- The differential of `riemannianExp` at `p : Sⁿ` is injective at every `v` with `‖v‖ < π`. -/
theorem injective_mfderiv_riemannianExp_sphere_of_norm_lt_pi {p : sphere (0 : E) 1}
    {v : TangentSpace (𝓡 n) p} (hv : ‖v‖ < Real.pi) :
    Function.Injective
      (mfderiv 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n)
        (riemannianExp (𝓡 n) (sphere (0 : E) 1) p) v) := by
  let L : TangentSpace (𝓡 n) p →L[ℝ]
      TangentSpace (𝓡 n) (riemannianExp (𝓡 n) (sphere (0 : E) 1) p v) :=
    mfderiv 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n) (riemannianExp (𝓡 n) (sphere (0 : E) 1) p) v
  -- Unfold the normed-space tangent fibre `T_v(T_p Sⁿ)` to `T_p Sⁿ` so linearity applies directly.
  change Function.Injective L
  intro w₁ w₂ heq
  rw [← sub_eq_zero]
  set w := w₁ - w₂
  have hLw : L w = 0 := by rw [map_sub, heq, sub_self]
  have hK : ∀ t ∈ Icc (0 : ℝ) 1,
      (leviCivitaConnection (𝓡 n) (sphere (0 : E) 1)).HasSectionalCurvatureAt
        (isMetricCompatible_leviCivitaConnection (𝓡 n))
        (riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v)) 1 :=
    fun t _ ↦ hasConstantSectionalCurvature_sphere.hasSectionalCurvatureAt _
  have hinner := inner_mfderiv_riemannianExp_of_hasSectionalCurvatureAt
    (I := 𝓡 n) (M := sphere (0 : E) 1) (p := p) (v := v) (κ := 1)
    (by simp) hK w w
  -- Read `mfderiv` on `w` as `L w` in `hinner`.
  change ⟪L w, L w⟫_ℝ = _ at hinner
  rw [hLw, inner_zero_left, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  have hcS : 0 < curvatureSine (1 * ‖v‖ ^ 2) 1 ^ 2 :=
    sq_pos_of_ne_zero (curvatureSine_norm_sq_ne_zero_of_norm_lt_pi hv)
  have hproj : (ℝ ∙ v).starProjection w = 0 := by
    have hsq : ‖(ℝ ∙ v).starProjection w‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖w - (ℝ ∙ v).starProjection w‖]
    exact norm_eq_zero.1 (sq_eq_zero_iff.1 hsq)
  rw [hproj, norm_zero, zero_pow two_ne_zero, zero_add, sub_zero] at hinner
  exact norm_eq_zero.1 (sq_eq_zero_iff.1 ((mul_eq_zero.1 hinner.symm).resolve_left hcS.ne'))

/-- `riemannianExp` at `p : Sⁿ` is a smooth local diffeomorphism at every `v` with `‖v‖ < π`. -/
theorem isLocalDiffeomorphAt_riemannianExp_sphere_of_norm_lt_pi {p : sphere (0 : E) 1}
    {v : TangentSpace (𝓡 n) p} (hv : ‖v‖ < Real.pi) :
    IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n) ∞
      (riemannianExp (𝓡 n) (sphere (0 : E) 1) p) v :=
  isLocalDiffeomorphAt_of_injective_mfderiv
    (s := expDomain (𝓡 n) (sphere (0 : E) 1) p)
    (contMDiffOn_riemannianExp p) (isOpen_expDomain p) (by simp)
    BoundarylessManifold.isInteriorPoint (by simp)
    (injective_mfderiv_riemannianExp_sphere_of_norm_lt_pi hv) rfl

/-- `riemannianExp` at `p : Sⁿ` is injective on the open tangent ball of radius `π`. -/
theorem injOn_riemannianExp_sphere_ball_pi (p : sphere (0 : E) 1) :
    InjOn (riemannianExp (𝓡 n) (sphere (0 : E) 1) p) (Metric.ball 0 Real.pi) := by
  intro v hv w hw heq
  rw [mem_ball_zero_iff] at hv hw
  have hcos : Real.cos ‖v‖ = Real.cos ‖w‖ := by
    rw [← inner_coe_riemannianExp_sphere p v, ← inner_coe_riemannianExp_sphere p w, heq]
  have hnorm : ‖v‖ = ‖w‖ := by
    rw [← Real.arccos_cos (norm_nonneg v) hv.le, ← Real.arccos_cos (norm_nonneg w) hw.le, hcos]
  by_cases hv0 : v = 0
  · subst hv0
    exact (norm_eq_zero.1 (by simpa only [norm_zero] using hnorm.symm)).symm
  · have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have hcoeff : Real.sin ‖v‖ / ‖v‖ ≠ 0 :=
      div_ne_zero (Real.sin_pos_of_pos_of_lt_pi hpos hv).ne' hpos.ne'
    have hcoe := congrArg Subtype.val heq
    simp only [coe_riemannianExp_sphere, ← hnorm] at hcoe
    have hsmul : (Real.sin ‖v‖ / ‖v‖) • mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p v =
        (Real.sin ‖v‖ / ‖v‖) • mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p w :=
      add_left_cancel hcoe
    exact injective_mvfderiv_subtypeVal_sphere p (smul_right_injective E hcoeff hsmul)

/-- For every `n : ℕ` and `p : Sⁿ`, the open tangent ball `Metric.ball 0 Real.pi` is a normal
domain at `p`. -/
theorem isNormalDomain_ball_sphere_pi (p : sphere (0 : E) 1) :
    IsNormalDomain (𝓡 n) (sphere (0 : E) 1) p (Metric.ball 0 Real.pi) where
  isOpen := Metric.isOpen_ball
  zero_mem := Metric.mem_ball_self Real.pi_pos
  starConvex := (convex_ball (0 : TangentSpace (𝓡 n) p) Real.pi).starConvex
    (Metric.mem_ball_self Real.pi_pos)
  subset_expDomain := by simp
  injOn := injOn_riemannianExp_sphere_ball_pi p
  isLocalDiffeomorphOn := fun ⟨v, hv⟩ ↦
    isLocalDiffeomorphAt_riemannianExp_sphere_of_norm_lt_pi (mem_ball_zero_iff.1 hv)

/-- At every point of `Sⁿ` (for all `n : ℕ`, including `n = 0`), the injectivity radius is at least
`ENNReal.ofReal Real.pi`. -/
theorem ofReal_pi_le_injectivityRadiusAt_sphere (p : sphere (0 : E) 1) :
    ENNReal.ofReal Real.pi ≤ injectivityRadiusAt (𝓡 n) (sphere (0 : E) 1) p :=
  (isNormalDomain_ball_sphere_pi p).ofReal_le_injectivityRadiusAt

/-! ### Exact injectivity radius for `1 ≤ n` and rescaled spheres -/

/-- When `1 ≤ n`, every tangent space of `Sⁿ` contains a unit vector. -/
private theorem exists_norm_eq_one_tangentSpace_sphere (hn : 1 ≤ n) (p : sphere (0 : E) 1) :
    ∃ u : TangentSpace (𝓡 n) p, ‖u‖ = 1 := by
  have hfin : 0 < finrank ℝ (TangentSpace (𝓡 n) p) := by
    -- `TangentSpace (𝓡 n) p` is the model space `EuclideanSpace ℝ (Fin n)`.
    change 0 < finrank ℝ (EuclideanSpace ℝ (Fin n))
    rw [finrank_euclideanSpace_fin]
    omega
  have : Nontrivial (TangentSpace (𝓡 n) p) := Module.nontrivial_of_finrank_pos hfin
  exact exists_norm_eq (TangentSpace (𝓡 n) p) zero_le_one

/-- **Pointwise injectivity radius of the round unit `n`-sphere (`1 ≤ n`).** -/
@[simp]
theorem injectivityRadiusAt_sphere_of_one_le (hn : 1 ≤ n) (p : sphere (0 : E) 1) :
    injectivityRadiusAt (𝓡 n) (sphere (0 : E) 1) p = ENNReal.ofReal Real.pi := by
  refine le_antisymm ?_ (ofReal_pi_le_injectivityRadiusAt_sphere p)
  obtain ⟨u, hu⟩ := exists_norm_eq_one_tangentSpace_sphere hn p
  have hu0 : u ≠ 0 := by
    intro h0
    simp [h0] at hu
  let v : TangentSpace (𝓡 n) p := Real.pi • u
  let w : TangentSpace (𝓡 n) p := -(Real.pi • u)
  have hvw : v ≠ w := by
    intro heq
    have h2 : (2 * Real.pi) • u = 0 := by
      have hadd := congrArg (· + Real.pi • u) heq
      simpa [v, w, two_mul, add_smul] using hadd
    exact hu0 ((smul_eq_zero.1 h2).resolve_left (by positivity))
  have hv_norm : ‖v‖ = Real.pi := by
    rw [norm_smul, Real.norm_of_nonneg Real.pi_pos.le, hu, mul_one]
  have hw_norm : ‖w‖ = Real.pi := by rw [norm_neg, hv_norm]
  have hexp : riemannianExp (𝓡 n) (sphere (0 : E) 1) p v =
      riemannianExp (𝓡 n) (sphere (0 : E) 1) p w := by
    rw [riemannianExp_sphere_eq_neg_of_norm_eq_pi hv_norm,
      riemannianExp_sphere_eq_neg_of_norm_eq_pi hw_norm]
  have hle := injectivityRadiusAt_le_of_riemannianExp_eq_of_enorm_le hvw
    (by rw [← ofReal_norm, ← ofReal_norm, hv_norm, hw_norm]) hexp
  rwa [← ofReal_norm, hv_norm] at hle

/-- **Global injectivity radius of the round unit `n`-sphere (`1 ≤ n`).** -/
@[simp]
theorem injectivityRadius_sphere_of_one_le (hn : 1 ≤ n) :
    injectivityRadius (𝓡 n) (sphere (0 : E) 1) = ENNReal.ofReal Real.pi := by
  have : Nontrivial E :=
    Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
  have : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  simp [injectivityRadius_def, injectivityRadiusAt_sphere_of_one_le hn]

/-- **Pointwise injectivity radius of the round `n`-sphere of radius `r > 0` (`WithMetric` form,
`1 ≤ n`).** Since `sphereRoundMetricOfRadius r hr` multiplies the unit round metric by `r²`, the
injectivity radius scales by `√(r²) = r` to `ENNReal.ofReal (r * Real.pi)`. -/
@[simp]
theorem injectivityRadiusAt_withMetric_sphereRoundMetricOfRadius (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) (p : sphere (0 : E) 1) :
    injectivityRadiusAt (𝓡 n) (WithMetric (sphereRoundMetricOfRadius (E := E) (n := n) r hr))
        (WithMetric.toWithMetric _ p) =
      ENNReal.ofReal (r * Real.pi) := by
  set g₀ := (sphereRoundMetric (E := E) (n := n)).ofLE le_top
  rw [WithMetric.injectivityRadiusAt_congr _
      (g₀.rescale (fun _ ↦ r ^ 2) contMDiff_const fun _ ↦ pow_pos hr 2)
      (fun x v w ↦ by simp [g₀]) p,
    WithMetric.injectivityRadiusAt_rescale_const g₀ (pow_pos hr 2) p,
    WithMetric.injectivityRadiusAt_toWithMetric g₀ (fun x v w ↦ by simp [g₀]) p,
    injectivityRadiusAt_sphere_of_one_le hn p, Real.sqrt_sq hr.le,
    ← ENNReal.ofReal_mul hr.le]

/-- **Global injectivity radius of the round `n`-sphere of radius `r > 0` (`WithMetric` form,
`1 ≤ n`).** -/
@[simp]
theorem injectivityRadius_withMetric_sphereRoundMetricOfRadius (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    injectivityRadius (𝓡 n) (WithMetric (sphereRoundMetricOfRadius (E := E) (n := n) r hr)) =
      ENNReal.ofReal (r * Real.pi) := by
  set g₀ := (sphereRoundMetric (E := E) (n := n)).ofLE le_top
  rw [WithMetric.injectivityRadius_congr _
      (g₀.rescale (fun _ ↦ r ^ 2) contMDiff_const fun _ ↦ pow_pos hr 2)
      (fun x v w ↦ by simp [g₀]),
    WithMetric.injectivityRadius_rescale_const g₀ (pow_pos hr 2),
    WithMetric.injectivityRadius_eq g₀ (fun x v w ↦ by simp [g₀]),
    injectivityRadius_sphere_of_one_le hn, Real.sqrt_sq hr.le,
    ← ENNReal.ofReal_mul hr.le]

/-- **Pointwise injectivity radius of the round `n`-sphere of radius `r > 0` (`letI` form,
`1 ≤ n`).** -/
theorem injectivityRadiusAt_sphereRoundMetricOfRadius (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    (p : sphere (0 : E) 1) :
    (letI : RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
        ⟨(sphereRoundMetricOfRadius r hr).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
          (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
        Bundle.instIsContMDiffRiemannianBundle _;
      injectivityRadiusAt (𝓡 n) (sphere (0 : E) 1) p) =
    ENNReal.ofReal (r * Real.pi) := by
  let _ : RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
    ⟨(sphereRoundMetricOfRadius r hr).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
    Bundle.instIsContMDiffRiemannianBundle _
  rw [← WithMetric.injectivityRadiusAt_toWithMetric (sphereRoundMetricOfRadius r hr)
      (fun _ _ _ ↦ rfl) p,
    injectivityRadiusAt_withMetric_sphereRoundMetricOfRadius hn hr p]

/-- **Global injectivity radius of the round `n`-sphere of radius `r > 0` (`letI` form,
`1 ≤ n`).** -/
theorem injectivityRadius_sphereRoundMetricOfRadius (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    (letI : RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
        ⟨(sphereRoundMetricOfRadius r hr).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
          (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
        Bundle.instIsContMDiffRiemannianBundle _;
      injectivityRadius (𝓡 n) (sphere (0 : E) 1)) =
    ENNReal.ofReal (r * Real.pi) := by
  let _ : RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
    ⟨(sphereRoundMetricOfRadius r hr).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
    Bundle.instIsContMDiffRiemannianBundle _
  rw [← WithMetric.injectivityRadius_eq (sphereRoundMetricOfRadius r hr) fun _ _ _ ↦ rfl,
    injectivityRadius_withMetric_sphereRoundMetricOfRadius hn hr]

/-! ### Antipodal conjugate multiplicity and non-uniqueness of minimizing geodesics -/

/-- Along any radial geodesic `t ↦ exp_p (t • v)` on `Sⁿ` with `‖v‖ = π`, the antipodal parameter
`1` has conjugate multiplicity `n - 1`. In particular, `S¹` (`n = 1`) has conjugate multiplicity
`0` (no conjugate points), whereas for `2 ≤ n` the antipode has positive conjugate multiplicity
`n - 1`. -/
theorem conjugateMultiplicity_sphere_of_norm_eq_pi {p : sphere (0 : E) 1}
    {v : TangentSpace (𝓡 n) p} (hv : ‖v‖ = Real.pi) :
    conjugateMultiplicity (isGeodesicCurveOn_riemannianExp_smul_sphere_univ p v)
      isPreconnected_univ (mem_univ (0 : ℝ)) (1 : ℝ) = n - 1 := by
  have hsub : (univ : Set ℝ) ⊆ geodesicInterval (𝓡 n) (sphere (0 : E) 1) p v := by simp
  have hvel : curveVelocityWithin (𝓡 n)
      (fun t : ℝ ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v)) univ 0 = v := by
    rw [curveVelocityWithin_univ, curveVelocity_riemannianExp_smul_zero]
  have hS : curvatureSine
      ((1 : ℝ) * ‖curveVelocityWithin (𝓡 n)
        (fun t : ℝ ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v)) univ 0‖ ^ 2) 1 = 0 := by
    -- Rewriting `0 • v = 0` and `exp_p 0 = p` transports the norm from `T_{exp_p(0 • v)} Sⁿ`
    -- to `T_p Sⁿ`.
    rw [hvel, zero_smul, riemannianExp_zero, hv, one_mul,
      curvatureSine_of_pos (sq_pos_of_pos Real.pi_pos),
      Real.sqrt_sq Real.pi_pos.le, mul_one, Real.sin_pi, zero_div]
  have hmult := conjugateMultiplicity_eq_finrank_sub_one_of_curvatureSine_eq_zero
    (hγ := isGeodesicCurveOn_riemannianExp_smul_sphere_univ p v)
    isPreconnected_univ hsub (mem_univ 0) (mem_univ 1) one_ne_zero
    (fun t _ ↦ hasConstantSectionalCurvature_sphere.hasSectionalCurvatureAt _) hS
  rwa [finrank_euclideanSpace_fin] at hmult

/-- **Antipodal Riemannian distance on `Sⁿ` (`1 ≤ n`).** The Riemannian distance between any point
`p : Sⁿ` and its antipode `-p` is `ENNReal.ofReal Real.pi` (equal to `injectivityRadiusAt p`). -/
@[simp]
theorem riemannianEDist_sphere_neg_self (hn : 1 ≤ n) (p : sphere (0 : E) 1) :
    riemannianEDist (𝓡 n) p (-p) = ENNReal.ofReal Real.pi := by
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hu⟩ := exists_norm_eq_one_tangentSpace_sphere hn p
    let v : TangentSpace (𝓡 n) p := Real.pi • u
    have hv_norm : ‖v‖ = Real.pi := by
      rw [norm_smul, Real.norm_of_nonneg Real.pi_pos.le, hu, mul_one]
    let γ : ℝ → sphere (0 : E) 1 :=
      fun t ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v)
    have hγ : IsGeodesicCurveOn (𝓡 n) γ (Icc 0 1) :=
      (isGeodesicCurveOn_riemannianExp_smul_sphere_univ p v).mono
        (uniqueDiffOn_Icc zero_lt_one) (subset_univ _)
    have h0 : γ 0 = p := by simp [γ]
    have h1 : γ 1 = -p := by
      simpa only [γ, one_smul] using riemannianExp_sphere_eq_neg_of_norm_eq_pi hv_norm
    calc
      riemannianEDist (𝓡 n) p (-p)
        ≤ pathELength (𝓡 n) γ 0 1 :=
          riemannianEDist_le_pathELength (hγ.contMDiffOn.of_le one_le_two) h0 h1 zero_le_one
      _ = ENNReal.ofReal Real.pi := by
          rw [pathELength_riemannianExp_smul_sphere_zero_one, ← ofReal_norm, hv_norm]
  · by_contra! hlt
    have hinj : riemannianEDist (𝓡 n) p (-p) <
        injectivityRadiusAt (𝓡 n) (sphere (0 : E) 1) p := by
      rwa [injectivityRadiusAt_sphere_of_one_le hn p]
    obtain ⟨v, ⟨hv_lt_inj, hv_exp⟩, _⟩ :=
      existsUnique_riemannianExp_eq_of_riemannianEDist_lt_injectivityRadiusAt hinj
    have hv_lt : ‖v‖ < Real.pi := by
      rw [← ofReal_norm, injectivityRadiusAt_sphere_of_one_le hn p,
        ENNReal.ofReal_lt_ofReal_iff Real.pi_pos] at hv_lt_inj
      exact hv_lt_inj
    have hcos : Real.cos ‖v‖ = -1 := by
      have h := inner_coe_riemannianExp_sphere p v
      have hp : ‖(p : E)‖ = 1 := mem_sphere_zero_iff_norm.1 p.2
      rw [hv_exp, coe_neg_sphere, inner_neg_right, real_inner_self_eq_norm_sq,
        hp, one_pow] at h
      exact h.symm
    have hgt : -1 < Real.cos ‖v‖ := by
      rw [← Real.cos_pi]
      exact Real.strictAntiOn_cos ⟨norm_nonneg v, hv_lt.le⟩
        ⟨Real.pi_pos.le, le_rfl⟩ hv_lt
    linarith

/-- **Sharpness at the injectivity radius on `Sⁿ` (`1 ≤ n`).** At distance `π = inj(p)` from
`p : Sⁿ`, the antipode `-p` is joined to `p` by two distinct minimizing geodesics on `[0, 1]`
(disagreeing at their midpoint `t = 1 / 2`), showing that uniqueness of minimizing geodesics below
`inj(p)` fails at `riemannianEDist p q = inj(p)`. -/
theorem exists_two_minimizing_geodesics_sphere_antipode (hn : 1 ≤ n) (p : sphere (0 : E) 1) :
    ∃ γ₁ γ₂ : ℝ → sphere (0 : E) 1,
      γ₁ (1 / 2) ≠ γ₂ (1 / 2) ∧
      IsGeodesicCurveOn (𝓡 n) γ₁ (Icc 0 1) ∧ γ₁ 0 = p ∧ γ₁ 1 = -p ∧
      pathELength (𝓡 n) γ₁ 0 1 = riemannianEDist (𝓡 n) p (-p) ∧
      IsGeodesicCurveOn (𝓡 n) γ₂ (Icc 0 1) ∧ γ₂ 0 = p ∧ γ₂ 1 = -p ∧
      pathELength (𝓡 n) γ₂ 0 1 = riemannianEDist (𝓡 n) p (-p) := by
  obtain ⟨u, hu⟩ := exists_norm_eq_one_tangentSpace_sphere hn p
  have hu0 : u ≠ 0 := by
    intro h0
    simp [h0] at hu
  let v₁ : TangentSpace (𝓡 n) p := Real.pi • u
  let v₂ : TangentSpace (𝓡 n) p := -(Real.pi • u)
  have hv₁ : ‖v₁‖ = Real.pi := by
    rw [norm_smul, Real.norm_of_nonneg Real.pi_pos.le, hu, mul_one]
  have hv₂ : ‖v₂‖ = Real.pi := by rw [norm_neg, hv₁]
  let γ₁ : ℝ → sphere (0 : E) 1 :=
    fun t ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v₁)
  let γ₂ : ℝ → sphere (0 : E) 1 :=
    fun t ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v₂)
  have hseg (v : TangentSpace (𝓡 n) p) (hv : ‖v‖ = Real.pi) :
      let γ := fun t : ℝ ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v)
      IsGeodesicCurveOn (𝓡 n) γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = -p ∧
        pathELength (𝓡 n) γ 0 1 = riemannianEDist (𝓡 n) p (-p) := by
    intro γ
    have hγ : IsGeodesicCurveOn (𝓡 n) γ (Icc 0 1) :=
      (isGeodesicCurveOn_riemannianExp_smul_sphere_univ p v).mono
        (uniqueDiffOn_Icc zero_lt_one) (subset_univ _)
    refine ⟨hγ, by simp [γ], ?_, ?_⟩
    · simpa only [γ, one_smul] using riemannianExp_sphere_eq_neg_of_norm_eq_pi hv
    · rw [pathELength_riemannianExp_smul_sphere_zero_one, ← ofReal_norm, hv,
        riemannianEDist_sphere_neg_self hn p]
  refine ⟨γ₁, γ₂, ?_, ?_⟩
  · intro hmid
    have hcoe := congrArg Subtype.val hmid
    have hhalf_v₁ : ‖(1 / 2 : ℝ) • v₁‖ = Real.pi / 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num), hv₁, one_div_mul_eq_div]
    have hhalf_v₂ : ‖(1 / 2 : ℝ) • v₂‖ = Real.pi / 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num), hv₂, one_div_mul_eq_div]
    simp only [γ₁, γ₂, coe_riemannianExp_sphere, hhalf_v₁, hhalf_v₂,
      Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, zero_add] at hcoe
    have hpos : (1 : ℝ) / (Real.pi / 2) ≠ 0 := div_ne_zero one_ne_zero (half_pos Real.pi_pos).ne'
    have hmv := injective_mvfderiv_subtypeVal_sphere p (smul_right_injective E hpos hcoe)
    have hdiff : ((1 / 2 : ℝ) * Real.pi + (1 / 2 : ℝ) * Real.pi) • u = 0 := by
      have hadd := congrArg (· + (1 / 2 : ℝ) • (Real.pi • u)) hmv
      simpa [v₁, v₂, smul_smul, add_smul] using hadd
    exact hu0 ((smul_eq_zero.1 hdiff).resolve_left (by positivity))
  · rcases hseg v₁ hv₁ with ⟨h1a, h1b, h1c, h1d⟩
    rcases hseg v₂ hv₂ with ⟨h2a, h2b, h2c, h2d⟩
    exact ⟨h1a, h1b, h1c, h1d, h2a, h2b, h2c, h2d⟩

end TauCeti

end
