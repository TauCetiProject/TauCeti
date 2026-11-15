/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RicciFlow.StandardCap.Profile
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.WarpedProd

/-!
# The standard cap away from its tip

A standard cap profile `f` gives a smooth positive definite metric
`dr² + f(r)² g_(Sⁿ)` on `(0, ∞) × Sⁿ`. We construct this metric using the native
warped-product construction and compute both its sectional curvature and its scalar
curvature from the native Levi-Civita connection. Mixed planes have sectional
curvature `-f''/f`, vertical planes have sectional curvature `(1 - f'²)/f²`, and
every tangent two-plane (including tilted planes) has nonnegative sectional
curvature, with constant sectional curvature `1/4` near the missing tip. Scalar
curvature is nonnegative, equals `n(n+1)/4` near the tip, and on the cylindrical
end equals `n(n-1)/2`, hence equals one when `n = 2`.

This is the punctured cap: the origin has not been added, and no completeness
assertion is made. Polar coordinates identify it isometrically with the punctured
cap metric on `V ∖ {0}`.

## Main definitions

* `TauCeti.standardCapRadialDomain`: the open radial half-line `(0, ∞)` as an `Opens ℝ`.
* `TauCeti.IsStandardCapProfile.puncturedMetric`: the smooth warped-product metric
  `dr² + f(r)² g_(Sⁿ)` on `(0, ∞) × Sⁿ`.

## Main results

* `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_mixed`,
  `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_vertical`,
  `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_nonneg`,
  `TauCeti.IsStandardCapProfile.exists_hasSectionalCurvatureAt_puncturedMetric_round`: sectional
  curvatures of mixed, vertical, and general tangent two-planes on the punctured cap.
* `TauCeti.IsStandardCapProfile.scalarCurvature_puncturedMetric`,
  `TauCeti.IsStandardCapProfile.scalarCurvature_puncturedMetric_nonneg`,
  `TauCeti.IsStandardCapProfile.exists_scalarCurvature_puncturedMetric_eq_round`,
  `TauCeti.IsStandardCapProfile.exists_scalarCurvature_puncturedMetric_eq_cylinder`: scalar
  curvature formula, nonnegativity, and round-tip / cylindrical-end values.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics
  Monographs 3 (2007), Definition 12.1.
* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7,
  Proposition 42 and Corollary 43 (warped-product curvature).
-/

public noncomputable section

open Bundle CovariantDerivative Set Real TopologicalSpace
open TauCeti.Manifold
open scoped ContDiff Manifold InnerProductSpace Topology

/-- The open radial half-line used for punctured standard caps. -/
abbrev TauCeti.standardCapRadialDomain : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩

namespace TauCeti.IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : TauCeti.IsStandardCapProfile f)
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (Module.finrank ℝ V = n + 1)]

/-- The standard cap metric `dr² + f(r)² g_(Sⁿ)` away from the tip, with the
radial coordinate first. The sphere is the unit sphere in `V`. -/
def puncturedMetric :
    ContMDiffRiemannianMetric (𝓘(ℝ).prod (𝓡 n)) ∞ (ℝ × EuclideanSpace ℝ (Fin n))
      (fun p : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :=
  (((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace
    standardCapRadialDomain).warpedProdTangentSpace (fun r ↦ f r)
      (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
      (fun r ↦ (hf.apply_pos r.property).ne')
      ((sphereRoundMetric (E := V)).ofLE (m := ∞) le_top)

variable {V}

/-- The punctured metric is the orthogonal sum of the radial metric and the
round sphere metric multiplied by `f(r)²`. -/
@[simp]
theorem puncturedMetric_inner
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1)
    (v w : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    (hf.puncturedMetric (n := n) V).inner p v w =
      (((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace
        standardCapRadialDomain).inner p.1 (tangentSpaceProdEquiv p v).1
          (tangentSpaceProdEquiv p w).1 +
      f p.1 ^ 2 * ((sphereRoundMetric (E := V)).ofLE (m := ∞) le_top).inner p.2
        (tangentSpaceProdEquiv p v).2 (tangentSpaceProdEquiv p w).2 := by
  rw [puncturedMetric, ContMDiffRiemannianMetric.warpedProdTangentSpace_inner]

/-- Mixed radial-spherical tangent planes of the punctured standard cap have sectional
curvature `-f''(r) / f(r)`. Both spanning vectors must be nonzero. -/
theorem sectionalCurvature_puncturedMetric_mixed
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1)
    (u : TangentSpace 𝓘(ℝ) p.1) (v : TangentSpace (𝓡 n) p.2) (hu : u ≠ 0) (hv : v ≠ 0) :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
        (standardCapRadialDomain × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p
      ((tangentSpaceProdEquiv p).symm (u, 0))
      ((tangentSpaceProdEquiv p).symm (0, v)) =
      -deriv (deriv f) p.1 / f p.1 := by
  let : RiemannianBundle
    (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
    ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  rw [puncturedMetric]
  exact sectionalCurvature_warpedProdTangentSpace_real_sphere_mixed standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
    (fun r ↦ (hf.apply_pos r.property).ne') p u v hu hv

/-- Vertical spherical tangent planes of the punctured standard cap have sectional
curvature `(1 - f'(r)²) / f(r)²`. -/
theorem sectionalCurvature_puncturedMetric_vertical
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1)
    (v w : TangentSpace (𝓡 n) p.2) (hvw : LinearIndependent ℝ ![v, w]) :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
        (standardCapRadialDomain × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p
      ((tangentSpaceProdEquiv p).symm (0, v))
      ((tangentSpaceProdEquiv p).symm (0, w)) =
      (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 := by
  let : RiemannianBundle
    (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
    ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  rw [puncturedMetric]
  exact sectionalCurvature_warpedProdTangentSpace_real_sphere_vertical standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
    (fun r ↦ (hf.apply_pos r.property).ne') p v w hvw

/-- Every tangent two-plane of the punctured standard cap (including tilted planes) has
nonnegative sectional curvature; dependent pairs also evaluate to `0 ≥ 0`. -/
theorem sectionalCurvature_puncturedMetric_nonneg
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1)
    (X Y : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    0 ≤ (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
        (standardCapRadialDomain × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p X Y := by
  let : RiemannianBundle
    (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
    ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  rw [puncturedMetric]
  have h₀ := hf.deriv_nonneg p.1.property.le
  have h₁ := hf.deriv_le_one p.1.property.le
  have h₂ := hf.deriv_deriv_nonpos p.1.property.le
  have hpos := hf.apply_pos p.1.property
  exact sectionalCurvature_warpedProdTangentSpace_real_sphere_nonneg standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
    (fun r ↦ (hf.apply_pos r.property).ne') p
    (div_nonneg (neg_nonneg.2 h₂) hpos.le)
    (div_nonneg (by nlinarith) (sq_nonneg _)) X Y

/-- Near its missing tip, the punctured standard cap has constant sectional curvature `1 / 4`,
the sectional curvature of the round sphere of radius `2`. -/
theorem exists_hasSectionalCurvatureAt_puncturedMetric_round :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    ∃ r₀ > 0, ∀ p : standardCapRadialDomain × Metric.sphere (0 : V) 1,
      (p.1 : ℝ) < r₀ →
      (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
          (standardCapRadialDomain × Metric.sphere (0 : V) 1)).HasSectionalCurvatureAt
        (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p (1 / 4) := by
  let : RiemannianBundle
    (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
    ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin
  refine ⟨r₀, hr₀, fun p hp ↦ ?_⟩
  have heq : f =ᶠ[𝓝 (p.1 : ℝ)] fun s ↦ 2 * sin (s / 2) := by
    filter_upwards [Ioo_mem_nhds p.1.property hp] with s hs using h s ⟨hs.1.le, hs.2⟩
  have hd : deriv f =ᶠ[𝓝 (p.1 : ℝ)] fun s ↦ cos (s / 2) := by
    filter_upwards [heq.deriv] with s hs
    rw [hs, (((hasDerivAt_id' s).div_const 2).sin.const_mul 2).deriv]
    ring
  have hdd : deriv (deriv f) (p.1 : ℝ) = -sin ((p.1 : ℝ) / 2) / 2 := by
    rw [hd.deriv_eq, (((hasDerivAt_id' (p.1 : ℝ)).div_const 2).cos).deriv]
    ring
  have hsin : sin ((p.1 : ℝ) / 2) ≠ 0 := by
    have := hf.apply_pos p.1.property
    rw [heq.eq_of_nhds] at this
    exact ne_of_gt (by linarith)
  have htrig : 1 - cos ((p.1 : ℝ) / 2) ^ 2 = sin ((p.1 : ℝ) / 2) ^ 2 := by
    nlinarith [sin_sq_add_cos_sq ((p.1 : ℝ) / 2)]
  rw [puncturedMetric]
  apply hasSectionalCurvatureAt_warpedProdTangentSpace_real_sphere standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
    (fun r ↦ (hf.apply_pos r.property).ne') p
  · rw [heq.eq_of_nhds, hdd]; field_simp; ring
  · rw [heq.eq_of_nhds, hd.eq_of_nhds, htrig]; field_simp; ring

/-- Scalar curvature of the punctured standard cap, using ordinary radial derivatives.
For a two-dimensional sphere fibre the two terms are
`2(1-f'²)/f² - 4f''/f`. -/
theorem scalarCurvature_puncturedMetric
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1) :
    (hf.puncturedMetric (n := n) V).scalarCurvature p =
      (n : ℝ) * (n - 1) * (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 -
        2 * n * deriv (deriv f) p.1 / f p.1 := by
  rw [puncturedMetric]
  exact scalarCurvature_warpedProdTangentSpace_real_sphere standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
    (fun r ↦ (hf.apply_pos r.property).ne') p

/-- The punctured standard cap has nonnegative scalar curvature in every
sphere dimension. -/
theorem scalarCurvature_puncturedMetric_nonneg
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1) :
    0 ≤ (hf.puncturedMetric (n := n) V).scalarCurvature p := by
  rw [hf.scalarCurvature_puncturedMetric (n := n)]
  have h₀ := hf.deriv_nonneg p.1.property.le
  have h₁ := hf.deriv_le_one p.1.property.le
  have h₂ := hf.deriv_deriv_nonpos p.1.property.le
  have hpos := hf.apply_pos p.1.property
  cases n with
  | zero => simp
  | succ n =>
    have hn : (0 : ℝ) ≤ (n + 1 : ℕ) - 1 := by simp
    have hderiv : 0 ≤ 1 - deriv f p.1 ^ 2 := by nlinarith
    have hfirst : 0 ≤ ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1) *
        (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 := by positivity
    have hsecond : 2 * ((n + 1 : ℕ) : ℝ) * deriv (deriv f) p.1 / f p.1 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) hpos.le
    linarith

/-- On a sufficiently far cylindrical end, scalar curvature is `n(n-1)/2`.
In particular it is one for the punctured three-dimensional cap. -/
theorem exists_scalarCurvature_puncturedMetric_eq_cylinder :
    ∃ R > 0, ∀ p : standardCapRadialDomain × Metric.sphere (0 : V) 1,
      R ≤ (p.1 : ℝ) →
      (hf.puncturedMetric (n := n) V).scalarCurvature p = (n : ℝ) * (n - 1) / 2 := by
  obtain ⟨R, hR⟩ := hf.exists_eq_sqrt_two
  refine ⟨max R 0 + 1, by positivity, fun p hp ↦ ?_⟩
  have hr : R < (p.1 : ℝ) := by linarith [le_max_left R 0]
  have heq : f =ᶠ[𝓝 (p.1 : ℝ)] fun _ ↦ √2 := by
    filter_upwards [Ioi_mem_nhds hr] with s hs using hR s hs.le
  have hd : deriv f =ᶠ[𝓝 (p.1 : ℝ)] fun _ ↦ 0 := by
    filter_upwards [heq.deriv] with s hs
    simpa only [deriv_const] using hs
  rw [hf.scalarCurvature_puncturedMetric, heq.eq_of_nhds, hd.eq_of_nhds,
    hd.deriv_eq, deriv_const, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Near its missing tip, the punctured metric has scalar curvature `n(n+1)/4`,
the scalar curvature of a round sphere of sectional curvature `1/4`. -/
theorem exists_scalarCurvature_puncturedMetric_eq_round :
    ∃ r₀ > 0, ∀ p : standardCapRadialDomain × Metric.sphere (0 : V) 1,
      (p.1 : ℝ) < r₀ →
      (hf.puncturedMetric (n := n) V).scalarCurvature p = (n : ℝ) * (n + 1) / 4 := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin
  refine ⟨r₀, hr₀, fun p hp ↦ ?_⟩
  have heq : f =ᶠ[𝓝 (p.1 : ℝ)] fun s ↦ 2 * sin (s / 2) := by
    filter_upwards [Ioo_mem_nhds p.1.property hp] with s hs using h s ⟨hs.1.le, hs.2⟩
  have hd : deriv f =ᶠ[𝓝 (p.1 : ℝ)] fun s ↦ cos (s / 2) := by
    filter_upwards [heq.deriv] with s hs
    rw [hs, (((hasDerivAt_id' s).div_const 2).sin.const_mul 2).deriv]
    ring
  have hdd : deriv (deriv f) (p.1 : ℝ) = -sin ((p.1 : ℝ) / 2) / 2 := by
    rw [hd.deriv_eq, (((hasDerivAt_id' (p.1 : ℝ)).div_const 2).cos).deriv]
    ring
  have hsin : sin ((p.1 : ℝ) / 2) ≠ 0 := by
    have := hf.apply_pos p.1.property
    rw [heq.eq_of_nhds] at this
    exact ne_of_gt (by linarith)
  have htrig : 1 - cos ((p.1 : ℝ) / 2) ^ 2 = sin ((p.1 : ℝ) / 2) ^ 2 := by
    nlinarith [sin_sq_add_cos_sq ((p.1 : ℝ) / 2)]
  rw [hf.scalarCurvature_puncturedMetric, heq.eq_of_nhds, hd.eq_of_nhds, hdd, htrig]
  field_simp
  ring

end TauCeti.IsStandardCapProfile
