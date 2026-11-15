/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Cylinder
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.WarpedProd
public import TauCeti.Geometry.RicciFlow.StandardCap.Profile
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The standard cap away from its tip

A standard cap profile `f` gives a smooth positive definite metric `dr² + f(r)² g_(Sⁿ)` on
`(0, ∞) × Sⁿ` via the native warped-product construction, identified smoothly with `V ∖ {0}` by
polar coordinates (`TauCeti.radialSphereDiffeomorph`). Mixed planes have sectional curvature
`-f''/f`, vertical planes have `(1 - f'²)/f²`, and every tangent two-plane has nonnegative
sectional curvature, equal to `1/4` near the missing tip. Scalar curvature is nonnegative, equals
`n(n+1)/4` near the tip, and equals `n(n-1)/2` on the cylindrical end (`1` when `n = 2`).

## Main definitions and results

* `TauCeti.standardCapRadialDomain`, `TauCeti.radialSphereDiffeomorph`,
  `TauCeti.mvfderiv_radial_smul_coe_sphere_apply`: polar coordinates `(r, u) ↦ r • u` on
  `(0, ∞) × Sⁿ` and its differential.
* `TauCeti.IsStandardCapProfile.puncturedMetric`: the smooth warped metric `dr² + f(r)² g_(Sⁿ)`.
* `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_mixed`,
  `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_vertical`,
  `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_nonneg`,
  `TauCeti.IsStandardCapProfile.exists_hasSectionalCurvatureAt_puncturedMetric_round`: sectional
  curvatures on the punctured cap.
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

open Bundle CovariantDerivative Manifold Metric Module Set Real TopologicalSpace
open TauCeti.Manifold
open scoped ContDiff Manifold InnerProductSpace Topology

/-- The open radial half-line used for punctured standard caps. -/
abbrev TauCeti.standardCapRadialDomain : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩

namespace TauCeti

section Polar

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)]

/-- **Polar coordinates** `(r, u) ↦ r • u` as a smooth diffeomorphism from
`standardCapRadialDomain × Sⁿ` onto the punctured space `V ∖ {0}`, with inverse
`x ↦ (‖x‖, ‖x‖⁻¹ • x)`. -/
def radialSphereDiffeomorph :
    (standardCapRadialDomain × sphere (0 : V) 1) ≃ₘ⟮𝓘(ℝ).prod (𝓡 n), 𝓘(ℝ, V)⟯ puncturedSpace V where
  toFun p := ⟨(p.1 : ℝ) • (p.2 : V),
    mem_puncturedSpace.2 (smul_ne_zero p.1.property.ne' (ne_zero_of_mem_unit_sphere p.2))⟩
  invFun x := (⟨‖(x : V)‖, norm_pos_iff.2 (mem_puncturedSpace.1 x.2)⟩,
    ⟨‖(x : V)‖⁻¹ • (x : V), by
      simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 (mem_puncturedSpace.1 x.2))]⟩)
  left_inv p := by
    rcases p with ⟨r, u⟩
    have hr : 0 < (r : ℝ) := r.property; have hu : ‖(u : V)‖ = 1 := norm_eq_of_mem_sphere u
    exact Prod.ext (Subtype.ext (by simp [norm_smul, hu, abs_of_pos hr]))
      (Subtype.ext (by simp [norm_smul, hu, abs_of_pos hr, smul_smul, inv_mul_cancel₀ hr.ne']))
  right_inv x := Subtype.ext <| by
    simp [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 (mem_puncturedSpace.1 x.2))]
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff (puncturedSpace V) _).1 <|
      (contMDiff_subtype_val.comp contMDiff_fst).smul (contMDiff_coe_sphere.comp contMDiff_snd)
  contMDiff_invFun := by
    refine ContMDiff.prodMk ?_ ?_
    · refine (ContMDiff.subtypeVal_comp_iff standardCapRadialDomain _).1 fun x ↦ ?_
      exact (contMDiffAt_subtype_iff (f := fun y : V ↦ ‖y‖)).2
        (contDiffAt_norm ℝ (mem_puncturedSpace.1 x.2)).contMDiffAt
    · refine ContMDiff.codRestrict_sphere (f := fun x : puncturedSpace V ↦ ‖(x : V)‖⁻¹ • (x : V))
        (fun x ↦ (contMDiffAt_subtype_iff (f := fun y : V ↦ ‖y‖⁻¹ • y)).2 ?_) _
      have hx : (x : V) ≠ 0 := mem_puncturedSpace.1 x.2
      exact (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.2 hx)).smul contDiffAt_id).contMDiffAt

variable {V}

@[simp] theorem coe_radialSphereDiffeomorph_apply (p : standardCapRadialDomain × sphere (0 : V) 1) :
    (radialSphereDiffeomorph (n := n) V p : V) = (p.1 : ℝ) • (p.2 : V) := (rfl)

@[simp] theorem radialSphereDiffeomorph_symm_apply_fst (x : puncturedSpace V) :
    ((radialSphereDiffeomorph (n := n) V).symm x).1 =
      ⟨‖(x : V)‖, norm_pos_iff.2 (mem_puncturedSpace.1 x.2)⟩ := (rfl)

@[simp] theorem coe_radialSphereDiffeomorph_symm_apply_snd (x : puncturedSpace V) :
    (((radialSphereDiffeomorph (n := n) V).symm x).2 : V) = ‖(x : V)‖⁻¹ • (x : V) := (rfl)

/-- The differential of `(r, u) ↦ r • u` on `(0, ∞) × Sⁿ` sends `(a, w)` at `(r, u)` to
`a • u + r • w`. -/
theorem mvfderiv_radial_smul_coe_sphere_apply
    (p : standardCapRadialDomain × sphere (0 : V) 1)
    (v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    mvfderiv (𝓘(ℝ).prod (𝓡 n))
        (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p v =
      (tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p v).1) • (p.2 : V) +
        (p.1 : ℝ) • mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.2
          (tangentSpaceProdEquiv p v).2 := by
  have hd₁ : MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ)
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ)) p :=
    (contMDiff_subtype_val.mdifferentiable one_ne_zero p.1).comp p mdifferentiableAt_fst
  have hd₂ : MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.2 : V)) p :=
    ((contMDiff_coe_sphere (E := V) (n := n) (m := 1) p.2).mdifferentiableAt one_ne_zero).comp p
      mdifferentiableAt_snd
  have hsub : mvfderiv 𝓘(ℝ) Subtype.val p.1 (tangentSpaceProdEquiv p v).1 =
      tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p v).1 := by
    rw [mvfderiv_subtype_val_apply]
    rfl
  have h₁ : mvfderiv (𝓘(ℝ).prod (𝓡 n))
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ)) p v =
      tangentSpaceCastModel 𝓘(ℝ) p.1 (tangentSpaceProdEquiv p v).1 := by
    rw [← hsub, tangentSpaceProdEquiv_apply]
    exact mvfderiv_comp_fst_apply Subtype.val p v
  have h₂ : mvfderiv (𝓘(ℝ).prod (𝓡 n))
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.2 : V)) p v =
      mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.2 (tangentSpaceProdEquiv p v).2 := by
    rw [tangentSpaceProdEquiv_apply]
    exact mvfderiv_comp_snd_apply _ p v
  rw [mvfderiv_fun_smul hd₁ hd₂]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply, h₁, h₂]
  exact add_comm _ _

end Polar

end TauCeti

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
include hf

private abbrev puncturedBundle :
    RiemannianBundle
      (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
  ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩

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
  let _ := hf.puncturedBundle (V := V) (n := n)
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
  let _ := hf.puncturedBundle (V := V) (n := n)
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
  let _ := hf.puncturedBundle (V := V) (n := n)
  rw [puncturedMetric]
  exact sectionalCurvature_warpedProdTangentSpace_real_sphere_nonneg standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
    (fun r ↦ (hf.apply_pos r.property).ne') p
    (div_nonneg (neg_nonneg.2 (hf.deriv_deriv_nonpos p.1.property.le))
      (hf.apply_pos p.1.property).le)
    (div_nonneg (by nlinarith [hf.deriv_nonneg p.1.property.le, hf.deriv_le_one p.1.property.le])
      (sq_nonneg _)) X Y

private theorem deriv_eq_round_of_eq_two_mul_sin {r₀ : ℝ}
    (h : ∀ s ∈ Ico 0 r₀, f s = 2 * sin (s / 2)) {r : ℝ} (hr0 : 0 < r) (hr : r < r₀) :
    f r = 2 * sin (r / 2) ∧ deriv f r = cos (r / 2) ∧
      deriv (deriv f) r = -sin (r / 2) / 2 ∧ sin (r / 2) ≠ 0 := by
  have heq : f =ᶠ[𝓝 r] fun s ↦ 2 * sin (s / 2) := by
    filter_upwards [Ioo_mem_nhds hr0 hr] with s hs using h s ⟨hs.1.le, hs.2⟩
  have hd : deriv f =ᶠ[𝓝 r] fun s ↦ cos (s / 2) := by
    filter_upwards [heq.deriv] with s hs
    rw [hs, (((hasDerivAt_id' s).div_const 2).sin.const_mul 2).deriv]
    ring
  refine ⟨heq.eq_of_nhds, hd.eq_of_nhds, ?_, ?_⟩
  · rw [hd.deriv_eq, (((hasDerivAt_id' r).div_const 2).cos).deriv]; ring
  · have hpos := hf.apply_pos hr0
    rw [heq.eq_of_nhds] at hpos
    exact ne_of_gt (by linarith)

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
  let _ := hf.puncturedBundle (V := V) (n := n)
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin
  refine ⟨r₀, hr₀, fun p hp ↦ ?_⟩
  obtain ⟨hf0, hd, hdd, hsin⟩ := hf.deriv_eq_round_of_eq_two_mul_sin h p.1.property hp
  have htrig : 1 - cos ((p.1 : ℝ) / 2) ^ 2 = sin ((p.1 : ℝ) / 2) ^ 2 := by
    nlinarith [sin_sq_add_cos_sq ((p.1 : ℝ) / 2)]
  rw [puncturedMetric]
  apply hasSectionalCurvatureAt_warpedProdTangentSpace_real_sphere standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
    (fun r ↦ (hf.apply_pos r.property).ne') p
  · rw [hf0, hdd]; field_simp; ring
  · rw [hf0, hd, htrig]; field_simp; ring

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
    filter_upwards [heq.deriv] with s hs using by simpa only [deriv_const] using hs
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
  obtain ⟨hf0, hd, hdd, hsin⟩ := hf.deriv_eq_round_of_eq_two_mul_sin h p.1.property hp
  have htrig : 1 - cos ((p.1 : ℝ) / 2) ^ 2 = sin ((p.1 : ℝ) / 2) ^ 2 := by
    nlinarith [sin_sq_add_cos_sq ((p.1 : ℝ) / 2)]
  rw [hf.scalarCurvature_puncturedMetric, hf0, hd, hdd, htrig]
  field_simp
  ring

end TauCeti.IsStandardCapProfile
