/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Curve.OrientedNormal
import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature.Reparametrization
import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature.OrientedNormal
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Total signed geodesic curvature

On an oriented surface, the integral of geodesic curvature relative to
`TauCeti.Manifold.orientedUnitNormal`
times speed is invariant under changes of parameter with transported endpoints. The nonmonotone
form requires the curve to be regular and `C²` at each point of the closed image interval, and a
continuous parameter change with a continuous derivative field, differentiable in the interior.
The monotone forms require the curve to be `C²` and the parameter change to be differentiable
with differentiable derivative only in the open interval; no nonvanishing velocity is required.
Reflection negates this integral, giving cancellation along a common boundary arc.
Curves agreeing on the open interval have equal integrals regardless of their endpoint values.

## Main results

* `Set.EqOn.integral_geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_eq`:
  equality on an open interval suffices for equality of total geodesic curvature.
* Reflection negates total signed geodesic curvature, without regularity assumptions.
* `TauCeti.Manifold.integral_geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp`:
  change of variables, including changes with critical points.
* Monotone substitution does not require endpoint regularity.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 9.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {φ : ℝ → ℝ} {t : ℝ}

variable (o : Orientation I M (Fin 2))

/-- Curves agreeing on the open interval have the same total geodesic curvature there.
Endpoint values and regularity at the endpoints do not affect the integral. -/
theorem
    _root_.Set.EqOn.integral_geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_eq
    {η : ℝ → M} {a b : ℝ} (h : Set.EqOn γ η (Set.uIoo a b))
    (o : Orientation I M (Fin 2)) :
    ∫ t in a..b, geodesicCurvature γ (orientedUnitNormal o γ) t * ‖curveVelocity I γ t‖ =
      ∫ t in a..b, geodesicCurvature η (orientedUnitNormal o η) t * ‖curveVelocity I η t‖ := by
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  have heq := h.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
  dsimp only
  rw [heq.geodesicCurvature_orientedUnitNormal_eq o, heq.norm_curveVelocity_eq (I := I)]

/-- Reflection `r ↦ d - r` negates the interval integral of geodesic curvature times speed
relative to the oriented unit normal. No regularity or integrability assumptions are needed. -/
theorem integral_geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp_const_sub
    (γ : ℝ → M) (d a b : ℝ) :
    ∫ t in a..b, geodesicCurvature (fun r ↦ γ (d - r)) (orientedUnitNormal o fun r ↦ γ (d - r)) t *
        ‖curveVelocity I (fun r ↦ γ (d - r)) t‖ =
      -∫ t in d - b..d - a, geodesicCurvature γ (orientedUnitNormal o γ) t *
        ‖curveVelocity I γ t‖ := by
  simp_rw [geodesicCurvature_orientedUnitNormal_comp_const_sub o γ,
    curveVelocity_comp_const_sub, norm_neg, neg_mul]
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_sub_left
      (fun r ↦ geodesicCurvature γ (orientedUnitNormal o γ) r * ‖curveVelocity I γ r‖) d]

/-- The interior density pullback suffices for equality of the interval integrals. -/
private theorem integral_density_comp {a b : ℝ} {φ' : ℝ → ℝ}
    (hγ : ∀ r ∈ φ '' Set.uIoo a b, ContMDiffAt 𝓘(ℝ) I 2 γ r)
    (hφ : ∀ r ∈ Set.uIoo a b, HasDerivAt φ (φ' r) r)
    (hφ' : ∀ r ∈ Set.uIoo a b, DifferentiableAt ℝ φ' r) :
    ∫ t in a..b, geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t *
        ‖curveVelocity I (γ ∘ φ) t‖ =
      ∫ t in a..b, (geodesicCurvature γ (orientedUnitNormal o γ) (φ t) *
        ‖curveVelocity I γ (φ t)‖) * φ' t := by
  apply intervalIntegral.integral_congr_uIoo
  intro r hr
  have heq : deriv φ =ᶠ[𝓝 r] φ' := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
    exact (hφ x hx).deriv
  dsimp only
  rw [← (hφ r hr).deriv]
  exact geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp o
    (hγ (φ r) ⟨r, hr, rfl⟩) (hφ r hr).differentiableAt
    ((hφ' r hr).congr_of_eventuallyEq heq)

/-- On an oriented surface, a change of parameter preserves the interval integral of geodesic
curvature relative to the oriented unit normal times speed, with transported endpoints.
The curve is regular and `C²` (`ContMDiffAt`) at each point of the closed image interval.
The parameter change and its derivative field are continuous on `Set.uIcc a b`; the derivative
field is differentiable at each point of `Set.uIoo a b`. Its sign is unrestricted. -/
theorem integral_geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp
    {a b : ℝ} {φ' : ℝ → ℝ}
    (hγ : ∀ r ∈ φ '' Set.uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ r)
    (hφc : ContinuousOn φ (Set.uIcc a b))
    (hφ : ∀ r ∈ Set.uIoo a b, HasDerivAt φ (φ' r) r)
    (hφ'c : ContinuousOn φ' (Set.uIcc a b))
    (hφ' : ∀ r ∈ Set.uIoo a b, DifferentiableAt ℝ φ' r)
    (hne : ∀ r ∈ φ '' Set.uIcc a b, curveVelocity I γ r ≠ 0) :
    ∫ t in a..b, geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t *
        ‖curveVelocity I (γ ∘ φ) t‖ =
      ∫ t in φ a..φ b, geodesicCurvature γ (orientedUnitNormal o γ) t *
        ‖curveVelocity I γ t‖ := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
    (F := E) (V := fun x : M ↦ TangentSpace I x)
  have hnorm : ∀ r ∈ φ '' Set.uIcc a b, ContinuousAt (fun r ↦ ‖curveVelocity I γ r‖) r :=
    fun r hr ↦ ((hγ r hr).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).continuousAt_norm_curveVelocity
  calc
    _ = ∫ t in a..b, (geodesicCurvature γ (orientedUnitNormal o γ) (φ t) *
        ‖curveVelocity I γ (φ t)‖) * φ' t :=
      integral_density_comp o (fun r hr ↦ hγ r (image_mono uIoo_subset_uIcc_self hr)) hφ hφ'
    _ = _ := intervalIntegral.integral_comp_mul_deriv''
      (g := fun r ↦ geodesicCurvature γ (orientedUnitNormal o γ) r * ‖curveVelocity I γ r‖) hφc
      (fun r hr ↦ (hφ r hr).hasDerivWithinAt) hφ'c
      (fun r hr ↦ ((continuousAt_geodesicCurvature_orientedUnitNormal o (hγ r hr) (hne r hr)).mul
        (hnorm r hr)).continuousWithinAt)

/-- A change of parameter with nonnegative derivative preserves total signed geodesic curvature.
Only `C²` smoothness of the original curve on the open image and differentiability of the
parameter change and its derivative in the interior are required. Endpoint regularity and
nonvanishing velocity are unnecessary. -/
theorem integral_geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp_of_deriv_nonneg
    {a b : ℝ} (hγ : ∀ r ∈ φ '' Set.uIoo a b, ContMDiffAt 𝓘(ℝ) I 2 γ r)
    (hφc : ContinuousOn φ (Set.uIcc a b))
    (hφ : ∀ r ∈ Set.uIoo a b, DifferentiableAt ℝ φ r)
    (hφ' : ∀ r ∈ Set.uIoo a b, DifferentiableAt ℝ (deriv φ) r)
    (hφ₀ : ∀ r ∈ Set.uIoo a b, 0 ≤ deriv φ r) :
    ∫ t in a..b, geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t *
        ‖curveVelocity I (γ ∘ φ) t‖ =
      ∫ t in φ a..φ b, geodesicCurvature γ (orientedUnitNormal o γ) t *
        ‖curveVelocity I γ t‖ := by
  calc
    _ = ∫ t in a..b, (geodesicCurvature γ (orientedUnitNormal o γ) (φ t) *
        ‖curveVelocity I γ (φ t)‖) * deriv φ t :=
      integral_density_comp o hγ (fun r hr ↦ (hφ r hr).hasDerivAt) hφ'
    _ = _ := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (g := fun r ↦ geodesicCurvature γ (orientedUnitNormal o γ) r * ‖curveVelocity I γ r‖) hφc
      (fun r hr ↦ (hφ r hr).hasDerivAt) hφ₀

/-- A change of parameter with nonpositive derivative preserves total signed geodesic curvature
with transported endpoints. Only `C²` smoothness of the original curve on the open image and
interior differentiability of the parameter change and its derivative are required; the curve
may have corners at the endpoints or vanishing velocity. -/
theorem integral_geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp_of_deriv_nonpos
    {a b : ℝ} (hγ : ∀ r ∈ φ '' Set.uIoo a b, ContMDiffAt 𝓘(ℝ) I 2 γ r)
    (hφc : ContinuousOn φ (Set.uIcc a b))
    (hφ : ∀ r ∈ Set.uIoo a b, DifferentiableAt ℝ φ r)
    (hφ' : ∀ r ∈ Set.uIoo a b, DifferentiableAt ℝ (deriv φ) r)
    (hφ₀ : ∀ r ∈ Set.uIoo a b, deriv φ r ≤ 0) :
    ∫ t in a..b, geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t *
        ‖curveVelocity I (γ ∘ φ) t‖ =
      ∫ t in φ a..φ b, geodesicCurvature γ (orientedUnitNormal o γ) t *
        ‖curveVelocity I γ t‖ := by
  calc
    _ = ∫ t in a..b, (geodesicCurvature γ (orientedUnitNormal o γ) (φ t) *
        ‖curveVelocity I γ (φ t)‖) * deriv φ t :=
      integral_density_comp o hγ (fun r hr ↦ (hφ r hr).hasDerivAt) hφ'
    _ = _ := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
      (g := fun r ↦ geodesicCurvature γ (orientedUnitNormal o γ) r * ‖curveVelocity I γ r‖) hφc
      (fun r hr ↦ (hφ r hr).hasDerivAt) hφ₀

end TauCeti.Manifold
