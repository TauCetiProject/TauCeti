/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.ConstantCurvature
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential

/-!
# Explicit model coefficients for normal Jacobi fields

For a normal Jacobi field `J` along a geodesic of constant sectional curvature `κ`, the
fundamental coefficients are `curvatureCosine λ (t - a)` and `curvatureSine λ (t - a)`, where
`λ = κ * ‖γ'(a)‖ ^ 2`. These are explicit trigonometric, linear, or hyperbolic functions according
to the sign of `λ`. This file applies the fundamental-solution theorem from
`Jacobi.ConstantCurvature` without asking callers to supply scalar ODE solutions.

The decomposition has parallel coefficient fields with initial values `J(a)` and `DJ(a)`.
Their inner products are constant, giving the squared norm from arbitrary normal initial data.
Normality is checked only at the initial parameter. No unit-speed, nonconstant-geodesic,
completeness, or positive-dimension assumption is needed.

## Main results

* `TauCeti.Manifold.IsJacobiFieldOn.exists_eq_curvatureCosine_smul_add_curvatureSine_smul`:
  the explicit parallel-field decomposition.
* `TauCeti.Manifold.IsJacobiFieldOn.norm_sq_eq_curvatureSine`:
  the length formula from arbitrary normal initial data.
* `TauCeti.Manifold.IsJacobiFieldOn.norm_eq_abs_curvatureSine_mul_norm`:
  the length formula when the field initially vanishes.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 10.
* M. P. do Carmo, *Riemannian Geometry*, Chapter 5, Section 2.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {a t κ : ℝ}

/-- A normal Jacobi field in constant curvature is a sum of two parallel fields multiplied by
the explicit model cosine and sine. The parallel fields have initial values `J(a)` and `DJ(a)`.
Only the initial data need to be checked for orthogonality to the geodesic velocity. -/
theorem IsJacobiFieldOn.exists_eq_curvatureCosine_smul_add_curvatureSine_smul
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hV : ⟪V a, curveVelocityWithin I γ s a⟫_ℝ = 0)
    (hDV : ⟪alongCurveWithin (leviCivitaConnection I M) γ V s a,
      curveVelocityWithin I γ s a⟫_ℝ = 0) :
    ∃ P Q : ∀ t, TangentSpace I (γ t),
      (∀ t ∈ s, alongCurveWithin (leviCivitaConnection I M) γ P s t = 0) ∧
      (∀ t ∈ s, alongCurveWithin (leviCivitaConnection I M) γ Q s t = 0) ∧
      (∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ P (γ t)) s t) ∧
      (∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ Q (γ t)) s t) ∧
      P a = V a ∧ Q a = alongCurveWithin (leviCivitaConnection I M) γ V s a ∧
      ∀ t ∈ s, V t =
        curvatureCosine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a) • P t +
          curvatureSine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a) • Q t := by
  let c := κ * ‖curveVelocityWithin I γ s a‖ ^ 2
  have hS (t : ℝ) := (hasDerivAt_curvatureSine c (t - a)).comp t
    ((hasDerivAt_id' t).sub_const a)
  have hC (t : ℝ) := (hasDerivAt_curvatureCosine c (t - a)).comp t
    ((hasDerivAt_id' t).sub_const a)
  simp only [mul_one] at hS hC
  exact h.exists_eq_smul_add_smul hs ha hκ
    ((h.forall_inner_curveVelocityWithin_eq_zero_iff hs ha).2 ⟨hV, hDV⟩)
    hS hC hC (fun t ↦ (hS t).const_mul (-c))
    (by simp) (by simp) (by simp) (by simp)

/-- The squared norm of a normal Jacobi field in constant curvature, in terms of its initial
value and covariant derivative. The formula includes all signs of the curvature and zero speed. -/
theorem IsJacobiFieldOn.norm_sq_eq_curvatureSine
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hV : ⟪V a, curveVelocityWithin I γ s a⟫_ℝ = 0)
    (hDV : ⟪alongCurveWithin (leviCivitaConnection I M) γ V s a,
      curveVelocityWithin I γ s a⟫_ℝ = 0) (ht : t ∈ s) :
    ‖V t‖ ^ 2 =
      curvatureCosine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a) ^ 2 * ‖V a‖ ^ 2 +
        2 * (curvatureCosine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a) *
          curvatureSine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a)) *
            ⟪V a, alongCurveWithin (leviCivitaConnection I M) γ V s a⟫_ℝ +
        curvatureSine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a) ^ 2 *
          ‖alongCurveWithin (leviCivitaConnection I M) γ V s a‖ ^ 2 := by
  let c := κ * ‖curveVelocityWithin I γ s a‖ ^ 2
  have hS (t : ℝ) := (hasDerivAt_curvatureSine c (t - a)).comp t
    ((hasDerivAt_id' t).sub_const a)
  have hC (t : ℝ) := (hasDerivAt_curvatureCosine c (t - a)).comp t
    ((hasDerivAt_id' t).sub_const a)
  simp only [mul_one] at hS hC
  exact h.norm_sq_eq hs ha hκ
    ((h.forall_inner_curveVelocityWithin_eq_zero_iff hs ha).2 ⟨hV, hDV⟩)
    hS hC hC (fun t ↦ (hS t).const_mul (-c))
    (by simp) (by simp) (by simp) (by simp) ht

/-- A normal Jacobi field vanishing at `a` has length `|sλ(t-a)| |DJ(a)|`, with the model
coefficient `λ = κ |γ'(a)|²`. The derivative need only be normal at the initial parameter. -/
theorem IsJacobiFieldOn.norm_eq_abs_curvatureSine_mul_norm
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hVa : V a = 0)
    (hDV : ⟪alongCurveWithin (leviCivitaConnection I M) γ V s a,
      curveVelocityWithin I γ s a⟫_ℝ = 0) (ht : t ∈ s) :
    ‖V t‖ = |curvatureSine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a)| *
      ‖alongCurveWithin (leviCivitaConnection I M) γ V s a‖ := by
  have hsq := h.norm_sq_eq_curvatureSine hs ha hκ (by simp [hVa]) hDV ht
  simp only [hVa, norm_zero, zero_pow two_ne_zero, mul_zero, inner_zero_left, zero_add] at hsq
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1
    (by simpa only [mul_pow, sq_abs] using hsq)

end TauCeti.Manifold
