/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Model
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed

/-!
# All Jacobi fields in constant curvature

The tangential part of a Jacobi field has an affine coefficient, while the normal part has
model cosine and sine coefficients. Here these two descriptions give the complete formula
from arbitrary initial value and covariant derivative, without a normality hypothesis.
The parallel coefficient fields start at the orthogonal projections of the initial data onto
the normal space. The squared-length formula separates the affine tangential contribution
from the oscillating, linear, or hyperbolic normal contribution.

The parameter set stays explicit and may be a closed interval. The formulas include zero
velocity: the tangential term vanishes, the normal projections are identities, and the model
coefficients reduce to one and the affine parameter. No completeness assumption is needed.

The construction uses the normal-field solution theorem in `Jacobi.Model` and the tangential
splitting and its covariant differentiation laws in `Jacobi.Tangential`.

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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {a t κ : ℝ}

/-- In constant curvature every Jacobi field is the sum of its explicit affine tangential part
and two parallel normal fields with model cosine and sine coefficients. The initial values of
the parallel fields are the normal projections of the original initial data. -/
theorem IsJacobiFieldOn.exists_eq_affine_smul_add_curvatureCosine_smul_add_curvatureSine_smul
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ) :
    ∃ P Q : ∀ t, TangentSpace I (γ t),
      (∀ t ∈ s, alongCurveWithin (leviCivitaConnection I M) γ P s t = 0) ∧
      (∀ t ∈ s, alongCurveWithin (leviCivitaConnection I M) γ Q s t = 0) ∧
      (∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ P (γ t)) s t) ∧
      (∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ Q (γ t)) s t) ∧
      P a = V a - (ℝ ∙ curveVelocityWithin I γ s a).starProjection (V a) ∧
      Q a = alongCurveWithin (leviCivitaConnection I M) γ V s a -
        (ℝ ∙ curveVelocityWithin I γ s a).starProjection
          (alongCurveWithin (leviCivitaConnection I M) γ V s a) ∧
      ∀ t ∈ s, V t =
        ((⟪V a, curveVelocityWithin I γ s a⟫_ℝ +
          (t - a) * ⟪alongCurveWithin (leviCivitaConnection I M) γ V s a,
            curveVelocityWithin I γ s a⟫_ℝ) / ‖curveVelocityWithin I γ s a‖ ^ 2) •
              curveVelocityWithin I γ s t +
        (curvatureCosine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a) • P t +
          curvatureSine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a) • Q t) := by
  let N := fun r ↦ V r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (V r)
  have hN := h.isJacobiFieldOn_sub_starProjection_singleton hs
  have horth : ∀ r ∈ s, ⟪N r, curveVelocityWithin I γ s r⟫_ℝ = 0 :=
    fun r _ ↦ Submodule.starProjection_inner_eq_zero _ _ (Submodule.mem_span_singleton_self _)
  have hdata := (hN.forall_inner_curveVelocityWithin_eq_zero_iff hs ha).1 horth
  obtain ⟨P, Q, hP, hQ, hdP, hdQ, hPa, hQa, hform⟩ :=
    hN.exists_eq_curvatureCosine_smul_add_curvatureSine_smul hs ha hκ hdata.1 hdata.2
  refine ⟨P, Q, hP, hQ, hdP, hdQ, hPa, ?_, fun r hr ↦ ?_⟩
  · rw [hQa, h.alongCurveWithin_sub_starProjection_singleton hs ha]
  · have hsplit : V r = (ℝ ∙ curveVelocityWithin I γ s r).starProjection (V r) + N r := by
      simp [N]
    rw [hsplit, h.starProjection_singleton_eq hs ha hr]
    exact congrArg (_ + ·) (hform r hr)

/-- The squared length of an arbitrary Jacobi field in constant curvature, computed entirely
from its initial value and covariant derivative. The affine tangential contribution is
orthogonal to the normal model solution, including at zero speed. -/
theorem IsJacobiFieldOn.norm_sq_eq_affine_add_curvatureSine
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ) (ht : t ∈ s) :
    ‖V t‖ ^ 2 =
      ((⟪V a, curveVelocityWithin I γ s a⟫_ℝ +
        (t - a) * ⟪alongCurveWithin (leviCivitaConnection I M) γ V s a,
          curveVelocityWithin I γ s a⟫_ℝ) / ‖curveVelocityWithin I γ s a‖ ^ 2) ^ 2 *
            ‖curveVelocityWithin I γ s a‖ ^ 2 +
      curvatureCosine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a) ^ 2 *
        ‖V a - (ℝ ∙ curveVelocityWithin I γ s a).starProjection (V a)‖ ^ 2 +
      2 * (curvatureCosine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a) *
        curvatureSine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a)) *
        ⟪V a - (ℝ ∙ curveVelocityWithin I γ s a).starProjection (V a),
          alongCurveWithin (leviCivitaConnection I M) γ V s a -
            (ℝ ∙ curveVelocityWithin I γ s a).starProjection
              (alongCurveWithin (leviCivitaConnection I M) γ V s a)⟫_ℝ +
      curvatureSine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (t - a) ^ 2 *
        ‖alongCurveWithin (leviCivitaConnection I M) γ V s a -
          (ℝ ∙ curveVelocityWithin I γ s a).starProjection
            (alongCurveWithin (leviCivitaConnection I M) γ V s a)‖ ^ 2 := by
  let N := fun r ↦ V r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (V r)
  have hN := h.isJacobiFieldOn_sub_starProjection_singleton hs
  have horth : ∀ r ∈ s, ⟪N r, curveVelocityWithin I γ s r⟫_ℝ = 0 :=
    fun r _ ↦ Submodule.starProjection_inner_eq_zero _ _ (Submodule.mem_span_singleton_self _)
  have hdata := (hN.forall_inner_curveVelocityWithin_eq_zero_iff hs ha).1 horth
  have hnorm := hN.norm_sq_eq_curvatureSine hs ha hκ hdata.1 hdata.2 ht
  have hDN : alongCurveWithin (leviCivitaConnection I M) γ N s a =
      alongCurveWithin (leviCivitaConnection I M) γ V s a -
        (ℝ ∙ curveVelocityWithin I γ s a).starProjection
          (alongCurveWithin (leviCivitaConnection I M) γ V s a) := by
    rw [h.alongCurveWithin_sub_starProjection_singleton hs ha]
  rw [hDN] at hnorm
  have hpyth := (ℝ ∙ curveVelocityWithin I γ s t).norm_sq_eq_add_norm_sq_starProjection (V t)
  rw [Submodule.starProjection_orthogonal_val] at hpyth
  have hproj := congrArg (fun v ↦ ‖v‖ ^ 2) (h.starProjection_singleton_eq hs ha ht)
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    h.isGeodesicCurveOn.norm_curveVelocityWithin_eq hs ht ha] at hproj
  linarith only [hpyth, hproj, hnorm]

end TauCeti.Manifold
