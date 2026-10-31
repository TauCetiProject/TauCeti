/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional
import TauCeti.Analysis.ODE.Wronskian
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Jacobi fields in constant curvature

Along a geodesic `γ` whose points all have sectional curvature `κ`, the curvature term of the
Jacobi equation acts on fields orthogonal to the velocity as multiplication by `κ |γ'|²`, so a
normal Jacobi field satisfies `D²J = -λ J` with the constant `λ = κ |γ'|²`. This file solves that
equation explicitly, without assuming parallel frames along `γ`.

If `φ` solves the scalar equation `φ'' = -λ φ`, then `φ' J - φ DJ` is parallel along `γ`. Taking
the fundamental pair `φ, ψ` of solutions with `φ(a) = 0, φ'(a) = 1` and `ψ(a) = 1, ψ'(a) = 0`, the
scalar Wronskian `ψ φ' - φ ψ'` is identically one, so every normal Jacobi field is

`J(t) = ψ(t) P(t) + φ(t) Q(t)`

with `P` and `Q` parallel, `P(a) = J(a)` and `Q(a) = DJ(a)`. For `λ > 0`, `λ = 0` and `λ < 0` the
pair is `(sin, cos)`, `(t, 1)` and `(sinh, cosh)` after rescaling. Since parallel fields keep their
inner products, this determines `|J|` from the initial data.

Two consequences describe conjugate points along geodesics in constant curvature.

* For `κ > 0` and a geodesic of speed `c > 0`, a normal Jacobi field vanishing at `a` has
  `|J(t)| = |sin(√κ c (t - a))| / (√κ c) · |DJ(a)|`. It vanishes again at `a + π / (√κ c)`, and a
  nonzero one does not vanish strictly in between.
* For `κ ≤ 0`, a normal Jacobi field vanishing at two distinct parameters vanishes identically.

## Main results

* `TauCeti.Manifold.IsJacobiFieldOn.alongCurveWithin_alongCurveWithin_eq_neg_smul`: the Jacobi
  equation of a normal field at a point of sectional curvature `κ`.
* `TauCeti.Manifold.IsJacobiFieldOn.alongCurveWithin_smul_sub_smul_eq_zero`: the parallel field
  `φ' J - φ DJ`.
* `TauCeti.Manifold.IsJacobiFieldOn.exists_eq_smul_add_smul`: the decomposition
  `J = ψ P + φ Q` with parallel `P`, `Q`.
* `TauCeti.Manifold.IsJacobiFieldOn.norm_sq_eq` and
  `TauCeti.Manifold.IsJacobiFieldOn.norm_eq_abs_mul_norm`: the resulting formulas for `|J(t)|`.
* `TauCeti.Manifold.IsJacobiFieldOn.norm_eq_abs_sin_mul_norm`,
  `TauCeti.Manifold.IsJacobiFieldOn.apply_add_pi_div_eq_zero` and
  `TauCeti.Manifold.IsJacobiFieldOn.apply_eq_zero_iff_of_abs_sub_lt`: conjugate points in positive
  curvature.
* `TauCeti.Manifold.IsJacobiFieldOn.apply_eq_zero_of_nonpos`: absence of conjugate
  points in nonpositive curvature.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10 (Jacobi fields and conjugate points in constant curvature).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapter 5, Section 2 (Jacobi fields
  on manifolds of constant curvature).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold InnerProductSpace Real

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

/-- At a point of sectional curvature `κ`, the Jacobi equation for a field orthogonal to the
velocity reads `D²J = -κ |γ'|² J`. -/
theorem IsJacobiFieldOn.alongCurveWithin_alongCurveWithin_eq_neg_smul
    (h : IsJacobiFieldOn I γ V s) (ht : t ∈ s)
    (hκ : (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hV : ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0) :
    alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ V s) s t =
      -((κ * ‖curveVelocityWithin I γ s t‖ ^ 2) • V t) := by
  rw [h.alongCurveWithin_alongCurveWithin_eq ht,
    hκ.curvatureTensor_apply_self_of_inner_eq_zero (torsion_leviCivitaConnection_eq_zero I) hV]

/-- The combination `f J - g DJ` of a Jacobi field and its covariant derivative, with
differentiable coefficients, has differentiable coordinate readings. -/
private theorem IsJacobiFieldOn.differentiableWithinAt_sectionCoord_smul_sub_smul
    (h : IsJacobiFieldOn I γ V s) (ht : t ∈ s) {f g : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    DifferentiableWithinAt ℝ (sectionCoord (F := E) γ
      (fun r ↦ f r • V r - g r • alongCurveWithin (leviCivitaConnection I M) γ V s r)
        (γ t)) s t := by
  have hcoord : sectionCoord (F := E) γ
      (fun r ↦ f r • V r - g r • alongCurveWithin (leviCivitaConnection I M) γ V s r) (γ t) =
      fun r ↦ f r • sectionCoord (F := E) γ V (γ t) r - g r • sectionCoord (F := E) γ
        (alongCurveWithin (leviCivitaConnection I M) γ V s) (γ t) r := by
    funext r
    simp only [sectionCoord_apply, map_sub, map_smul]
  rw [hcoord]
  exact (hf.differentiableWithinAt.smul (h.differentiableWithinAt_sectionCoord ht)).sub
    (hg.differentiableWithinAt.smul (h.differentiableWithinAt_sectionCoord_alongCurveWithin ht))

/-- **Parallel combinations of a normal Jacobi field.** On a preconnected parameter set along
which the sectional curvature is `κ`, let `J` be a Jacobi field orthogonal to the velocity and let
`φ` solve `φ'' = -κ |γ'|² φ`, the speed being constant. Then `φ' J - φ DJ` is parallel. -/
theorem IsJacobiFieldOn.alongCurveWithin_smul_sub_smul_eq_zero
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hV : ∀ t ∈ s, ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0) {φ φ' : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t, HasDerivAt φ' (-(κ * ‖curveVelocityWithin I γ s a‖ ^ 2) * φ t) t)
    (ht : t ∈ s) :
    alongCurveWithin (leviCivitaConnection I M) γ
      (fun r ↦ φ' r • V r - φ r • alongCurveWithin (leviCivitaConnection I M) γ V s r) s t =
        0 := by
  set c := κ * ‖curveVelocityWithin I γ s a‖ ^ 2
  have hc : κ * ‖curveVelocityWithin I γ s t‖ ^ 2 = c := by
    rw [h.isGeodesicCurveOn.norm_curveVelocityWithin_eq hs ht ha]
  have hu := h.uniqueDiffOn t ht
  have hneg : derivWithin (fun r ↦ -φ r) s t = -φ' t := (hφ t).neg.hasDerivWithinAt.derivWithin hu
  have hfun : (fun r ↦ φ' r • V r - φ r • alongCurveWithin (leviCivitaConnection I M) γ V s r) =
      fun r ↦ φ' r • V r +
        (fun r ↦ -φ r) r • alongCurveWithin (leviCivitaConnection I M) γ V s r := by
    funext r
    rw [neg_smul, sub_eq_add_neg]
  have h₁ : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (fun r ↦ φ' r • V r) (γ t)) s t := by
    rw [sectionCoord_smul]
    exact (hφ' t).differentiableAt.differentiableWithinAt.smul
      (h.differentiableWithinAt_sectionCoord ht)
  have h₂ : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (fun r ↦ (fun r ↦ -φ r) r •
      alongCurveWithin (leviCivitaConnection I M) γ V s r) (γ t)) s t := by
    rw [sectionCoord_smul]
    exact (hφ t).differentiableAt.neg.differentiableWithinAt.smul
      (h.differentiableWithinAt_sectionCoord_alongCurveWithin ht)
  rw [hfun, alongCurveWithin_add _ γ _ _ s h₁ h₂,
    alongCurveWithin_smul _ γ _ _ s (hφ' t).differentiableAt.differentiableWithinAt
      (h.differentiableWithinAt_sectionCoord ht),
    alongCurveWithin_smul _ γ _ (fun r ↦ -φ r) s (hφ t).differentiableAt.neg.differentiableWithinAt
      (h.differentiableWithinAt_sectionCoord_alongCurveWithin ht),
    (hφ' t).hasDerivWithinAt.derivWithin hu, hneg,
    h.alongCurveWithin_alongCurveWithin_eq_neg_smul ht (hκ t ht) (hV t ht), hc]
  module

/-- **Normal Jacobi fields in constant curvature.** On a preconnected parameter set along which the
sectional curvature is `κ`, let `J` be a Jacobi field orthogonal to the velocity. Let `φ`, `ψ` solve
`f'' = -κ |γ'|² f` with `φ(a) = 0`, `φ'(a) = 1`, `ψ(a) = 1` and `ψ'(a) = 0`. Then
`J = ψ P + φ Q` for parallel fields `P` and `Q` along `γ` with `P(a) = J(a)` and `Q(a) = DJ(a)`,
whose coordinate readings are differentiable on `s`. -/
theorem IsJacobiFieldOn.exists_eq_smul_add_smul
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hV : ∀ t ∈ s, ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0) {φ φ' ψ ψ' : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t, HasDerivAt φ' (-(κ * ‖curveVelocityWithin I γ s a‖ ^ 2) * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hψ' : ∀ t, HasDerivAt ψ' (-(κ * ‖curveVelocityWithin I γ s a‖ ^ 2) * ψ t) t)
    (hφa : φ a = 0) (hφ'a : φ' a = 1) (hψa : ψ a = 1) (hψ'a : ψ' a = 0) :
    ∃ P Q : ∀ t, TangentSpace I (γ t),
      (∀ t ∈ s, alongCurveWithin (leviCivitaConnection I M) γ P s t = 0) ∧
      (∀ t ∈ s, alongCurveWithin (leviCivitaConnection I M) γ Q s t = 0) ∧
      (∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ P (γ t)) s t) ∧
      (∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ Q (γ t)) s t) ∧
      P a = V a ∧ Q a = alongCurveWithin (leviCivitaConnection I M) γ V s a ∧
      ∀ t ∈ s, V t = ψ t • P t + φ t • Q t := by
  refine ⟨fun r ↦ φ' r • V r - φ r • alongCurveWithin (leviCivitaConnection I M) γ V s r,
    fun r ↦ (-1 : ℝ) •
      (ψ' r • V r - ψ r • alongCurveWithin (leviCivitaConnection I M) γ V s r),
    fun t ht ↦ h.alongCurveWithin_smul_sub_smul_eq_zero hs ha hκ hV hφ hφ' ht,
    fun t ht ↦ ?_, fun t ht ↦ h.differentiableWithinAt_sectionCoord_smul_sub_smul ht
      (hφ' t).differentiableAt (hφ t).differentiableAt, fun t ht ↦ ?_,
    by simp [hφa, hφ'a], by simp [hψa, hψ'a], fun t _ ↦ ?_⟩
  · rw [alongCurveWithin_const_smul,
      h.alongCurveWithin_smul_sub_smul_eq_zero hs ha hκ hV hψ hψ' ht, smul_zero]
  · rw [sectionCoord_smul]
    exact (differentiableWithinAt_const _).smul
      (h.differentiableWithinAt_sectionCoord_smul_sub_smul ht (hψ' t).differentiableAt
        (hψ t).differentiableAt)
  · have hw := wronskian_eq_one_of_hasDerivAt hφ hφ' hψ hψ' hφa hφ'a hψa hψ'a t
    calc V t = (ψ t * φ' t - φ t * ψ' t) • V t := by rw [hw, one_smul]
      _ = _ := by module

/-- **The length of a normal Jacobi field in constant curvature.** Under the hypotheses of
`IsJacobiFieldOn.exists_eq_smul_add_smul`,
`|J(t)|² = ψ(t)² |J(a)|² + 2 ψ(t) φ(t) ⟨J(a), DJ(a)⟩ + φ(t)² |DJ(a)|²`. -/
theorem IsJacobiFieldOn.norm_sq_eq
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hV : ∀ t ∈ s, ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0) {φ φ' ψ ψ' : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t, HasDerivAt φ' (-(κ * ‖curveVelocityWithin I γ s a‖ ^ 2) * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hψ' : ∀ t, HasDerivAt ψ' (-(κ * ‖curveVelocityWithin I γ s a‖ ^ 2) * ψ t) t)
    (hφa : φ a = 0) (hφ'a : φ' a = 1) (hψa : ψ a = 1) (hψ'a : ψ' a = 0) (ht : t ∈ s) :
    ‖V t‖ ^ 2 = ψ t ^ 2 * ‖V a‖ ^ 2 +
      2 * (ψ t * φ t) * ⟪V a, alongCurveWithin (leviCivitaConnection I M) γ V s a⟫_ℝ +
        φ t ^ 2 * ‖alongCurveWithin (leviCivitaConnection I M) γ V s a‖ ^ 2 := by
  have hP := fun t (ht : t ∈ s) ↦ h.alongCurveWithin_smul_sub_smul_eq_zero hs ha hκ hV hφ hφ' ht
  have hQ := fun t (ht : t ∈ s) ↦ h.alongCurveWithin_smul_sub_smul_eq_zero hs ha hκ hV hψ hψ' ht
  have hPd := fun t (ht : t ∈ s) ↦ h.differentiableWithinAt_sectionCoord_smul_sub_smul ht
    (hφ' t).differentiableAt (hφ t).differentiableAt
  have hQd := fun t (ht : t ∈ s) ↦ h.differentiableWithinAt_sectionCoord_smul_sub_smul ht
    (hψ' t).differentiableAt (hψ t).differentiableAt
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hγ := h.isGeodesicCurveOn.mdifferentiableOn
  -- The parallel fields `P = φ' J - φ DJ` and `Q = ψ' J - ψ DJ` keep their inner products.
  have hPP := hm.inner_eq_of_alongCurveWithin_eq_zero h.uniqueDiffOn hs hγ hPd hPd hP hP ht ha
  have hPQ := hm.inner_eq_of_alongCurveWithin_eq_zero h.uniqueDiffOn hs hγ hPd hQd hP hQ ht ha
  have hQQ := hm.inner_eq_of_alongCurveWithin_eq_zero h.uniqueDiffOn hs hγ hQd hQd hQ hQ ht ha
  simp only [hφa, hφ'a, hψa, hψ'a, zero_smul, one_smul, sub_zero, zero_sub] at hPP hPQ hQQ
  have hw := wronskian_eq_one_of_hasDerivAt hφ hφ' hψ hψ' hφa hφ'a hψa hψ'a t
  have hVt : V t = ψ t • (φ' t • V t - φ t • alongCurveWithin (leviCivitaConnection I M) γ V s t) -
      φ t • (ψ' t • V t - ψ t • alongCurveWithin (leviCivitaConnection I M) γ V s t) := by
    calc V t = (ψ t * φ' t - φ t * ψ' t) • V t := by rw [hw, one_smul]
      _ = _ := by module
  set p := φ' t • V t - φ t • alongCurveWithin (leviCivitaConnection I M) γ V s t
  set q := ψ' t • V t - ψ t • alongCurveWithin (leviCivitaConnection I M) γ V s t
  rw [hVt, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hPP, real_inner_comm p q, hPQ, hQQ, inner_neg_left, inner_neg_right, neg_neg]
  ring

/-- Under the hypotheses of `IsJacobiFieldOn.exists_eq_smul_add_smul`, a normal Jacobi field
vanishing at `a` has `|J(t)| = |φ(t)| |DJ(a)|`. In particular, it vanishes identically when
`DJ(a) = 0`. -/
theorem IsJacobiFieldOn.norm_eq_abs_mul_norm
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hV : ∀ t ∈ s, ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0) {φ φ' ψ ψ' : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t, HasDerivAt φ' (-(κ * ‖curveVelocityWithin I γ s a‖ ^ 2) * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hψ' : ∀ t, HasDerivAt ψ' (-(κ * ‖curveVelocityWithin I γ s a‖ ^ 2) * ψ t) t)
    (hφa : φ a = 0) (hφ'a : φ' a = 1) (hψa : ψ a = 1) (hψ'a : ψ' a = 0) (hVa : V a = 0)
    (ht : t ∈ s) :
    ‖V t‖ = |φ t| * ‖alongCurveWithin (leviCivitaConnection I M) γ V s a‖ := by
  have hsq := h.norm_sq_eq hs ha hκ hV hφ hφ' hψ hψ' hφa hφ'a hψa hψ'a ht
  rw [hVa, norm_zero, inner_zero_left] at hsq
  refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [hsq, mul_pow, sq_abs]
  ring

/-- **Normal Jacobi fields in positive constant curvature.** Along a geodesic of speed `c > 0`
through points of sectional curvature `κ > 0`, a normal Jacobi field vanishing at `a` has
`|J(t)| = |sin(√κ c (t - a))| / (√κ c) · |DJ(a)|`. -/
theorem IsJacobiFieldOn.norm_eq_abs_sin_mul_norm
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hV : ∀ t ∈ s, ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0) (hκpos : 0 < κ)
    (hγ' : curveVelocityWithin I γ s a ≠ 0) (hVa : V a = 0) (ht : t ∈ s) :
    ‖V t‖ = |Real.sin (√κ * ‖curveVelocityWithin I γ s a‖ * (t - a))| /
      (√κ * ‖curveVelocityWithin I γ s a‖) *
        ‖alongCurveWithin (leviCivitaConnection I M) γ V s a‖ := by
  set ν := √κ * ‖curveVelocityWithin I γ s a‖
  have hν : 0 < ν := mul_pos (Real.sqrt_pos.2 hκpos) (norm_pos_iff.2 hγ')
  have hν2 : κ * ‖curveVelocityWithin I γ s a‖ ^ 2 = ν ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hκpos.le]
  have hlin : ∀ t, HasDerivAt (fun r ↦ ν * (r - a)) ν t := fun t ↦
    (((hasDerivAt_id t).sub_const a).const_mul ν).congr_deriv (by simp)
  have hsin : ∀ t, HasDerivAt (fun r ↦ Real.sin (ν * (r - a)) / ν)
      (Real.cos (ν * (t - a))) t := fun t ↦
    (((hlin t).sin).div_const ν).congr_deriv (by field_simp)
  have hcos : ∀ t, HasDerivAt (fun r ↦ Real.cos (ν * (r - a)))
      (-(κ * ‖curveVelocityWithin I γ s a‖ ^ 2) * (Real.sin (ν * (t - a)) / ν)) t := fun t ↦
    ((hlin t).cos).congr_deriv (by rw [hν2]; field_simp)
  have hcos' : ∀ t, HasDerivAt (fun r ↦ Real.cos (ν * (r - a)))
      (-ν * Real.sin (ν * (t - a))) t := fun t ↦
    ((hlin t).cos).congr_deriv (by ring)
  have hsin' : ∀ t, HasDerivAt (fun r ↦ -ν * Real.sin (ν * (r - a)))
      (-(κ * ‖curveVelocityWithin I γ s a‖ ^ 2) * Real.cos (ν * (t - a))) t := fun t ↦
    (((hlin t).sin).const_mul (-ν)).congr_deriv (by rw [hν2]; ring)
  rw [h.norm_eq_abs_mul_norm hs ha hκ hV hsin hcos hcos' hsin' (by simp) (by simp) (by simp)
    (by simp) hVa ht, abs_div, abs_of_pos hν]

/-- **Conjugate points in positive constant curvature.** Along a geodesic of speed `c > 0` through
points of sectional curvature `κ > 0`, a normal Jacobi field vanishing at `a` vanishes again at
`a + π / (√κ c)`. -/
theorem IsJacobiFieldOn.apply_add_pi_div_eq_zero
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hV : ∀ t ∈ s, ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0) (hκpos : 0 < κ)
    (hγ' : curveVelocityWithin I γ s a ≠ 0) (hVa : V a = 0)
    (hb : a + π / (√κ * ‖curveVelocityWithin I γ s a‖) ∈ s) :
    V (a + π / (√κ * ‖curveVelocityWithin I γ s a‖)) = 0 := by
  have hν : 0 < √κ * ‖curveVelocityWithin I γ s a‖ :=
    mul_pos (Real.sqrt_pos.2 hκpos) (norm_pos_iff.2 hγ')
  rw [← norm_eq_zero, h.norm_eq_abs_sin_mul_norm hs ha hκ hV hκpos hγ' hVa hb, add_sub_cancel_left,
    mul_div_cancel₀ _ hν.ne', Real.sin_pi, abs_zero, zero_div, zero_mul]

/-- **No earlier conjugate points in positive constant curvature.** Along a geodesic of speed
`c > 0` through points of sectional curvature `κ > 0`, a normal Jacobi field vanishing at `a`
vanishes at a parameter `t ≠ a` with `|t - a| < π / (√κ c)` only when `DJ(a) = 0`. By
`IsJacobiFieldOn.norm_eq_abs_mul_norm` such a field vanishes identically. -/
theorem IsJacobiFieldOn.apply_eq_zero_iff_of_abs_sub_lt
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hV : ∀ t ∈ s, ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0) (hκpos : 0 < κ)
    (hγ' : curveVelocityWithin I γ s a ≠ 0) (hVa : V a = 0) (ht : t ∈ s) (hta : t ≠ a)
    (hlt : |t - a| < π / (√κ * ‖curveVelocityWithin I γ s a‖)) :
    V t = 0 ↔ alongCurveWithin (leviCivitaConnection I M) γ V s a = 0 := by
  set ν := √κ * ‖curveVelocityWithin I γ s a‖
  have hν : 0 < ν := mul_pos (Real.sqrt_pos.2 hκpos) (norm_pos_iff.2 hγ')
  have hsin : Real.sin (ν * (t - a)) ≠ 0 := by
    have hlt' : |ν * (t - a)| < π := by
      rwa [abs_mul, abs_of_pos hν, ← lt_div_iff₀' hν]
    intro h0
    exact mul_ne_zero hν.ne' (sub_ne_zero.2 hta) <|
      (Real.sin_eq_zero_iff_of_lt_of_lt (neg_lt_of_abs_lt hlt') (lt_of_abs_lt hlt')).1 h0
  rw [← norm_eq_zero, h.norm_eq_abs_sin_mul_norm hs ha hκ hV hκpos hγ' hVa ht, mul_eq_zero,
    div_eq_zero_iff, abs_eq_zero, norm_eq_zero]
  exact ⟨fun h' ↦ h'.resolve_left fun h0 ↦ h0.elim hsin hν.ne', Or.inr⟩

/-- **No conjugate points in nonpositive constant curvature.** Along a geodesic through points of
sectional curvature `κ ≤ 0`, on a preconnected parameter set, a normal Jacobi field vanishing at two
distinct parameters vanishes identically. -/
theorem IsJacobiFieldOn.apply_eq_zero_of_nonpos
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hV : ∀ t ∈ s, ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0) (hκ0 : κ ≤ 0) {b : ℝ}
    (hb : b ∈ s) (hba : b ≠ a) (hVa : V a = 0) (hVb : V b = 0) (ht : t ∈ s) : V t = 0 := by
  set c := κ * ‖curveVelocityWithin I γ s a‖ ^ 2
  have hc : c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hκ0 (by positivity)
  -- A fundamental pair `φ, ψ` of solutions of `f'' = -c f` with `φ` vanishing only at `a`.
  obtain ⟨φ, φ', ψ, ψ', hφ, hφ', hψ, hψ', hφa, hφ'a, hψa, hψ'a, hφb⟩ :
      ∃ φ φ' ψ ψ' : ℝ → ℝ, (∀ t, HasDerivAt φ (φ' t) t) ∧
        (∀ t, HasDerivAt φ' (-c * φ t) t) ∧ (∀ t, HasDerivAt ψ (ψ' t) t) ∧
        (∀ t, HasDerivAt ψ' (-c * ψ t) t) ∧ φ a = 0 ∧ φ' a = 1 ∧ ψ a = 1 ∧ ψ' a = 0 ∧
        φ b ≠ 0 := by
    rcases hc.lt_or_eq with hc | hc
    · -- `c < 0`: hyperbolic sine and cosine with frequency `μ = √(-c)`.
      set μ := √(-c)
      have hμ : 0 < μ := Real.sqrt_pos.2 (neg_pos.2 hc)
      have hμ2 : μ ^ 2 = -c := Real.sq_sqrt (neg_nonneg.2 hc.le)
      have hlin : ∀ t, HasDerivAt (fun r ↦ μ * (r - a)) μ t := fun t ↦
        (((hasDerivAt_id t).sub_const a).const_mul μ).congr_deriv (by simp)
      refine ⟨fun r ↦ Real.sinh (μ * (r - a)) / μ, fun r ↦ Real.cosh (μ * (r - a)),
        fun r ↦ Real.cosh (μ * (r - a)), fun r ↦ μ * Real.sinh (μ * (r - a)),
        fun t ↦ (((hlin t).sinh).div_const μ).congr_deriv (by field_simp),
        fun t ↦ ((hlin t).cosh).congr_deriv (by rw [← hμ2]; field_simp),
        fun t ↦ ((hlin t).cosh).congr_deriv (by ring),
        fun t ↦ (((hlin t).sinh).const_mul μ).congr_deriv (by rw [← hμ2]; ring),
        by simp, by simp, by simp, by simp, ?_⟩
      exact div_ne_zero ((Real.sinh_eq_zero.not).2 (mul_ne_zero hμ.ne' (sub_ne_zero.2 hba))) hμ.ne'
    · -- `c = 0`: the affine pair `t - a` and `1`.
      refine ⟨fun r ↦ r - a, fun _ ↦ 1, fun _ ↦ 1, fun _ ↦ 0,
        fun t ↦ (hasDerivAt_id t).sub_const a, fun t ↦ (hasDerivAt_const t 1).congr_deriv
          (by simp [hc]), fun t ↦ hasDerivAt_const t 1, fun t ↦ (hasDerivAt_const t 0).congr_deriv
          (by simp [hc]), by simp, rfl, rfl, rfl, sub_ne_zero.2 hba⟩
  -- `J(b) = 0` with `φ(b) ≠ 0` forces `DJ(a) = 0`; then `|J|²` vanishes identically.
  have hDa : alongCurveWithin (leviCivitaConnection I M) γ V s a = 0 := by
    have hnorm := h.norm_eq_abs_mul_norm hs ha hκ hV hφ hφ' hψ hψ' hφa hφ'a hψa hψ'a hVa hb
    rw [hVb, norm_zero, eq_comm, mul_eq_zero, abs_eq_zero, norm_eq_zero] at hnorm
    exact hnorm.resolve_left hφb
  have hsq := h.norm_sq_eq hs ha hκ hV hφ hφ' hψ hψ' hφa hφ'a hψa hψ'a ht
  rw [hVa, hDa, norm_zero, inner_zero_left] at hsq
  simpa using hsq

end TauCeti.Manifold
