/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Uniqueness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Jacobi fields in nonpositive sectional curvature

The Jacobi equation and the metric product rule give
`(⟨DJ, J⟩)' = |DJ|² - ⟨R(J, γ')γ', J⟩`. Consequently the squared norm of a Jacobi
field is convex along a geodesic through points of nonpositive sectional curvature.
There is no orthogonality or constant-speed normalization requirement on the field.
The statements use derivatives within the parameter set and apply to closed intervals.

The norm itself is also convex, including across zeros of the field, by
`IsJacobiFieldOn.convexOn_norm_of_sectionalCurvature_nonpos`. At a zero the norm need
not be differentiable; regularizing by `sqrt (|J|² + ε)` and taking the limit handles
these points. Norm convexity supplies the expanding estimate for the exponential differential.

A Jacobi field vanishing at two distinct parameters is zero on the interval between them
by convexity, and then everywhere on a preconnected parameter set by initial-value uniqueness.
Thus no nonzero Jacobi field vanishes twice, the no-conjugate-field input to the
nonsingularity of the exponential map. More generally, endpoint values determine a Jacobi
field uniquely. These results need neither completeness nor a constant curvature hypothesis,
and include constant geodesics and dimensions zero and one.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 10–12 (Jacobi fields and the Cartan–Hadamard theorem).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold InnerProductSpace Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V W : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {a b t : ℝ}

/-- The differentiated metric pairing underlying convexity of Jacobi-field norms:
`(⟨DJ, J⟩)' = |DJ|² - ⟨R(J, γ')γ', J⟩`. -/
theorem IsJacobiFieldOn.hasDerivWithinAt_inner_alongCurveWithin_self
    (h : IsJacobiFieldOn I γ V s) (ht : t ∈ s) :
    HasDerivWithinAt
      (fun r ↦ ⟪alongCurveWithin (leviCivitaConnection I M) γ V s r, V r⟫_ℝ)
      (‖alongCurveWithin (leviCivitaConnection I M) γ V s t‖ ^ 2 -
        ⟪(leviCivitaConnection I M).curvatureTensor (γ t) (V t)
          (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t), V t⟫_ℝ) s t := by
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hd := hm.hasDerivWithinAt_inner_alongCurveWithin (h.uniqueDiffOn t ht)
    (h.isGeodesicCurveOn.mdifferentiableOn t ht)
    (h.differentiableWithinAt_sectionCoord_alongCurveWithin ht)
    (h.differentiableWithinAt_sectionCoord ht)
  convert hd using 1
  rw [h.alongCurveWithin_alongCurveWithin_eq ht, inner_neg_left,
    real_inner_self_eq_norm_sq]
  ring

/-- The squared norm of a Jacobi field is convex on a preconnected parameter set if every
sectional curvature along its geodesic is nonpositive. Curvature is tested only on independent
pairs, but the field need not be independent of, or orthogonal to, the velocity. -/
theorem IsJacobiFieldOn.convexOn_norm_sq_of_sectionalCurvature_nonpos
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s)
    (hK : ∀ r ∈ s, ∀ u v : TangentSpace I (γ r), LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (γ r) u v ≤ 0) :
    ConvexOn ℝ s (fun r ↦ ‖V r‖ ^ 2) := by
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  refine convexOn_of_hasDerivWithinAt2_nonneg (Real.convex_iff_isPreconnected.2 hs)
    (fun r hr ↦ (h.hasDerivWithinAt_norm_sq hr).continuousWithinAt)
    (fun r hr ↦ (h.hasDerivWithinAt_norm_sq (interior_subset hr)).mono interior_subset)
    (fun r hr ↦ ((h.hasDerivWithinAt_inner_alongCurveWithin_self (interior_subset hr)).const_mul
      2).mono interior_subset) ?_
  intro r hr
  have hc := ((leviCivitaConnection I M).forall_sectionalCurvature_le_iff hm (γ r) 0).1
    (hK r (interior_subset hr)) (V r) (curveVelocityWithin I γ s r)
  simp only [zero_mul] at hc
  exact mul_nonneg (by norm_num) (sub_nonneg.2 (hc.trans (sq_nonneg _)))

private theorem IsJacobiFieldOn.hasDerivWithinAt_regularized_norm
    (h : IsJacobiFieldOn I γ V s) {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ s) :
    HasDerivWithinAt (fun r ↦ Real.sqrt (‖V r‖ ^ 2 + ε))
      (⟪alongCurveWithin (leviCivitaConnection I M) γ V s t, V t⟫_ℝ /
        Real.sqrt (‖V t‖ ^ 2 + ε)) s t := by
  convert ((h.hasDerivWithinAt_norm_sq ht).add_const ε).sqrt
    (ne_of_gt (by positivity)) using 1
  ring

private theorem IsJacobiFieldOn.convexOn_regularized_norm
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s)
    (hK : ∀ r ∈ s, ∀ u v : TangentSpace I (γ r), LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (γ r) u v ≤ 0) {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ s (fun r ↦ Real.sqrt (‖V r‖ ^ 2 + ε)) := by
  let A (r : ℝ) := ⟪alongCurveWithin (leviCivitaConnection I M) γ V s r, V r⟫_ℝ
  let B (r : ℝ) := ‖alongCurveWithin (leviCivitaConnection I M) γ V s r‖ ^ 2 -
    ⟪(leviCivitaConnection I M).curvatureTensor (γ r) (V r)
      (curveVelocityWithin I γ s r) (curveVelocityWithin I γ s r), V r⟫_ℝ
  let N (r : ℝ) := Real.sqrt (‖V r‖ ^ 2 + ε)
  have hN (r : ℝ) : 0 < N r := Real.sqrt_pos.2 (by positivity)
  have hd (r : ℝ) (hr : r ∈ s) : HasDerivWithinAt N (A r / N r) s r :=
    h.hasDerivWithinAt_regularized_norm hε hr
  refine convexOn_of_hasDerivWithinAt2_nonneg (Real.convex_iff_isPreconnected.2 hs)
    (fun r hr ↦ (hd r hr).continuousWithinAt)
    (fun r hr ↦ (hd r (interior_subset hr)).mono interior_subset)
    (f'' := fun r ↦ (B r * N r - A r * (A r / N r)) / (N r) ^ 2)
    (fun r hr ↦ ((h.hasDerivWithinAt_inner_alongCurveWithin_self
      (interior_subset hr)).div (hd r (interior_subset hr)) (ne_of_gt (hN r))).mono
      interior_subset) ?_
  intro r hr
  have hc := ((leviCivitaConnection I M).forall_sectionalCurvature_le_iff
    (isMetricCompatible_leviCivitaConnection I) (γ r) 0).1
      (hK r (interior_subset hr)) (V r) (curveVelocityWithin I γ s r)
  simp only [zero_mul] at hc
  have hcs := real_inner_mul_inner_self_le
    (alongCurveWithin (leviCivitaConnection I M) γ V s r) (V r)
  have hNsq : N r ^ 2 = ‖V r‖ ^ 2 + ε := Real.sq_sqrt (by positivity)
  have hnum : 0 ≤ B r * (N r) ^ 2 - A r ^ 2 := by
    dsimp only [A, B]
    rw [hNsq]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
    nlinarith [sq_nonneg ‖alongCurveWithin (leviCivitaConnection I M) γ V s r‖]
  apply div_nonneg _ (sq_nonneg _)
  have heq : B r * N r - A r * (A r / N r) =
      (B r * (N r) ^ 2 - A r ^ 2) / N r := by
    field_simp
  rw [heq]
  exact div_nonneg hnum (le_of_lt (hN r))

/-- The norm of a Jacobi field is convex on a preconnected parameter set under nonpositive
sectional curvature. This includes zeros of the field, constant geodesics and tangential fields;
no completeness or unit-speed assumption is needed. -/
theorem IsJacobiFieldOn.convexOn_norm_of_sectionalCurvature_nonpos
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s)
    (hK : ∀ r ∈ s, ∀ u v : TangentSpace I (γ r), LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (γ r) u v ≤ 0) :
    ConvexOn ℝ s (fun r ↦ ‖V r‖) := by
  refine ⟨Real.convex_iff_isPreconnected.2 hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hlim (r : ℝ) : Tendsto (fun ε : ℝ ↦ Real.sqrt (‖V r‖ ^ 2 + ε))
      (𝓝[>] 0) (𝓝 ‖V r‖) := by
    have ht : Tendsto (fun ε : ℝ ↦ ‖V r‖ ^ 2 + ε) (𝓝[>] 0)
        (𝓝 (‖V r‖ ^ 2 + 0)) :=
      tendsto_const_nhds.add nhdsWithin_le_nhds
    simpa only [add_zero, Real.sqrt_sq_eq_abs, abs_norm] using ht.sqrt
  exact le_of_tendsto_of_tendsto (hlim (a • x + b • y))
    ((hlim x).const_mul a |>.add ((hlim y).const_mul b))
    (eventually_nhdsWithin_of_forall fun ε hε ↦
      (h.convexOn_regularized_norm hs hK hε).2 hx hy ha hb hab)

/-- Under nonpositive sectional curvature, a Jacobi field vanishing at the ends of a
nondegenerate interval vanishes on its entire preconnected parameter set. In particular,
there is no nonzero Jacobi field with two zeros. -/
theorem IsJacobiFieldOn.eq_zero_of_endpoints_eq_zero_of_sectionalCurvature_nonpos
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s)
    (hK : ∀ r ∈ s, ∀ u v : TangentSpace I (γ r), LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (γ r) u v ≤ 0)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hVa : V a = 0) (hVb : V b = 0)
    (ht : t ∈ s) : V t = 0 := by
  wlog hlt : a < b generalizing a b
  · exact this hb ha hab.symm hVb hVa (hab.lt_or_gt.resolve_left hlt)
  have hc := h.convexOn_norm_sq_of_sectionalCurvature_nonpos hs hK
  have hz (r : ℝ) (hr : r ∈ Icc a b) : V r = 0 := by
    have hle := hc.le_max_of_mem_Icc ha hb hr
    simp only [hVa, hVb, norm_zero, sq, mul_zero, max_self] at hle
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (V r)])
  -- Vanishing on the interval forces the covariant derivative to vanish at its left end.
  have hd := (h.hasDerivWithinAt_inner_alongCurveWithin_self ha).mono (hs.Icc_subset ha hb)
  have hd₀ : HasDerivWithinAt
      (fun r ↦ ⟪alongCurveWithin (leviCivitaConnection I M) γ V s r, V r⟫_ℝ)
      0 (Icc a b) a :=
    (hasDerivWithinAt_const a (Icc a b) (0 : ℝ)).congr_of_mem
      (fun r hr ↦ by simp [hz r hr]) (left_mem_Icc.2 hlt.le)
  have heq := (uniqueDiffOn_Icc hlt a (left_mem_Icc.2 hlt.le)).eq_deriv _ hd hd₀
  simp only [hVa, map_zero, LinearMap.zero_apply, inner_zero_right, sub_zero] at heq
  have hDV : alongCurveWithin (leviCivitaConnection I M) γ V s a = 0 :=
    norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 heq)
  exact h.eq_zero_of_eq_zero_of_alongCurveWithin_eq_zero hs ha hVa hDV ht

/-- Endpoint uniqueness for Jacobi fields in nonpositive sectional curvature. The two endpoint
values, at distinct parameters, determine the field on the whole preconnected parameter set. -/
theorem IsJacobiFieldOn.eq_of_endpoints_eq_of_sectionalCurvature_nonpos
    (hV : IsJacobiFieldOn I γ V s) (hW : IsJacobiFieldOn I γ W s) (hs : IsPreconnected s)
    (hK : ∀ r ∈ s, ∀ u v : TangentSpace I (γ r), LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (γ r) u v ≤ 0)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (h₀ : V a = W a) (h₁ : V b = W b)
    (ht : t ∈ s) : V t = W t := by
  have h := (hV.add (hW.const_smul (-1))).eq_zero_of_endpoints_eq_zero_of_sectionalCurvature_nonpos
    hs hK ha hb hab (by simp [h₀]) (by simp [h₁]) ht
  simpa only [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] using h

end TauCeti.Manifold
