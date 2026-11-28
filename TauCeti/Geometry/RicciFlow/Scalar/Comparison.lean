/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.Scalar.Evolution
public import TauCeti.Geometry.RicciFlow.Scalar.CurvatureComparison
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Family
public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple
import Mathlib.Algebra.Order.Chebyshev

/-!
# Geometric scalar comparison for Ricci flow

The actual native Ricci-flow metric equation implies the scalar heat inequality and its
quadratic reaction bound. On a closed manifold this gives the scalar lower comparison from
initial data, including the three-dimensional bound `-6 / (1 + 4t)`.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Chapter 4, Claim 4.2.
* P. Topping, *Lectures on the Ricci Flow*, Chapter 3.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (g : ContMDiffNondegenerateMetricFamily I M 𝓘(ℝ) ℝ)
  (r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
  (hr : ∀ s, g.metric s = (r s).toNondegenerateMetric)

include hr

/-- The scalar curvature of a Ricci flow is a supersolution of the native heat equation. -/
theorem laplaceBeltrami_le_deriv_scalarCurvature_of_ricciFlow
    {t : ℝ}
    (hflow : IsRicciFlowAt r t)
    (x : M) :
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(r t).toRiemannianMetric⟩
    laplaceBeltrami I (r t).scalarCurvature x ≤ deriv (fun s ↦ (r s).scalarCurvature x) t := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(r t).toRiemannianMetric⟩
  rw [(g.hasDerivAt_scalarCurvature_sum_leviCivitaConnection_of_ricciFlow r hr hflow x).deriv]
  exact le_add_of_nonneg_right (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _))

/-- The native scalar-curvature equation has reaction at least `2 R² / n`, where `n` is the
dimension. The zero-dimensional case is included, with the usual convention for division by zero. -/
theorem laplaceBeltrami_add_mul_sq_le_deriv_scalarCurvature_of_ricciFlow
    {t : ℝ}
    (hflow : IsRicciFlowAt r t)
    (x : M) :
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(r t).toRiemannianMetric⟩
    laplaceBeltrami I (r t).scalarCurvature x +
        (2 / Module.finrank ℝ E) * (r t).scalarCurvature x ^ 2 ≤
      deriv (fun s ↦ (r s).scalarCurvature x) t := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(r t).toRiemannianMetric⟩
  by_cases hn : Module.finrank ℝ E = 0
  · simpa only [hn, Nat.cast_zero, div_zero, zero_mul, add_zero] using
      g.laplaceBeltrami_le_deriv_scalarCurvature_of_ricciFlow r hr hflow x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  let Q : ℝ := ∑ i, ∑ j, ((leviCivitaConnection I M).ricciTensor x (b i) (b j)) ^ 2
  have htrace : (r t).scalarCurvature x =
      ∑ i, (leviCivitaConnection I M).ricciTensor x (b i) (b i) := by
    rw [(r t).scalarCurvature_eq_scalarCurvature_leviCivitaConnection rfl,
      scalarCurvature_eq_sum _ x b]
  have hdiag : (∑ i, ((leviCivitaConnection I M).ricciTensor x (b i) (b i)) ^ 2) ≤ Q := by
    exact Finset.sum_le_sum fun i _ ↦ Finset.single_le_sum
      (fun j _ ↦ sq_nonneg ((leviCivitaConnection I M).ricciTensor x (b i) (b j)))
      (Finset.mem_univ i)
  have hsq : (r t).scalarCurvature x ^ 2 ≤ (Module.finrank ℝ E : ℝ) * Q := by
    have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i ↦ (leviCivitaConnection I M).ricciTensor x (b i) (b i))
    rw [← htrace] at hs
    simp only [Finset.card_univ, Fintype.card_fin] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg _))
  have hnpos : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hreaction : (2 / Module.finrank ℝ E) * (r t).scalarCurvature x ^ 2 ≤ 2 * Q := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hnpos).mpr (by nlinarith)
  rw [(g.hasDerivAt_scalarCurvature_sum_leviCivitaConnection_of_ricciFlow r hr hflow x).deriv]
  dsimp only [Q, b] at hreaction
  linarith

variable [I.Boundaryless]

/-- At a spatial local minimum of scalar curvature along a Ricci flow, the time derivative
is at least the quadratic reaction `2 R² / n`. -/
theorem mul_sq_le_deriv_scalarCurvature_of_isLocalMin_of_ricciFlow
    {t : ℝ} (hflow : IsRicciFlowAt r t) {x : M}
    (hmin : IsLocalMin (r t).scalarCurvature x) :
    (2 / Module.finrank ℝ E) * (r t).scalarCurvature x ^ 2 ≤
      deriv (fun s ↦ (r s).scalarCurvature x) t := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(r t).toRiemannianMetric⟩
  have hΔ := laplaceBeltrami_nonneg_of_isLocalMin
    (((r t).contMDiff_scalarCurvature x).of_le (by simp))
    (BoundarylessManifold.isInteriorPoint (I := I)) hmin
  have hreaction :=
    g.laplaceBeltrami_add_mul_sq_le_deriv_scalarCurvature_of_ricciFlow r hr hflow x
  linarith

variable [CompactSpace M]

/-- On a closed manifold, the actual native Ricci-flow equation propagates every initial
scalar lower bound by `ρ / (1 - (2/n)ρ(t-a))`, as long as the comparison denominator is positive. -/
theorem div_one_sub_mul_le_scalarCurvature_of_ricciFlow
    {a b ρ : ℝ}
    (hflow : IsRicciFlowOn r (Ioo a b))
    (hb : 0 < 1 - (2 / Module.finrank ℝ E) * ρ * (b - a))
    (hinit : ∀ x, ρ ≤ (r a).scalarCurvature x) :
    ∀ t ∈ Icc a b, ∀ x,
      ρ / (1 - (2 / Module.finrank ℝ E) * ρ * (t - a)) ≤ (r t).scalarCurvature x := by
  apply TauCeti.div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin hb
    (g.continuous_scalarCurvature r hr).continuousOn
    (fun t ht x ↦ (g.hasDerivAt_scalarCurvature_sum_leviCivitaConnection_of_ricciFlow
      r hr (hflow.at r ht) x).differentiableAt)
    _ hinit
  exact fun t ht x hmin _ ↦
    g.mul_sq_le_deriv_scalarCurvature_of_isLocalMin_of_ricciFlow r hr (hflow.at r ht) hmin

/-- Nonnegative scalar curvature is preserved by an actual Ricci flow on a closed manifold. -/
theorem scalarCurvature_nonneg_of_ricciFlow
    {a b : ℝ}
    (hflow : IsRicciFlowOn r (Ioo a b))
    (hinit : ∀ x, 0 ≤ (r a).scalarCurvature x) :
    ∀ t ∈ Icc a b, ∀ x, 0 ≤ (r t).scalarCurvature x := by
  simpa only [mul_zero, zero_mul, sub_zero, zero_div] using
    g.div_one_sub_mul_le_scalarCurvature_of_ricciFlow r hr hflow (ρ := 0) (by simp) hinit

/-- The normalized three-dimensional scalar bound propagates from any nonnegative restart time,
with the same absolute time clock and both endpoints of the slab included. -/
theorem neg_six_div_one_add_four_mul_le_scalarCurvature_of_ricciFlow
    (hn : Module.finrank ℝ E = 3) {a b : ℝ} (ha : 0 ≤ a)
    (hflow : IsRicciFlowOn r (Ioo a b))
    (hinit : ∀ x, -6 / (1 + 4 * a) ≤ (r a).scalarCurvature x) :
    ∀ t ∈ Icc a b, ∀ x, -6 / (1 + 4 * t) ≤ (r t).scalarCurvature x := by
  apply TauCeti.neg_six_div_one_add_four_mul_le_of_mul_sq_le_deriv_of_isLocalMin ha
    (g.continuous_scalarCurvature r hr).continuousOn
    (fun t ht x ↦ (g.hasDerivAt_scalarCurvature_sum_leviCivitaConnection_of_ricciFlow
      r hr (hflow.at r ht) x).differentiableAt)
    _ hinit
  intro t ht x hmin _
  simpa [hn] using
    g.mul_sq_le_deriv_scalarCurvature_of_isLocalMin_of_ricciFlow r hr (hflow.at r ht) hmin

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily
