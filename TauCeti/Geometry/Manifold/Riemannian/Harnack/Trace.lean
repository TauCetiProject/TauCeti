/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Analysis.ODE.ScalarComparison
import TauCeti.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Linarith

/-!
# Integrating the geometric trace Harnack inequality

For a time-dependent family of native smooth Riemannian metrics, the trace Harnack inequality
and the bound `Ric(v,v) ≤ R g(v,v)` give a differential inequality for scalar curvature along a
moving manifold curve. Choosing half the curve velocity in the quadratic Ricci term gives the
coefficient `g(γ′,γ′) / 2`. An integrating factor yields the finite-origin endpoint estimate;
frequently valid origins tending to negative infinity yield the ancient estimate.

## Main results

* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_path_inequality_of_trace_harnack`:
  the half-velocity estimate.
* `TauCeti.Manifold.scalarCurvature_mul_sub_exp_le_of_trace_harnack`: finite-origin integration.
* `TauCeti.Manifold.scalarCurvature_mul_exp_le_of_ancient_trace_harnack`: ancient integration.

The geometric differential Harnack inequality, Ricci bound, and spacetime regularity are explicit
premises. In particular, this file does not produce those premises from a Ricci flow, completeness,
or curvature-operator bounds. No positivity of scalar curvature is required for integration.

## References

Morgan–Tian, *Ricci Flow and the Poincaré Conjecture* (2007), Theorem 4.40.
Formalization references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public section

open Bundle Set Filter
open scoped ContDiff Manifold Topology intervalIntegral

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- Evaluating trace Harnack at half a tangent velocity and using the Ricci upper bound gives
the quadratic energy term in the scalar-curvature path inequality. -/
theorem _root_.Bundle.ContMDiffRiemannianMetric.scalarCurvature_path_inequality_of_trace_harnack
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {x : M} {τ c : ℝ} (v : TangentSpace I x)
    (hRic :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v) ≤
      g.scalarCurvature x * g.inner x v v)
    (htrace : ∀ w : TangentSpace I x,
      0 ≤ τ + c + 2 * mvfderiv I g.scalarCurvature x w +
        2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨g.toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x w w)) :
    0 ≤ τ + mvfderiv I g.scalarCurvature x v + c +
      g.inner x v v / 2 * g.scalarCurvature x := by
  have hi := htrace ((1 / 2 : ℝ) • v)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hi
  nlinarith [hRic]

variable (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- Integrating geometric trace Harnack along a curve retains the elapsed-time factors at both
endpoints. The scalar curvature can have either sign, and the origin may equal the first time. -/
theorem scalarCurvature_mul_sub_exp_le_of_trace_harnack
    {T a b : ℝ} (hTa : T ≤ a) (hab : a ≤ b) (γ : ℝ → M)
    (hγ : MDifferentiableOn 𝓘(ℝ) I γ (Icc a b))
    (hR : ∀ t ∈ Icc a b, MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ)
      (fun z : ℝ × M ↦ (g z.1).scalarCurvature z.2) (t, γ t))
    (henergy : ContinuousOn (fun t ↦
      (g t).inner (γ t) (curveVelocity I γ t) (curveVelocity I γ t)) (Ioo a b))
    (henergy_int : IntervalIntegrable (fun t ↦
      (g t).inner (γ t) (curveVelocity I γ t) (curveVelocity I γ t)) MeasureTheory.volume a b)
    (hRic : ∀ t ∈ Ioo a b,
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor (γ t)
          (curveVelocity I γ t) (curveVelocity I γ t)) ≤
      (g t).scalarCurvature (γ t) *
        (g t).inner (γ t) (curveVelocity I γ t) (curveVelocity I γ t))
    (hfinite : ∀ t ∈ Ioo a b, ∀ v : TangentSpace I (γ t),
      0 ≤ deriv (fun s ↦ (g s).scalarCurvature (γ t)) t +
        (g t).scalarCurvature (γ t) / (t - T) +
        2 * mvfderiv I (g t).scalarCurvature (γ t) v +
        2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor (γ t) v v)) :
    (g a).scalarCurvature (γ a) * (a - T) * Real.exp
      (-(∫ t in a..b, (g t).inner (γ t) (curveVelocity I γ t) (curveVelocity I γ t)) / 2) ≤
      (g b).scalarCurvature (γ b) * (b - T) := by
  let f : ℝ → ℝ := fun t ↦ (g t).scalarCurvature (γ t)
  let q : ℝ → ℝ := fun t ↦
    (g t).inner (γ t) (curveVelocity I γ t) (curveVelocity I γ t) / 2
  have hf : ContinuousOn f (Icc a b) := by
    intro t ht
    exact (hR t ht).continuousAt.comp_continuousWithinAt
      (f := fun s : ℝ ↦ (s, γ s))
      (continuousWithinAt_id.prodMk (hγ.continuousOn t ht))
  have hq : ContinuousOn q (Ioo a b) := henergy.div_const 2
  have hdiff (t : ℝ) (ht : t ∈ Ioo a b) :=
    HasMFDerivAt.hasDerivAt_comp_graph (f := fun s x ↦ (g s).scalarCurvature x)
      (hasMFDerivAt_curveVelocity (hγ.mdifferentiableAt (Icc_mem_nhds ht.1 ht.2)))
      (hR t (Ioo_subset_Icc_self ht))
  have hineq (t : ℝ) (ht : t ∈ Ioo a b) :=
    (g t).scalarCurvature_path_inequality_of_trace_harnack (curveVelocity I γ t)
      (hRic t ht) (hfinite t ht)
  have h := mul_sub_mul_exp_neg_integral_le_of_deriv_add_div_add_mul_nonneg hTa hab hf
    hq (henergy_int.div_const 2) hdiff hineq
  simpa only [q, f, intervalIntegral.integral_div, neg_div] using h

/-- Frequently valid geometric finite-origin trace Harnack inequalities with origins tending to
negative infinity give the ancient integrated estimate along a native manifold curve. -/
theorem scalarCurvature_mul_exp_le_of_ancient_trace_harnack {a b : ℝ} (hab : a ≤ b) (γ : ℝ → M)
    (hγ : MDifferentiableOn 𝓘(ℝ) I γ (Icc a b))
    (hR : ∀ t ∈ Icc a b, MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ)
      (fun z : ℝ × M ↦ (g z.1).scalarCurvature z.2) (t, γ t))
    (henergy : ContinuousOn (fun t ↦
      (g t).inner (γ t) (curveVelocity I γ t) (curveVelocity I γ t)) (Ioo a b))
    (henergy_int : IntervalIntegrable (fun t ↦
      (g t).inner (γ t) (curveVelocity I γ t) (curveVelocity I γ t)) MeasureTheory.volume a b)
    (hRic : ∀ t ∈ Ioo a b,
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor (γ t)
          (curveVelocity I γ t) (curveVelocity I γ t)) ≤
      (g t).scalarCurvature (γ t) *
        (g t).inner (γ t) (curveVelocity I γ t) (curveVelocity I γ t))
    (hfinite : ∃ᶠ T : ℝ in atBot, ∀ t ∈ Ioo a b, ∀ v : TangentSpace I (γ t),
      0 ≤ deriv (fun s ↦ (g s).scalarCurvature (γ t)) t +
        (g t).scalarCurvature (γ t) / (t - T) +
        2 * mvfderiv I (g t).scalarCurvature (γ t) v +
        2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor (γ t) v v)) :
    (g a).scalarCurvature (γ a) * Real.exp
      (-(∫ t in a..b, (g t).inner (γ t) (curveVelocity I γ t) (curveVelocity I γ t)) / 2) ≤
      (g b).scalarCurvature (γ b) := by
  apply le_of_frequently_mul_sub_le (a := a) (b := b)
  apply (hfinite.and_eventually (eventually_le_atBot a)).mono
  intro T hT
  have h := scalarCurvature_mul_sub_exp_le_of_trace_harnack g hT.2 hab γ hγ hR henergy
    henergy_int hRic hT.1
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end TauCeti.Manifold
