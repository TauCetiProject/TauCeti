/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Analysis.SpecialFunctions.Exp.Cutoff

/-!
# Ricci contraction of index forms in a parallel frame

Multiplying a parallel tangent field by a scalar function gives an index density equal to
the squared scalar derivative times the field's squared length, minus the scalar square
times its curvature term. Summing in an orthonormal parallel frame contracts curvature to
the Ricci tensor. These identities use the native connection, velocity and index form.

The scalar exponential cutoff supplies a length-independent bound for the resulting Ricci
integral. Parallel-frame construction and nonnegativity of the index form along a minimizing
geodesic are separate geometric inputs.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Claim 9.47.
* Related formalizations: https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Bundle CovariantDerivative MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}

/-- The diagonal index density of a scalar multiple of a parallel field, with derivatives
within any parameter set. Only differentiability of the scalar and the field's coordinate
reading at the evaluation point is required. -/
theorem indexFormIntegrandWithin_smul_of_alongCurveWithin_eq_zero
    (φ : ℝ → ℝ) (hφ : DifferentiableWithinAt ℝ φ s t)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hparallel : alongCurveWithin (leviCivitaConnection I M) γ V s t = 0) :
    indexFormIntegrandWithin I γ (fun r ↦ φ r • V r) (fun r ↦ φ r • V r) s t =
      derivWithin φ s t ^ 2 * inner ℝ (V t) (V t) - φ t ^ 2 *
        inner ℝ ((leviCivitaConnection I M).curvatureTensor (γ t) (V t)
          (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (V t) := by
  rw [indexFormIntegrandWithin_def,
    alongCurveWithin_smul _ γ V φ s hφ hV, hparallel, smul_zero, add_zero]
  simp only [real_inner_smul_left, real_inner_smul_right, map_smul,
    LinearMap.smul_apply]
  ring

/-- Summing diagonal index densities of scalar multiples of an orthonormal parallel frame
gives the dimension times the squared scalar derivative minus the weighted Ricci contraction.
The frame index is any finite type, including the empty type. -/
theorem sum_indexFormIntegrandWithin_smul_of_alongCurveWithin_eq_zero
    {ι : Type*} [Fintype ι] (e : ∀ r, OrthonormalBasis ι ℝ (TangentSpace I (γ r)))
    (φ : ℝ → ℝ) (hφ : DifferentiableWithinAt ℝ φ s t)
    (he : ∀ i, DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ e r i) (γ t)) s t)
    (hparallel : ∀ i,
      alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ e r i) s t = 0) :
    ∑ i, indexFormIntegrandWithin I γ
        (fun r ↦ φ r • e r i) (fun r ↦ φ r • e r i) s t =
      Fintype.card ι * derivWithin φ s t ^ 2 - φ t ^ 2 *
        (leviCivitaConnection I M).ricciTensor (γ t)
          (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t) := by
  classical
  have hterm (i : ι) : indexFormIntegrandWithin I γ
      (fun r ↦ φ r • e r i) (fun r ↦ φ r • e r i) s t =
      derivWithin φ s t ^ 2 - φ t ^ 2 *
        inner ℝ ((leviCivitaConnection I M).curvatureTensor (γ t) (e t i)
          (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (e t i) := by
    rw [indexFormIntegrandWithin_smul_of_alongCurveWithin_eq_zero φ hφ
      (he i) (hparallel i), (e t).inner_eq_one, mul_one]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    (leviCivitaConnection I M).ricciTensor_eq_sum_inner (γ t) (e t)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _

/-- The trace of the cutoff index densities integrates to the derivative energy minus
the cutoff-weighted Ricci integral. Parallelism is needed only in the open segment. -/
theorem integral_sum_indexFormIntegrand_cutoff_smul
    {ι : Type*} [Fintype ι] (e : ∀ r, OrthonormalBasis ι ℝ (TangentSpace I (γ r)))
    (L scale : ℝ)
    (he : ∀ r ∈ uIoo 0 L, ∀ i, DifferentiableAt ℝ
      (sectionCoord (F := E) γ (fun t ↦ e t i) (γ r)) r)
    (hparallel : ∀ r ∈ uIoo 0 L, ∀ i,
      alongCurve (leviCivitaConnection I M) γ (fun t ↦ e t i) r = 0)
    (hRic : IntervalIntegrable (fun r ↦ (leviCivitaConnection I M).ricciTensor (γ r)
      (curveVelocity I γ r) (curveVelocity I γ r)) volume 0 L) :
    (∫ r in (0 : ℝ)..L, ∑ i, indexFormIntegrand I γ
        (fun t ↦ ExponentialCutoff.cutoff L scale t • e t i)
        (fun t ↦ ExponentialCutoff.cutoff L scale t • e t i) r) =
      Fintype.card ι * (∫ r in (0 : ℝ)..L,
        deriv (ExponentialCutoff.cutoff L scale) r ^ 2) -
      ∫ r in (0 : ℝ)..L, ExponentialCutoff.cutoff L scale r ^ 2 *
        (leviCivitaConnection I M).ricciTensor (γ r)
          (curveVelocity I γ r) (curveVelocity I γ r) := by
  have hD : Continuous (fun r ↦ deriv (ExponentialCutoff.cutoff L scale) r ^ 2) := by
    simp_rw [(ExponentialCutoff.hasDerivAt_cutoff L scale _).deriv]
    fun_prop
  have hφ : Continuous (fun r : ℝ ↦ ExponentialCutoff.cutoff L scale r ^ 2) :=
    (ExponentialCutoff.contDiff_cutoff L scale).continuous.pow 2
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
    ((hD.intervalIntegrable 0 L).const_mul _) (hRic.continuousOn_mul hφ.continuousOn)]
  apply intervalIntegral.integral_congr_uIoo
  intro r hr
  simpa only [indexFormIntegrandWithin_univ, derivWithin_univ, curveVelocityWithin_univ]
    using sum_indexFormIntegrandWithin_smul_of_alongCurveWithin_eq_zero
      (s := univ) (t := r) e (ExponentialCutoff.cutoff L scale)
      (ExponentialCutoff.hasDerivAt_cutoff L scale r).differentiableAt.differentiableWithinAt
      (fun i ↦ (he r hr i).differentiableWithinAt)
      (by simpa only [alongCurveWithin_univ] using hparallel r hr)

/-- A nonnegative trace index integral bounds the unweighted Ricci integral independently
of the segment length. The coefficient is the full frame dimension, rather than the
normal dimension. The frame and its parallelism are supplied as hypotheses. -/
theorem integral_ricci_le_of_integral_sum_indexFormIntegrand_nonneg
    {ι : Type*} [Fintype ι] (e : ∀ r, OrthonormalBasis ι ℝ (TangentSpace I (γ r)))
    {L scale K : ℝ} (hL : 0 ≤ L) (hscale : 0 < scale) (hK : 0 ≤ K)
    (he : ∀ r ∈ uIoo 0 L, ∀ i, DifferentiableAt ℝ
      (sectionCoord (F := E) γ (fun t ↦ e t i) (γ r)) r)
    (hparallel : ∀ r ∈ uIoo 0 L, ∀ i,
      alongCurve (leviCivitaConnection I M) γ (fun t ↦ e t i) r = 0)
    (hbound : ∀ r ∈ Icc 0 L, (leviCivitaConnection I M).ricciTensor (γ r)
      (curveVelocity I γ r) (curveVelocity I γ r) ≤ K)
    (hindex : 0 ≤ ∫ r in (0 : ℝ)..L, ∑ i, indexFormIntegrand I γ
      (fun t ↦ ExponentialCutoff.cutoff L scale t • e t i)
      (fun t ↦ ExponentialCutoff.cutoff L scale t • e t i) r) :
    (∫ r in (0 : ℝ)..L, (leviCivitaConnection I M).ricciTensor (γ r)
      (curveVelocity I γ r) (curveVelocity I γ r)) ≤
        Fintype.card ι * (2 * scale) + K * (4 / scale) := by
  by_cases hRic : IntervalIntegrable (fun r ↦ (leviCivitaConnection I M).ricciTensor (γ r)
      (curveVelocity I γ r) (curveVelocity I γ r)) volume 0 L
  swap
  · rw [intervalIntegral.integral_undef hRic]
    positivity
  apply ExponentialCutoff.integral_le_of_integral_cutoff_sq_mul_le
    hL hscale hK hRic hbound
  rw [integral_sum_indexFormIntegrand_cutoff_smul e L scale he hparallel hRic] at hindex
  exact (sub_nonneg.mp hindex).trans
    (mul_le_mul_of_nonneg_left (ExponentialCutoff.integral_deriv_cutoff_sq_le hscale.le)
      (Nat.cast_nonneg _))

end TauCeti.Manifold
