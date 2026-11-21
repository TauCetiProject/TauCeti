/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Ricci contraction of index forms in a parallel frame

The sum of index densities of scalar multiples of an orthonormal parallel frame is the
dimension times the squared scalar derivative minus the scalar-square-weighted Ricci tensor.
Orthonormality and parallelism are required only at the evaluation parameter, or in the open
segment for the integrated identity. The fields may be arbitrary elsewhere.

The integrated identity is stated for the native index form and any scalar test function on
any oriented interval. Integrability of each index density and of the scalar derivative
energy implies integrability of the weighted Ricci term. It supplies the trace calculation
used in index-form comparison arguments; it assumes the parallel fields as inputs.

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
  {γ : ℝ → M} {s : Set ℝ} {t a b : ℝ}

/-- Summing diagonal index densities in a frame orthonormal and parallel at the evaluation
parameter contracts curvature to the Ricci tensor. No condition is imposed elsewhere. -/
theorem sum_indexFormIntegrandWithin_smul_of_alongCurveWithin_eq_zero
    {ι : Type*} [Fintype ι] (e : ι → ∀ r, TangentSpace I (γ r))
    (hcard : Fintype.card ι = Module.finrank ℝ E)
    (hon : Orthonormal ℝ (fun i ↦ e i t))
    (φ : ℝ → ℝ) (hφ : DifferentiableWithinAt ℝ φ s t)
    (he : ∀ i, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (e i) (γ t)) s t)
    (hparallel : ∀ i, alongCurveWithin (leviCivitaConnection I M) γ (e i) s t = 0) :
    ∑ i, indexFormIntegrandWithin I γ
        (fun r ↦ φ r • e i r) (fun r ↦ φ r • e i r) s t =
      Fintype.card ι * derivWithin φ s t ^ 2 - φ t ^ 2 *
        (leviCivitaConnection I M).ricciTensor (γ t)
          (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t) := by
  classical
  let b₀ := basisOfLinearIndependentOfCardEqFinrank' (fun i ↦ e i t)
    hon.linearIndependent (hcard.trans (TauCeti.finrank_tangentSpace _).symm)
  let b := b₀.toOrthonormalBasis (by simpa only [b₀,
    coe_basisOfLinearIndependentOfCardEqFinrank'] using hon)
  have hb (i : ι) : b i = e i t := by
    simp only [b, Module.Basis.coe_toOrthonormalBasis, b₀,
      coe_basisOfLinearIndependentOfCardEqFinrank']
  have hterm (i : ι) : indexFormIntegrandWithin I γ
      (fun r ↦ φ r • e i r) (fun r ↦ φ r • e i r) s t =
      derivWithin φ s t ^ 2 - φ t ^ 2 *
        inner ℝ ((leviCivitaConnection I M).curvatureTensor (γ t) (e i t)
          (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (e i t) := by
    rw [indexFormIntegrandWithin_smul_smul_of_alongCurveWithin_eq_zero φ φ hφ hφ
      (he i) (he i) (hparallel i) (hparallel i)]
    simp only [real_inner_self_eq_norm_sq, hon.1 i, mul_one, pow_two]
  have hRic := (leviCivitaConnection I M).ricciTensor_eq_sum_inner (γ t) b
    (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)
  simp only [hb] at hRic
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hRic]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _

/-- Ricci contraction of scalar-multiple index densities with unrestricted derivatives. -/
theorem sum_indexFormIntegrand_smul_of_alongCurve_eq_zero
    {ι : Type*} [Fintype ι] (e : ι → ∀ r, TangentSpace I (γ r))
    (hcard : Fintype.card ι = Module.finrank ℝ E)
    (hon : Orthonormal ℝ (fun i ↦ e i t))
    (φ : ℝ → ℝ) (hφ : DifferentiableAt ℝ φ t)
    (he : ∀ i, DifferentiableAt ℝ (sectionCoord (F := E) γ (e i) (γ t)) t)
    (hparallel : ∀ i, alongCurve (leviCivitaConnection I M) γ (e i) t = 0) :
    ∑ i, indexFormIntegrand I γ (fun r ↦ φ r • e i r) (fun r ↦ φ r • e i r) t =
      Fintype.card ι * deriv φ t ^ 2 - φ t ^ 2 *
        (leviCivitaConnection I M).ricciTensor (γ t)
          (curveVelocity I γ t) (curveVelocity I γ t) := by
  simpa only [indexFormIntegrandWithin_univ, derivWithin_univ, curveVelocityWithin_univ]
    using sum_indexFormIntegrandWithin_smul_of_alongCurveWithin_eq_zero e hcard hon φ
      hφ.differentiableWithinAt (fun i ↦ (he i).differentiableWithinAt) (s := univ)
      (by simpa only [alongCurveWithin_univ] using hparallel)

/-- The sum of index forms in a locally orthonormal parallel frame is the scalar derivative
energy times the dimension minus the weighted Ricci integral. Each index density and the
scalar derivative energy must be integrable; weighted Ricci integrability follows. -/
theorem sum_indexForm_smul
    {ι : Type*} [Fintype ι] (e : ι → ∀ r, TangentSpace I (γ r))
    (hcard : Fintype.card ι = Module.finrank ℝ E) (φ : ℝ → ℝ)
    (hon : ∀ r ∈ uIoo a b, Orthonormal ℝ (fun i ↦ e i r))
    (hφ : ∀ r ∈ uIoo a b, DifferentiableAt ℝ φ r)
    (he : ∀ r ∈ uIoo a b, ∀ i,
      DifferentiableAt ℝ (sectionCoord (F := E) γ (e i) (γ r)) r)
    (hparallel : ∀ r ∈ uIoo a b, ∀ i,
      alongCurve (leviCivitaConnection I M) γ (e i) r = 0)
    (hD : IntervalIntegrable (fun r ↦ deriv φ r ^ 2) volume a b)
    (hint : ∀ i, IntervalIntegrable (fun r ↦ indexFormIntegrand I γ
      (fun t ↦ φ t • e i t) (fun t ↦ φ t • e i t) r) volume a b) :
    ∑ i, indexForm I γ (fun r ↦ φ r • e i r) (fun r ↦ φ r • e i r) a b =
      Fintype.card ι * (∫ r in a..b, deriv φ r ^ 2) -
      ∫ r in a..b, φ r ^ 2 * (leviCivitaConnection I M).ricciTensor (γ r)
        (curveVelocity I γ r) (curveVelocity I γ r) := by
  classical
  have htrace (r : ℝ) (hr : r ∈ uIoo a b) :=
    sum_indexFormIntegrand_smul_of_alongCurve_eq_zero e hcard (hon r hr) φ
      (hφ r hr) (he r hr) (hparallel r hr)
  have hsum : IntervalIntegrable (fun r ↦ ∑ i, indexFormIntegrand I γ
      (fun t ↦ φ t • e i t) (fun t ↦ φ t • e i t) r) volume a b := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun i _ ↦ hint i)
  have hRic : IntervalIntegrable (fun r ↦ φ r ^ 2 *
      (leviCivitaConnection I M).ricciTensor (γ r)
        (curveVelocity I γ r) (curveVelocity I γ r)) volume a b :=
    ((hD.const_mul (Fintype.card ι : ℝ)).sub hsum).congr_uIoo fun r hr ↦ by
      dsimp
      linarith [htrace r hr]
  simp_rw [indexForm_def]
  rw [← intervalIntegral.integral_finsetSum (fun i _ ↦ hint i),
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hD.const_mul _) hRic]
  exact intervalIntegral.integral_congr_uIoo htrace

end TauCeti.Manifold
