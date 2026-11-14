/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- Read the normalization formula, which has no exposed evaluation lemma in Mathlib.
import all Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Orthonormalization of frames parallel at a point

For a metric connection, Gram–Schmidt preserves the vanishing of the covariant derivatives
of a linearly independent family at a point. Metric compatibility makes the scalar products
stationary there, so both the projection coefficients and the normalization factors have zero
derivative. Thus orthonormalizing a smooth frame parallel at a point gives an orthonormal
frame still parallel at that point.
-/

public section

open Bundle InnerProductSpace
open scoped ContDiff Manifold

namespace CovariantDerivative.IsMetricCompatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V]
  {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {v : ι → Π x : M, V x} {x : M} {cov : CovariantDerivative I F V}

attribute [local instance] IsWellOrder.toHasWellFounded

/-- Gram–Schmidt preserves a family's being parallel at a point for a metric connection. The
Gram–Schmidt vector at an index is parallel at `x` when the input sections up to and including the
index are differentiable and parallel at `x` and the input vectors strictly before the index are
linearly independent there. -/
theorem apply_gramSchmidt_eq_zero (hcov : cov.IsMetricCompatible) (j : ι)
    (hv : ∀ i ≤ j, MDiffAt (T% (v i)) x)
    (hli : LinearIndepOn ℝ (fun i ↦ v i x) (Set.Iio j)) (hzero : ∀ i ≤ j, cov (v i) x = 0) :
    cov (fun y ↦ gramSchmidt ℝ (fun i ↦ v i y) j) x = 0 := by
  classical
  let w (i : ι) (y : M) := gramSchmidt ℝ (fun k ↦ v k y) i
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hw (i : ι) (hi : i < j) : MDiffAt (T% (w i)) x :=
      MDifferentiableAt.gramSchmidt_bundle i (fun k hk ↦ hv k (hk.trans hi.le))
        (hli.mono (Set.Iio_subset_Iio hi.le))
    have hwz (i : ι) (hi : i < j) : cov (w i) x = 0 :=
      ih i hi (fun k hk ↦ hv k (hk.trans hi.le)) (hli.mono (Set.Iio_subset_Iio hi.le))
        (fun k hk ↦ hzero k (hk.trans hi.le))
    have hc (i : ι) (hi : i < j) :
        HasMFDerivAt I 𝓘(ℝ) (fun y ↦ inner ℝ (w i y) (v j y) /
          inner ℝ (w i y) (w i y)) x 0 := by
      exact (
        (hcov.hasMFDerivAt_inner_of_eq_zero (hw i hi)
          (hv j le_rfl) (hwz i hi) (hzero j le_rfl)).div
          (hcov.hasMFDerivAt_inner_of_eq_zero (hw i hi) (hw i hi) (hwz i hi) (hwz i hi))
          (inner_self_ne_zero.mpr (gramSchmidt_ne_zero_coe i
            (hli.mono (Set.Iic_subset_Iio.2 hi)).linearIndependent))).congr_mfderiv (by
            ext
            -- Evaluate in ℝ to reconcile the scalar and scalar-tangent module instances.
            change (1 / inner ℝ (w i x) (w i x)) * 0 -
              (inner ℝ (w i x) (v j x) / inner ℝ (w i x) (w i x) ^ 2) * 0 = 0
            ring)
    have ht (i : ι) (hi : i < j) : MDiffAt (T%
        ((fun y ↦ inner ℝ (w i y) (v j y) / inner ℝ (w i y) (w i y)) • w i)) x :=
      (hc i hi).mdifferentiableAt.smul_section (hw i hi)
    have hz (i : ι) (hi : i < j) :
        cov ((fun y ↦ inner ℝ (w i y) (v j y) / inner ℝ (w i y) (w i y)) • w i) x = 0 := by
      rw [cov.isCovariantDerivativeOnUniv.leibniz (hw i hi) (hc i hi).mdifferentiableAt, hwz i hi]
      simp [mvfderiv, (hc i hi).mfderiv]
    have hformula : (fun y ↦ gramSchmidt ℝ (fun i ↦ v i y) j) = v j - ∑ i ∈ Finset.Iio j,
        (fun y ↦ inner ℝ (w i y) (v j y) / inner ℝ (w i y) (w i y)) • w i := by
      funext y
      simp only [Pi.sub_apply, Finset.sum_apply, real_inner_self_eq_norm_sq]
      exact eq_sub_of_add_eq (gramSchmidt_def'' ℝ (fun i ↦ v i y) j).symm
    have hsum : MDiffAt (T% (∑ i ∈ Finset.Iio j,
        (fun y ↦ inner ℝ (w i y) (v j y) / inner ℝ (w i y) (w i y)) • w i)) x := by
      simpa only [Finset.sum_apply] using MDifferentiableAt.sum_section
        (fun i hi ↦ ht i (Finset.mem_Iio.mp hi))
    rw [hformula, cov.isCovariantDerivativeOnUniv.sub
      (hv j le_rfl) hsum,
      TauCeti.Manifold.covariantDerivative_sum cov.isCovariantDerivativeOnUniv (Set.mem_univ x)
        (fun i hi ↦ ht i (Finset.mem_Iio.mp hi)), hzero j le_rfl]
    rw [Finset.sum_eq_zero (fun i hi ↦ hz i (Finset.mem_Iio.mp hi)), sub_zero]

/-- Normalized Gram–Schmidt preserves a family's being parallel at a point for a metric
connection. The normalized Gram–Schmidt vector at an index is parallel at `x` when the input
sections up to and including the index are differentiable and parallel at `x` and the input
vectors up to and including the index are linearly independent there. -/
theorem apply_gramSchmidtNormed_eq_zero (hcov : cov.IsMetricCompatible) (j : ι)
    (hv : ∀ i ≤ j, MDiffAt (T% (v i)) x)
    (hli : LinearIndepOn ℝ (fun i ↦ v i x) (Set.Iic j)) (hzero : ∀ i ≤ j, cov (v i) x = 0) :
    cov (fun y ↦ gramSchmidtNormed ℝ (fun i ↦ v i y) j) x = 0 := by
  let w (y : M) := gramSchmidt ℝ (fun i ↦ v i y) j
  have hw : MDiffAt (T% w) x :=
    MDifferentiableAt.gramSchmidt_bundle j hv (hli.mono Set.Iio_subset_Iic_self)
  have hz : cov w x = 0 :=
    hcov.apply_gramSchmidt_eq_zero j hv (hli.mono Set.Iio_subset_Iic_self) hzero
  have hne : gramSchmidt ℝ (fun i ↦ v i x) j ≠ 0 :=
    gramSchmidt_ne_zero_coe j hli.linearIndependent
  have hinner := hcov.hasMFDerivAt_inner_of_eq_zero hw hw hz hz
  have hn : HasMFDerivAt I 𝓘(ℝ) (fun y ↦ ‖w y‖) x 0 := by
    have heq : (fun y ↦ ‖w y‖) = fun y ↦ Real.sqrt (inner ℝ (w y) (w y)) :=
      funext fun y ↦ norm_eq_sqrt_real_inner (w y)
    rw [heq]
    have hr := (Real.hasDerivAt_sqrt
      (inner_self_ne_zero.mpr hne)).hasFDerivAt.hasMFDerivAt
    exact (hr.comp x hinner).congr_mfderiv (by
      ext
      -- The target tangent space is identified with ℝ by evaluating the scalar derivative.
      change 0 * (1 / (2 * Real.sqrt (inner ℝ (w x) (w x)))) = 0
      ring)
  have hi : HasMFDerivAt I 𝓘(ℝ) (fun y ↦ ‖w y‖⁻¹) x 0 := by
    exact (hn.inv (norm_ne_zero_iff.mpr hne)).congr_mfderiv
      (by
        ext
        -- Evaluate the inverse derivative in ℝ, as for the square root above.
        change -(‖w x‖ ^ 2)⁻¹ * 0 = 0
        ring)
  have hformula : (fun y ↦ gramSchmidtNormed ℝ (fun i ↦ v i y) j) =
      (fun y ↦ ‖w y‖⁻¹) • w := (rfl)
  rw [hformula, cov.isCovariantDerivativeOnUniv.leibniz hw hi.mdifferentiableAt, hz]
  simp [mvfderiv, hi.mfderiv]

end CovariantDerivative.IsMetricCompatible
