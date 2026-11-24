/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Sqrt
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Pairing

/-!
# Norm estimates for sections of a metric vector bundle

Metric compatibility expresses the differential of the squared norm of a section through its
covariant derivative. Cauchy--Schwarz then gives
`|grad |σ|²|² ≤ 4 |σ|² |∇σ|²`, with the Hilbert--Schmidt norm on `∇σ`. Away from the zero locus,
the same calculation gives Kato's inequality `|grad |σ||² ≤ |∇σ|²`.

These estimates control gradient cross terms in localized tensor-energy arguments.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Chapter 9.
* [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
* [frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative.IsMetricCompatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V]
  {cov : CovariantDerivative I F V} {σ : Π x : M, V x} {x : M}

/-- The differential of the norm of a section away from its zero locus. -/
theorem mvfderiv_norm (hcov : cov.IsMetricCompatible) (hσ : MDiffAt (T% σ) x)
    (hσx : σ x ≠ 0) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ ‖σ y‖) x v = ⟪cov σ x v, σ x⟫ / ‖σ x‖ := by
  have hn : ‖σ x‖ ≠ 0 := norm_ne_zero_iff.2 hσx
  have hd : MDiffAt (fun y ↦ ‖σ y‖ ^ 2) x := by
    simpa only [real_inner_self_eq_norm_sq] using hσ.inner_bundle hσ
  have heq : (fun y ↦ ‖σ y‖) = Real.sqrt ∘ (fun y ↦ ‖σ y‖ ^ 2) := by
    funext y
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [heq, TauCeti.mvfderiv_scalar_comp hd
    ((Real.hasDerivAt_sqrt (pow_ne_zero 2 hn)).differentiableAt)]
  simp only [smul_apply, smul_eq_mul,
    (Real.hasDerivAt_sqrt (pow_ne_zero 2 hn)).deriv, Real.sqrt_sq (norm_nonneg _)]
  have hd : mvfderiv I (fun y ↦ ‖σ y‖ ^ 2) x v = 2 * ⟪cov σ x v, σ x⟫ := by
    simpa only [real_inner_self_eq_norm_sq, real_inner_comm (σ x), two_mul] using
      hcov.mvfderiv_inner_eq (fun _ ↦ v) hσ hσ
  rw [hd]
  field_simp

/-- The differential of a positive regularization of the norm of a section. -/
theorem mvfderiv_sqrt_norm_sq_add (hcov : cov.IsMetricCompatible)
    (hσ : MDiffAt (T% σ) x) {ε : ℝ} (hε : 0 < ε) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ Real.sqrt (‖σ y‖ ^ 2 + ε)) x v =
      ⟪cov σ x v, σ x⟫ / Real.sqrt (‖σ x‖ ^ 2 + ε) := by
  have hd : MDiffAt (fun y ↦ ‖σ y‖ ^ 2 + ε) x := by
    simpa only [real_inner_self_eq_norm_sq, Pi.add_def] using
      (hσ.inner_bundle hσ).add (mdifferentiableAt_const (c := ε))
  have hpos : 0 < ‖σ x‖ ^ 2 + ε := by positivity
  -- The scalar chain rule takes a composition; this equation expands only `Function.comp`.
  rw [show (fun y ↦ Real.sqrt (‖σ y‖ ^ 2 + ε)) =
      Real.sqrt ∘ (fun y ↦ ‖σ y‖ ^ 2 + ε) from rfl,
    TauCeti.mvfderiv_scalar_comp hd
      ((Real.hasDerivAt_sqrt (ne_of_gt hpos)).differentiableAt)]
  simp only [smul_apply, smul_eq_mul,
    (Real.hasDerivAt_sqrt (ne_of_gt hpos)).deriv,
    TauCeti.mvfderiv_add_const]
  have hd : mvfderiv I (fun y ↦ ‖σ y‖ ^ 2) x v = 2 * ⟪cov σ x v, σ x⟫ := by
    simpa only [real_inner_self_eq_norm_sq, real_inner_comm (σ x), two_mul] using
      hcov.mvfderiv_inner_eq (fun _ ↦ v) hσ hσ
  rw [hd]
  field_simp

variable [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The squared gradient of section energy is at most four times the energy and the squared
Hilbert--Schmidt norm of the covariant derivative. -/
theorem norm_sq_mgradient_norm_sq_le (hcov : cov.IsMetricCompatible)
    (hσ : MDiffAt (T% σ) x) :
    ‖TauCeti.Manifold.mgradient I (fun y ↦ ‖σ y‖ ^ 2) x‖ ^ 2 ≤
      4 * ‖σ x‖ ^ 2 * cov.innerCovariantDerivative σ σ x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [← b.sum_sq_inner_left, cov.innerCovariantDerivative_eq_sum σ σ x b, Finset.mul_sum]
  simp only [TauCeti.Manifold.inner_mgradient, real_inner_self_eq_norm_sq]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hd : mvfderiv I (fun y ↦ ‖σ y‖ ^ 2) x (b i) =
      2 * ⟪cov σ x (b i), σ x⟫ := by
    simpa only [real_inner_self_eq_norm_sq, real_inner_comm (σ x), two_mul] using
      hcov.mvfderiv_inner_eq (fun _ ↦ b i) hσ hσ
  rw [hd]
  have h := real_inner_mul_inner_self_le (cov σ x (b i)) (σ x)
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith only [h]

/-- Kato's inequality for the norm of a differentiable section away from its zero locus. -/
theorem norm_sq_mgradient_norm_le (hcov : cov.IsMetricCompatible)
    (hσ : MDiffAt (T% σ) x) (hσx : σ x ≠ 0) :
    ‖TauCeti.Manifold.mgradient I (fun y ↦ ‖σ y‖) x‖ ^ 2 ≤
      cov.innerCovariantDerivative σ σ x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [← b.sum_sq_inner_left, cov.innerCovariantDerivative_eq_sum σ σ x b]
  simp only [TauCeti.Manifold.inner_mgradient, hcov.mvfderiv_norm hσ hσx,
    real_inner_self_eq_norm_sq]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have h := real_inner_mul_inner_self_le (cov σ x (b i)) (σ x)
  simp only [real_inner_self_eq_norm_sq] at h
  rw [div_pow, div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.2 hσx))]
  simpa only [pow_two] using h

/-- Kato's inequality for the positive regularization `sqrt (|σ|² + ε)`, including zeros of the
section. The right side is the squared Hilbert--Schmidt norm of its covariant derivative. -/
theorem norm_sq_mgradient_sqrt_norm_sq_add_le (hcov : cov.IsMetricCompatible)
    (hσ : MDiffAt (T% σ) x) {ε : ℝ} (hε : 0 < ε) :
    ‖TauCeti.Manifold.mgradient I (fun y ↦ Real.sqrt (‖σ y‖ ^ 2 + ε)) x‖ ^ 2 ≤
      cov.innerCovariantDerivative σ σ x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [← b.sum_sq_inner_left, cov.innerCovariantDerivative_eq_sum σ σ x b]
  simp only [TauCeti.Manifold.inner_mgradient, hcov.mvfderiv_sqrt_norm_sq_add hσ hε,
    real_inner_self_eq_norm_sq]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have h := real_inner_mul_inner_self_le (cov σ x (b i)) (σ x)
  simp only [real_inner_self_eq_norm_sq] at h
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos (Real.sqrt_pos.2 (by positivity))),
    Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg ‖cov σ x (b i)‖) hε.le]

end CovariantDerivative.IsMetricCompatible
