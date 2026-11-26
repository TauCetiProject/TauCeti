/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Norm
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.MaximumPrinciple

/-!
# Kato's inequality for the rough Laplacian

For a smooth section `σ` and `ε > 0`, the smooth positive function
`r = sqrt (|σ|² + ε)` satisfies

`Δ r ≥ -⟪∇*∇σ, σ⟫ / r`.

This is the regularized form of Kato's inequality for the nonnegative rough Laplacian
`∇*∇ = -tr ∇²` and the scalar Laplace--Beltrami operator `Δ = div grad`.
The statement includes zeros of the section. In particular the regularized norm of a
rough-harmonic section is subharmonic. No differentiability of `|σ|` at its zeros is asserted.

The proof combines the native norm-square Bochner identity with the scalar Laplacian product
rule and the gradient estimate in `CovariantDerivative.IsMetricCompatible`.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Chapter 9.
* [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
* [frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative.IsMetricCompatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  {σ : Π x : M, V x}

/-- The Laplacian of the positive regularization of the norm of a section, expressed through
the covariant derivative energy and its rough Laplacian. -/
theorem laplaceBeltrami_sqrt_norm_sq_add (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) {ε : ℝ} (hε : 0 < ε) (x : M) :
    TauCeti.Manifold.laplaceBeltrami I (fun y ↦ Real.sqrt (‖σ y‖ ^ 2 + ε)) x =
      (cov.innerCovariantDerivative σ σ x -
        ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, σ x⟫ -
          ‖TauCeti.Manifold.mgradient I (fun y ↦ Real.sqrt (‖σ y‖ ^ 2 + ε)) x‖ ^ 2) /
        Real.sqrt (‖σ x‖ ^ 2 + ε) := by
  let r := fun y ↦ Real.sqrt (‖σ y‖ ^ 2 + ε)
  have hq : ContMDiff I 𝓘(ℝ) 2 (fun y ↦ ‖σ y‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using (hσ.inner_bundle hσ).of_le (by simp)
  have hqε : ContMDiff I 𝓘(ℝ) 2 (fun y ↦ ‖σ y‖ ^ 2 + ε) := by
    simpa only [Pi.add_def] using hq.add (contMDiff_const (c := ε))
  have hr : ContMDiff I 𝓘(ℝ) 2 r := hqε.sqrt (fun y ↦ ne_of_gt (by positivity))
  have hsq : r * r = (fun y ↦ ‖σ y‖ ^ 2) + (fun _ ↦ ε) := by
    funext y
    exact Real.mul_self_sqrt (by positivity)
  have henergy : (∑ i, ‖cov σ x (stdOrthonormalBasis ℝ (TangentSpace I x) i)‖ ^ 2) =
      cov.innerCovariantDerivative σ σ x := by
    simpa only [real_inner_self_eq_norm_sq] using
      (cov.innerCovariantDerivative_eq_sum σ σ x (stdOrthonormalBasis ℝ _)).symm
  have hprod := TauCeti.Manifold.laplaceBeltrami_mul I hr hr x
  rw [hsq, TauCeti.Manifold.laplaceBeltrami_add I hq contMDiff_const,
    TauCeti.Manifold.laplaceBeltrami_const, add_zero,
    hcov.laplaceBeltrami_norm_sq hσ x (stdOrthonormalBasis ℝ _),
    henergy] at hprod
  rw [real_inner_self_eq_norm_sq] at hprod
  apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.2 (by positivity)))).2
  -- Fold the local abbreviation `r` in both factors to match the product identity `hprod`.
  change TauCeti.Manifold.laplaceBeltrami I r x * r x = _
  linarith

/-- **Regularized Kato inequality.** The scalar Laplacian of `sqrt (|σ|² + ε)` is bounded below
by `-⟪∇*∇σ, σ⟫ / sqrt (|σ|² + ε)`, also at zeros of the section. -/
theorem neg_inner_roughLaplacian_div_sqrt_le (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) {ε : ℝ} (hε : 0 < ε) (x : M) :
    -⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, σ x⟫ /
        Real.sqrt (‖σ x‖ ^ 2 + ε) ≤
      TauCeti.Manifold.laplaceBeltrami I (fun y ↦ Real.sqrt (‖σ y‖ ^ 2 + ε)) x := by
  rw [hcov.laplaceBeltrami_sqrt_norm_sq_add hσ hε]
  apply (div_le_div_iff_of_pos_right (Real.sqrt_pos.2 (by positivity))).2
  have hgrad := hcov.norm_sq_mgradient_sqrt_norm_sq_add_le
    (hσ.mdifferentiable (by simp) x) hε
  linarith

/-- The regularized norm of a rough-harmonic section is subharmonic. It suffices that the
rough Laplacian paired with the section is nonpositive at the point in question. -/
theorem laplaceBeltrami_sqrt_norm_sq_add_nonneg (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) {ε : ℝ} (hε : 0 < ε) (x : M)
    (h : ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, σ x⟫ ≤ 0) :
    0 ≤ TauCeti.Manifold.laplaceBeltrami I (fun y ↦ Real.sqrt (‖σ y‖ ^ 2 + ε)) x := by
  exact (div_nonneg (neg_nonneg.2 h) (Real.sqrt_nonneg _)).trans
    (hcov.neg_inner_roughLaplacian_div_sqrt_le hσ hε x)

end CovariantDerivative.IsMetricCompatible
