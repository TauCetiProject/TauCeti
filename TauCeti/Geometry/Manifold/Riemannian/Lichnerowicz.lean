/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Bochner.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The Lichnerowicz eigenvalue estimate

On a closed Riemannian manifold of dimension `n ≥ 2` with `Ric ≥ (n - 1) k g`,
every nonzero smooth eigenfunction of the nonnegative scalar Laplacian with positive
eigenvalue `λ` satisfies `λ ≥ n k`. The sign convention here is
`laplaceBeltrami f = -λ f`.
The estimate applies to every positive eigenvalue, including the first one.

The proof integrates the Bochner inequality and uses Green's identity. The pointwise
Bochner inequality is also available without compactness.
Connectedness and a mean-zero hypothesis are unnecessary for this estimate.
No existence of eigenfunctions or rigidity of the equality case is asserted here.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Chapter 9 (the Bochner technique
  and the Lichnerowicz estimate).
-/

public section

open Bundle MeasureTheory
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {k lam : ℝ}

variable [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The dimension-weighted Bochner inequality under a Ricci lower bound. It is local,
requires no dimension restriction, and uses `Δ = div grad` rather than `Δ⁺`. -/
theorem le_finrank_mul_laplaceBeltrami_norm_sq_mgradient
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hRic : ∀ v : TangentSpace I x,
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v) :
    2 * laplaceBeltrami I f x ^ 2 +
      2 * (Module.finrank ℝ E : ℝ) *
        mvfderiv I (laplaceBeltrami I f) x (mgradient I f x) +
      2 * (Module.finrank ℝ E : ℝ) * (((Module.finrank ℝ E : ℝ) - 1) * k) *
        ‖mgradient I f x‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        laplaceBeltrami I (fun y ↦ ‖mgradient I f y‖ ^ 2) x := by
  have htrace := laplaceBeltrami_sq_le_finrank_mul_sum_hessian_sq f x
    (stdOrthonormalBasis ℝ (TangentSpace I x))
  rw [laplaceBeltrami_norm_sq_mgradient hf x
    (stdOrthonormalBasis ℝ (TangentSpace I x))]
  have hcurv := mul_le_mul_of_nonneg_left (hRic (mgradient I f x))
    (show 0 ≤ 2 * (Module.finrank ℝ E : ℝ) by positivity)
  nlinarith

section Closed

variable [I.Boundaryless] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **The Lichnerowicz estimate.** On a closed manifold of dimension `n ≥ 2` with
`Ric ≥ (n - 1) k g`, every positive eigenvalue with a nonzero smooth eigenfunction
is at least `n k`. The eigen-equation is stated for the native `Δ = div grad`.
The real lower bound `k` need not be positive. -/
theorem finrank_mul_le_of_laplaceBeltrami_eq_neg_mul
    (hn : 2 ≤ Module.finrank ℝ E) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hlam : 0 < lam) (heig : ∀ x, laplaceBeltrami I f x = -lam * f x)
    (hne : ∃ x, f x ≠ 0)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v) :
    (Module.finrank ℝ E : ℝ) * k ≤ lam := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let _ := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  let n : ℝ := Module.finrank ℝ E
  let μ := riemannianVolume I M
  have hN : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ ‖mgradient I f x‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using contMDiff_inner_mgradient (n := ∞) hf hf
  have hFint : Integrable (fun x ↦ f x ^ 2) μ :=
    (hf.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNint : Integrable (fun x ↦ ‖mgradient I f x‖ ^ 2) μ :=
    hN.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hL := contMDiff_laplaceBeltrami (I := I) (n := 0) (m := ∞) (k := ∞)
    (by simp) (by simp) (hN.of_le (by simp))
  have hLint : Integrable (laplaceBeltrami I (fun x ↦ ‖mgradient I f x‖ ^ 2)) μ :=
    hL.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have henergy := integral_norm_sq_mgradient_eq_mul_integral_sq_of_laplaceBeltrami_eq_neg_mul
    (hf.of_le (by simp)) (HasCompactSupport.of_compactSpace f) heig
  have hzero := integral_laplaceBeltrami_eq_zero (hN.of_le (by simp))
    (HasCompactSupport.of_compactSpace _)
  have hderiv (x : M) : mvfderiv I (laplaceBeltrami I f) x (mgradient I f x) =
      -lam * ‖mgradient I f x‖ ^ 2 := by
    have heq : laplaceBeltrami I f = -lam • f := funext heig
    rw [heq, mvfderiv_const_smul_field, smul_apply, smul_eq_mul,
      ← inner_mgradient, real_inner_self_eq_norm_sq]
  have hpoint (x : M) : 2 * lam ^ 2 * f x ^ 2 +
      (2 * n * ((n - 1) * k - lam)) * ‖mgradient I f x‖ ^ 2 ≤
      n * laplaceBeltrami I (fun y ↦ ‖mgradient I f y‖ ^ 2) x := by
    have h := le_finrank_mul_laplaceBeltrami_norm_sq_mgradient hf x (hRic x)
    rw [heig, hderiv] at h
    dsimp [n]
    nlinarith
  have hint := integral_mono
    ((hFint.const_mul (2 * lam ^ 2)).add (hNint.const_mul (2 * n * ((n - 1) * k - lam))))
    (hLint.const_mul n) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add (hFint.const_mul _) (hNint.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, hzero, mul_zero, henergy] at hint
  obtain ⟨x, hx⟩ := hne
  have hpos : 0 < ∫ x, f x ^ 2 ∂μ :=
    (hf.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_ne_zero
      (HasCompactSupport.of_compactSpace _) (fun _ ↦ sq_nonneg _) (pow_ne_zero 2 hx)
  have hn' : 1 < n := by dsimp [n]; exact_mod_cast (show 1 < Module.finrank ℝ E by omega)
  -- The integrated inequality factors as 2 * lam * (n - 1) * (∫ f²) * (n * k - lam) ≤ 0.
  have hfactor : 0 < 2 * lam * (n - 1) * ∫ x, f x ^ 2 ∂μ := by positivity
  by_contra hlt
  have hneg : 0 < n * k - lam := sub_pos.2 (lt_of_not_ge hlt)
  nlinarith [mul_pos hfactor hneg]

end Closed

end TauCeti.Manifold
