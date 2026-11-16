/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Bochner.Basic
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem

/-!
# The integrated Bochner identity

For a compactly supported smooth real function on a σ-compact boundaryless Riemannian manifold,

`∫ (|Hess f|² + Ric(grad f, grad f)) dV = ∫ (Δ f)² dV`.

Here `Δ = div grad` is `TauCeti.Manifold.laplaceBeltrami`; squaring makes the right
side identical for the nonnegative Laplacian. The measure is the canonical
`TauCeti.riemannianVolume`. Compact support replaces compactness of the manifold;
no orientation, completeness, connectedness or positive dimension is needed.

The Hessian norm is written in arbitrary pointwise orthonormal bases. The bases
need not vary continuously: the pointwise Bochner formula identifies the combined
Hessian–Ricci integrand with an integrable scalar expression. In particular the
integral is not justified by an unproved regularity assumption on a chosen frame.
This identity is the energy equality underlying the sharp scalar eigenvalue estimate.

The proof uses `laplaceBeltrami_norm_sq_mgradient` and Green's first identity
`integral_mul_laplaceBeltrami`.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016),
  Chapter 9 (the Bochner technique).
-/

public section

open Bundle MeasureTheory
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {ι : Type*} [Fintype ι]

section Integrability

variable [LindelofSpace M]

omit [T2Space M] [I.Boundaryless] in
private theorem integrable_bochner_terms (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hfc : HasCompactSupport f) :
    Integrable (laplaceBeltrami I (fun x ↦ ‖mgradient I f x‖ ^ 2))
        (riemannianVolume I M) ∧
      Integrable (fun x ↦ mvfderiv I (laplaceBeltrami I f) x (mgradient I f x))
        (riemannianVolume I M) := by
  let _ : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hN : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ ‖mgradient I f x‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using contMDiff_inner_mgradient (n := ∞) hf hf
  have hNc : HasCompactSupport (fun x ↦ ‖mgradient I f x‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using hfc.inner_mgradient (I := I) (mgradient I f)
  have hL : ContMDiff I 𝓘(ℝ) ∞ (laplaceBeltrami I f) :=
    contMDiff_laplaceBeltrami (n := ∞) (m := ∞) (k := ∞) (by simp) (by simp) hf
  constructor
  · exact (contMDiff_laplaceBeltrami (n := 0) (m := ∞) (k := ∞)
      (by simp) (by simp) (hN.of_le (by simp))).continuous.integrable_of_hasCompactSupport
        (hNc.laplaceBeltrami I)
  · have hcont := (contMDiff_inner_mgradient (n := ∞) hL hf).continuous
    have hsupp := (hfc.laplaceBeltrami I).inner_mgradient (I := I) (mgradient I f)
    simpa only [inner_mgradient] using hcont.integrable_of_hasCompactSupport hsupp

omit [I.Boundaryless] in
/-- The combined Hessian–Ricci integrand is integrable for a compactly supported smooth
function. The pointwise orthonormal bases may be chosen without any regularity assumption. -/
theorem integrable_sum_hessian_sq_add_ricci (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hfc : HasCompactSupport f) (b : ∀ x : M, OrthonormalBasis ι ℝ (TangentSpace I x)) :
    Integrable (fun x ↦ (∑ i, ∑ j, hessian I f x (b x i) (b x j) ^ 2) +
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x
        (mgradient I f x) (mgradient I f x)) (riemannianVolume I M) := by
  obtain ⟨hN, hL⟩ := integrable_bochner_terms hf hfc
  refine ((hN.const_mul (1 / 2 : ℝ)).sub hL).congr (Filter.Eventually.of_forall fun x ↦ ?_)
  have h := laplaceBeltrami_norm_sq_mgradient hf x (b x)
  dsimp only [Pi.sub_apply]
  linarith

end Integrability

/-- **The integrated Bochner identity.** For a compactly supported smooth function on a
boundaryless manifold, `∫ (|Hess f|² + Ric(grad f, grad f)) = ∫ (Δ f)²`.
Both integrands are integrable, and the identity holds in every pointwise orthonormal basis. -/
theorem integral_sum_hessian_sq_add_ricci [SigmaCompactSpace M] (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hfc : HasCompactSupport f) (b : ∀ x : M, OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∫ x, ((∑ i, ∑ j, hessian I f x (b x i) (b x j) ^ 2) +
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x
        (mgradient I f x) (mgradient I f x)) ∂riemannianVolume I M =
      ∫ x, laplaceBeltrami I f x ^ 2 ∂riemannianVolume I M := by
  let _ : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hN : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ ‖mgradient I f x‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using contMDiff_inner_mgradient (n := ∞) hf hf
  have hNc : HasCompactSupport (fun x ↦ ‖mgradient I f x‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using hfc.inner_mgradient (I := I) (mgradient I f)
  have hL : ContMDiff I 𝓘(ℝ) ∞ (laplaceBeltrami I f) :=
    contMDiff_laplaceBeltrami (n := ∞) (m := ∞) (k := ∞) (by simp) (by simp) hf
  have hzero := integral_laplaceBeltrami_eq_zero (hN.of_le (by simp)) hNc
  have hgreen := integral_mul_laplaceBeltrami (hL.of_le (by simp))
    (hfc.laplaceBeltrami I) (hf.of_le (by simp))
  simp only [← sq, inner_mgradient] at hgreen
  obtain ⟨hNi, hLi⟩ := integrable_bochner_terms hf hfc
  calc
    _ = ∫ x, ((1 / 2 : ℝ) * laplaceBeltrami I (fun y ↦ ‖mgradient I f y‖ ^ 2) x -
        mvfderiv I (laplaceBeltrami I f) x (mgradient I f x)) ∂riemannianVolume I M := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        have h := laplaceBeltrami_norm_sq_mgradient hf x (b x)
        linarith
    _ = _ := by
      rw [integral_sub (hNi.const_mul _) hLi, integral_const_mul, hzero]
      linarith

end TauCeti.Manifold
