/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pulled-back metric coefficients and conformally Euclidean ends on metric-indexed manifolds

For a `C^k` Riemannian metric `g` on a manifold `M`, the pulled-back metric coefficients
(`TauCeti.pullbackMetricCoeff`) of the metric-indexed copy `TauCeti.WithMetric g` along
`WithMetric.toWithMetric g ∘ φ` evaluate `g.inner` on the differentials of `φ` along the standard
Euclidean basis vectors. Consequently, conformal rescaling `g ↦ f • g` scales the pulled-back
coefficient matrix by `f (φ x)`, and on Euclidean space `ℝⁿ` the conformally flat metric
`f • g_eucl` has pulled-back coefficient matrix `f x • 1`.

When `w : ℝⁿ → ℝ` (`0 < n`) is a positive `C^k` (`2 ≤ k`) conformal factor whose deviation `w - 1`
decays at order `t` up to second derivatives outside `closedBall 0 R`, rescaling the flat Euclidean
metric by `w` on `TauCeti.WithMetric` produces an asymptotically Euclidean end of order `t` and a
one-ended finite-ended asymptotically Euclidean manifold.

## Main results

* `TauCeti.pullbackMetricCoeff_toWithMetric_comp`: coordinate pullback coefficients of
  `WithMetric g` along `WithMetric.toWithMetric g ∘ φ`.
* `TauCeti.pullbackMetricCoeff_toWithMetric_rescale_comp`: coordinate pullback coefficients scale
  by `f (φ x)` under conformal rescaling `g.rescale f hf hf_pos`.
* `TauCeti.pullbackMetricCoeff_toWithMetric_rescale`: pulling back `f • g_eucl` along
  `WithMetric.toWithMetric` yields `f x • 1`.
* `TauCeti.isAsymptoticallyEuclideanEnd_toWithMetric_rescale` and
  `TauCeti.isFiniteEndedAsymptoticallyEuclidean_toWithMetric_rescale`: conformally Euclidean ends
  and one-ended structures on `WithMetric` from a positive `C^k` (`2 ≤ k`) conformal factor with
  `w - 1 = O_2(‖x‖ ^ (-t))`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (pullback metrics and conformal changes of metric).
* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, Trans. Amer. Math. Soc. 377 (2024), 5271-5288 (arXiv:2108.11972), Section 2.
-/

public section

noncomputable section

open Bundle Metric Set
open scoped ContDiff Manifold

namespace TauCeti

/-- Pulling back `WithMetric g` along `WithMetric.toWithMetric g ∘ φ` evaluates `g.inner` on the
differentials of `φ` along the Euclidean coordinate basis vectors. -/
theorem pullbackMetricCoeff_toWithMetric_comp {n : ℕ} {k : ℕ∞ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : ContMDiffRiemannianMetric I k E (fun x : M ↦ TangentSpace I x))
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff I (WithMetric.toWithMetric g ∘ φ) x =
      Matrix.of fun i j ↦
        g.inner (φ x)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x (EuclideanSpace.basisFun (Fin n) ℝ i))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  ext i j
  rw [pullbackMetricCoeff_apply, Matrix.of_apply, WithMetric.inner_def,
    ← ContMDiffRiemannianMetric.inner_riemannianBundle,
    ← ContMDiffRiemannianMetric.inner_riemannianBundle]
  exact inner_tangentSpace_congr (I := I) (WithMetric.ofWithMetric_toWithMetric g (φ x))
    (WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric_comp φ x _)
    (WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric_comp φ x _)

/-- Conformal rescaling of pulled-back metric coefficients: pulling back `g.rescale f hf hf_pos`
along `WithMetric.toWithMetric _ ∘ φ` scales the pulled-back metric coefficient matrix of `g` by
`f (φ x)`. -/
theorem pullbackMetricCoeff_toWithMetric_rescale_comp {n : ℕ} {k : ℕ∞ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : ContMDiffRiemannianMetric I k E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff I (WithMetric.toWithMetric (g.rescale f hf hf_pos) ∘ φ) x =
      f (φ x) • pullbackMetricCoeff I (WithMetric.toWithMetric g ∘ φ) x := by
  ext i j
  rw [pullbackMetricCoeff_toWithMetric_comp, Matrix.smul_apply,
    pullbackMetricCoeff_toWithMetric_comp, Matrix.of_apply, Matrix.of_apply,
    ContMDiffRiemannianMetric.rescale_inner, smul_eq_mul]

/-- Pulling back the conformally rescaled Euclidean metric `f • g_eucl` along
`WithMetric.toWithMetric` yields the scalar multiple `f x • 1` of the identity matrix. -/
@[simp]
theorem pullbackMetricCoeff_toWithMetric_rescale {n : ℕ} {k : ℕ∞ω}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)
    (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (WithMetric.toWithMetric
        (((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE le_top).rescale
          f hf hf_pos))
      x = f x • 1 := by
  rw [← Function.comp_id (WithMetric.toWithMetric _),
    pullbackMetricCoeff_toWithMetric_rescale_comp, id_eq]
  congr 1
  ext i j
  rw [pullbackMetricCoeff_toWithMetric_comp, Matrix.of_apply, id_eq,
    ContMDiffRiemannianMetric.ofLE_inner, ← ContMDiffRiemannianMetric.inner_riemannianBundle,
    ← pullbackMetricCoeff_apply, pullbackMetricCoeff_id]

/-- Any `C^k` (`2 ≤ k`) positive conformal factor `w : ℝⁿ → ℝ` (`0 < n`) satisfying
`‖D^m(w - 1)(x)‖ ≤ C ‖x‖ ^ (-t - m)` (`m ≤ 2`) outside `closedBall 0 R` (`R > 0`) defines an
asymptotically Euclidean end of order `t` on `WithMetric (w • g_eucl)`. -/
theorem isAsymptoticallyEuclideanEnd_toWithMetric_rescale {n : ℕ} (hn : 0 < n) {k : ℕ∞ω}
    (hk : 2 ≤ k) {t R : ℝ} (hR : 0 < R) {w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hw : ContDiff ℝ k w) (hw_pos : ∀ x, 0 < w x)
    (hdecay : ∃ C : ℝ, ∀ m ≤ 2, ∀ x ∈ (closedBall 0 R)ᶜ,
      ‖iteratedFDeriv ℝ m (fun y ↦ w y - 1) x‖ ≤ C * ‖x‖ ^ (-t - m)) :
    IsAsymptoticallyEuclideanEnd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) t R
      (WithMetric.toWithMetric
        (((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := k)
          le_top).rescale w hw.contMDiff hw_pos)) := by
  let g := ((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := k)
    le_top).rescale w hw.contMDiff hw_pos
  have hg_coeff (y : EuclideanSpace ℝ (Fin n)) :
      pullbackMetricCoeff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (WithMetric.toWithMetric g) y =
        w y • 1 :=
    pullbackMetricCoeff_toWithMetric_rescale hw.contMDiff hw_pos y
  have hg_ij (i j : Fin n) :
      (pullbackMetricCoeff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (WithMetric.toWithMetric g) · i j) =
        if i = j then w else 0 := by
    ext y
    rw [hg_coeff]
    split_ifs <;> simp [*]
  obtain ⟨C, hC⟩ := hdecay
  refine
    { radius_pos := hR
      dim_pos := hn
      contMDiffOn := WithMetric.contMDiff_toWithMetric.contMDiffOn
      injOn := (WithMetric.toWithMetric_injective g).injOn
      isInvertible_mfderiv := fun x _ ↦ by
        rw [WithMetric.mfderiv_toWithMetric]
        exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
      contDiffOn_pullbackMetricCoeff := fun i j ↦ by
        rw [hg_ij]
        split_ifs
        · exact (hw.of_le hk).contDiffOn
        · exact contDiffOn_const
      exists_norm_iteratedFDeriv_le := ⟨max C 0, fun m hm i j x hx ↦ ?_⟩ }
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  by_cases hij : i = j
  · subst hij
    have hcoeff : (fun y ↦ (pullbackMetricCoeff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (WithMetric.toWithMetric g) y - 1) i i) = fun y ↦ w y - 1 := by
      ext y; rw [Matrix.sub_apply, hg_coeff]; simp
    rw [hcoeff]
    exact (hC m hm x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hx0 _))
  · have hcoeff : (fun y ↦ (pullbackMetricCoeff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (WithMetric.toWithMetric g) y - 1) i j) = 0 := by
      ext y; rw [Matrix.sub_apply, hg_coeff]; simp [hij]
    rw [hcoeff, iteratedFDeriv_zero]
    simp only [Pi.zero_apply, norm_zero]
    exact mul_nonneg (le_max_right C 0) (Real.rpow_nonneg hx0 _)

/-- Any `C^k` (`2 ≤ k`) positive conformal factor `w : ℝⁿ → ℝ` (`0 < n`) satisfying
`‖D^m(w - 1)(x)‖ ≤ C ‖x‖ ^ (-t - m)` (`m ≤ 2`) outside `closedBall 0 R` (`R > 0`) makes
`WithMetric (w • g_eucl)` a one-ended finite-ended asymptotically Euclidean manifold of order
`t`. -/
theorem isFiniteEndedAsymptoticallyEuclidean_toWithMetric_rescale {n : ℕ} (hn : 0 < n) {k : ℕ∞ω}
    (hk : 2 ≤ k) {t R : ℝ} (hR : 0 < R) {w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hw : ContDiff ℝ k w) (hw_pos : ∀ x, 0 < w x)
    (hdecay : ∃ C : ℝ, ∀ m ≤ 2, ∀ x ∈ (closedBall 0 R)ᶜ,
      ‖iteratedFDeriv ℝ m (fun y ↦ w y - 1) x‖ ≤ C * ‖x‖ ^ (-t - m)) :
    IsFiniteEndedAsymptoticallyEuclidean 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) t
      (fun _ : Unit ↦ R)
      (fun _ ↦ WithMetric.toWithMetric
        (((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := k)
          le_top).rescale w hw.contMDiff hw_pos)) where
  finite := inferInstance
  nonempty := inferInstance
  isAsymptoticallyEuclideanEnd _ :=
    isAsymptoticallyEuclideanEnd_toWithMetric_rescale hn hk hR hw hw_pos hdecay
  pairwise_disjoint e e' hee' := (hee' (Subsingleton.elim e e')).elim
  isCompact_compl_iUnion := by
    let g := ((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := k)
      le_top).rescale w hw.contMDiff hw_pos
    rw [iUnion_const, ← WithMetric.coe_homeomorph_symm g,
      ← image_compl_eq (WithMetric.homeomorph g).symm.bijective, compl_compl]
    exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).image
      (WithMetric.homeomorph g).symm.continuous

end TauCeti
