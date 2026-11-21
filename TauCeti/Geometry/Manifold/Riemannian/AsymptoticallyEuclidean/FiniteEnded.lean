/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Asymptotics
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Rescale

/-!
# Finite-ended asymptotically Euclidean manifolds

This module extends `TauCeti.IsFiniteEndedAsymptoticallyEuclidean` (from
`TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic`) with topological, scaling,
and infinite-volume results.

## Main results

* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.nonempty_manifold`: a manifold carrying a
  finite-ended asymptotically Euclidean structure is nonempty.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.isOpen_iUnion_image`: the union of the end
  images is open.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.rescale`: constant metric rescaling `g ↦ c • g`
  preserves finite-ended asymptotically Euclidean structures.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.riemannianVolume_univ_eq_top`: every finite-ended
  asymptotically Euclidean manifold of positive order has infinite Riemannian volume.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.not_compactSpace`: no compact `C¹` manifold with
  a continuous Riemannian metric admits a finite-ended asymptotically Euclidean structure of
  positive order.

## References

* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  661–693.
* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, Trans. Amer. Math. Soc. 377 (2024), 5271–5288, Definition 2.3 (arXiv:2108.11972v2).
-/

public section

noncomputable section

open Bundle MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace TauCeti

namespace IsFiniteEndedAsymptoticallyEuclidean

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} {t : ℝ} {R : ι → ℝ} {φ : ι → EuclideanSpace ℝ (Fin n) → M}

/-- Any manifold carrying a finite-ended asymptotically Euclidean structure is nonempty. -/
theorem nonempty_manifold (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) : Nonempty M := by
  obtain ⟨e⟩ := h.nonempty
  obtain ⟨y, _, -⟩ := (h.isAsymptoticallyEuclideanEnd e).nonempty_image
  exact ⟨y⟩

/-- The union of the images of the ends of a finite-ended asymptotically Euclidean structure is
open in `M`. -/
theorem isOpen_iUnion_image [IsManifold I ∞ M]
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) :
    IsOpen (⋃ a, φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ) :=
  isOpen_iUnion fun a ↦ (h.isAsymptoticallyEuclideanEnd a).isOpen_image

/-- Constant metric rescaling `g ↦ c • g` preserves finite-ended asymptotically Euclidean
structures, rescaling each excised radius by `√c` and each parametrization by
`y ↦ toWithMetric _ (φ a ((√c)⁻¹ • y))`. -/
theorem rescale (m : ℕ∞ω) [FiniteDimensional ℝ E] [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)] {c : ℝ} (hc : 0 < c)
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) :
    IsFiniteEndedAsymptoticallyEuclidean I t (fun a ↦ Real.sqrt c * R a)
      (fun a y ↦ WithMetric.toWithMetric (rescaledMetric I M m hc)
        (φ a ((Real.sqrt c)⁻¹ • y))) := by
  set g_c := rescaledMetric I M m hc
  set s := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  have himage (a : ι) :
      (fun y ↦ WithMetric.toWithMetric g_c (φ a (s⁻¹ • y))) ''
          (closedBall (0 : EuclideanSpace ℝ (Fin n)) (s * R a))ᶜ =
        WithMetric.toWithMetric g_c '' (φ a '' (closedBall 0 (R a))ᶜ) := by
    have hsmul : (s⁻¹ • ·) '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (s * R a))ᶜ =
        (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ := by
      ext z
      simp only [mem_image, mem_compl_iff, mem_closedBall_zero_iff, not_le]
      refine ⟨?_, fun hz ↦ ⟨s • z, ?_, by simp [smul_smul, hs.ne']⟩⟩
      · rintro ⟨w, hw, rfl⟩
        rwa [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), lt_inv_mul_iff₀ hs]
      · rwa [norm_smul, Real.norm_of_nonneg hs.le, mul_lt_mul_iff_right₀ hs]
    rw [show ((fun y ↦ WithMetric.toWithMetric g_c (φ a (s⁻¹ • y))) :
        EuclideanSpace ℝ (Fin n) → WithMetric g_c) =
        WithMetric.toWithMetric g_c ∘ φ a ∘ (s⁻¹ • ·) from rfl,
      image_comp, image_comp, hsmul]
  refine
    { finite := h.finite
      nonempty := h.nonempty
      isAsymptoticallyEuclideanEnd a := (h.isAsymptoticallyEuclideanEnd a).rescale m hc
      pairwise_disjoint a b hab := by
        dsimp only
        rw [himage a, himage b]
        exact (h.pairwise_disjoint hab).image (WithMetric.toWithMetric_injective g_c).injOn
          (subset_univ _) (subset_univ _)
      isCompact_compl_iUnion := by
        have hU :
            (⋃ a, (fun y ↦ WithMetric.toWithMetric g_c (φ a (s⁻¹ • y))) ''
                (closedBall (0 : EuclideanSpace ℝ (Fin n)) (s * R a))ᶜ) =
              WithMetric.toWithMetric g_c ''
                (⋃ a, φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ) := by
          simp_rw [himage, ← image_iUnion]
        rw [hU, ← WithMetric.coe_homeomorph_symm g_c,
          ← (WithMetric.homeomorph g_c).symm.image_compl]
        exact h.isCompact_compl_iUnion.image (WithMetric.homeomorph g_c).symm.continuous }

/-- Every finite-ended asymptotically Euclidean manifold of positive order `t > 0` has infinite
Riemannian volume. -/
theorem riemannianVolume_univ_eq_top [FiniteDimensional ℝ E] [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) (ht : 0 < t) :
    riemannianVolume I M univ = ⊤ := by
  obtain ⟨a⟩ := h.nonempty
  exact top_unique
    (((h.isAsymptoticallyEuclideanEnd a).riemannianVolume_image_eq_top ht).symm.trans_le
      (measure_mono (subset_univ _)))

/-- No compact `C¹` manifold with a continuous Riemannian metric admits a finite-ended
asymptotically Euclidean structure of positive order `t > 0`. -/
theorem not_compactSpace [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) (ht : 0 < t) : ¬ CompactSpace M := by
  obtain ⟨a⟩ := h.nonempty
  exact (h.isAsymptoticallyEuclideanEnd a).not_compactSpace ht

end IsFiniteEndedAsymptoticallyEuclidean

end TauCeti

end
