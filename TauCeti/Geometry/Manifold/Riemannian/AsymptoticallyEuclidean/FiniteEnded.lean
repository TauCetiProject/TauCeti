/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Distance
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Rescale
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Volume
import TauCeti.Analysis.Normed.Module.Ball.Exterior

/-!
# Finite-ended asymptotically Euclidean manifolds

This module extends `TauCeti.IsFiniteEndedAsymptoticallyEuclidean` (from
`TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic`) with topological, compact
truncation, scaling, and infinite-volume results.

Note that `IsFiniteEndedAsymptoticallyEuclidean.isCompact_compl_iUnion` controls only the complement
of the initial cover at radii `R`; cutting the ends at larger radii `R' ≥ R` need not leave a
compact complement on an incomplete manifold, so compact truncation is proved separately under a
compact-collar or Riemannian completeness hypothesis.

## Main results

* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.nonempty_manifold`: a manifold carrying a
  finite-ended asymptotically Euclidean structure is nonempty.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.finiteDimensional` and
  `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.lindelofSpace`: its model space is
  finite-dimensional and the manifold is Lindelöf.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.isOpen_iUnion_image`: the union of the end
  images is open on any `C¹` manifold.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.isCompact_compl_iUnion_of_compact_collar`,
  `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.mono_radius_of_compact_collar`,
  `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.mono_radius_of_completeSpace`: cutting the ends at
  larger radii preserves compactness of the complement under a compact-collar or completeness
  hypothesis.
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
open scoped ContDiff ENNReal Manifold Pointwise Topology

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

/-- The model space `E` of a finite-ended asymptotically Euclidean manifold is finite-dimensional,
derived from one of its ends. -/
theorem finiteDimensional (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) :
    FiniteDimensional ℝ E :=
  let ⟨e⟩ := h.nonempty
  (h.isAsymptoticallyEuclideanEnd e).finiteDimensional

/-- Every finite-ended asymptotically Euclidean manifold is Lindelöf, as a finite union of
continuous images of subspaces of `ℝⁿ` together with a compact remainder. -/
theorem lindelofSpace (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) : LindelofSpace M := by
  have := h.finite
  have hend (a : ι) :
      IsLindelof (φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ) := by
    rw [← Subtype.coe_image_univ (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ, ← image_comp]
    exact isLindelof_univ.image
      ((h.isAsymptoticallyEuclideanEnd a).contMDiffOn.continuousOn.comp_continuous
        continuous_subtypeVal fun x ↦ x.property)
  rw [← isLindelof_univ_iff,
    ← union_compl_self (⋃ a, φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ)]
  exact (isLindelof_iUnion hend).union h.isCompact_compl_iUnion.isLindelof

/-- The union of the images of the ends of a finite-ended asymptotically Euclidean structure is
open in any `C¹` manifold `M`. -/
theorem isOpen_iUnion_image [IsManifold I 1 M]
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) :
    IsOpen (⋃ a, φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ) :=
  isOpen_iUnion fun a ↦ (h.isAsymptoticallyEuclideanEnd a).isOpen_image

/-- Cutting the ends of a finite-ended asymptotically Euclidean structure on a `C¹` manifold at
larger radii `R' ≥ R` leaves a compact complement whenever each annular collar
`φ a '' ((closedBall 0 (R a))ᶜ ∩ closedBall 0 (R' a))` is contained in a compact set. -/
theorem isCompact_compl_iUnion_of_compact_collar [IsManifold I 1 M]
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ)
    {R' : ι → ℝ} (hR : ∀ a, R a ≤ R' a)
    (hcollar : ∀ a, ∃ K : Set M, IsCompact K ∧
      φ a '' ((closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ ∩ closedBall 0 (R' a)) ⊆ K) :
    IsCompact (⋃ a, φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R' a))ᶜ)ᶜ := by
  classical
  choose K hK_comp hK_sub using hcollar
  have hclosed :
      IsClosed (⋃ a, φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R' a))ᶜ)ᶜ :=
    (isOpen_iUnion fun a ↦
      ((h.isAsymptoticallyEuclideanEnd a).mono_radius (hR a)).isOpen_image).isClosed_compl
  have hsub :
      (⋃ a, φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R' a))ᶜ)ᶜ ⊆
        (⋃ a, φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ)ᶜ ∪ ⋃ a, K a := by
    intro p hp
    by_cases hp0 : p ∈ ⋃ a, φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ
    · refine Or.inr ?_
      rw [mem_iUnion] at hp0 ⊢
      obtain ⟨a, x, hx, rfl⟩ := hp0
      have hx' : x ∉ (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R' a))ᶜ := fun hx' ↦
        hp (mem_iUnion.2 ⟨a, x, hx', rfl⟩)
      exact ⟨a, hK_sub a ⟨x, ⟨hx, not_not.1 hx'⟩, rfl⟩⟩
    · exact Or.inl hp0
  have := h.finite
  exact (h.isCompact_compl_iUnion.union (isCompact_iUnion hK_comp)).of_isClosed_subset hclosed hsub

/-- Cutting the ends of a finite-ended asymptotically Euclidean structure on a `C¹` manifold at
larger radii `R' ≥ R` preserves the finite-ended structure whenever each annular collar
`φ a '' ((closedBall 0 (R a))ᶜ ∩ closedBall 0 (R' a))` is contained in a compact set. -/
theorem mono_radius_of_compact_collar [IsManifold I 1 M]
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ)
    {R' : ι → ℝ} (hR : ∀ a, R a ≤ R' a)
    (hcollar : ∀ a, ∃ K : Set M, IsCompact K ∧
      φ a '' ((closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ ∩ closedBall 0 (R' a)) ⊆ K) :
    IsFiniteEndedAsymptoticallyEuclidean I t R' φ where
  finite := h.finite
  nonempty := h.nonempty
  isAsymptoticallyEuclideanEnd a := (h.isAsymptoticallyEuclideanEnd a).mono_radius (hR a)
  pairwise_disjoint a b hab := by
    have hsub (c : ι) :
        φ c '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R' c))ᶜ ⊆
          φ c '' (closedBall 0 (R c))ᶜ :=
      image_mono (compl_subset_compl.2 (closedBall_subset_closedBall (hR c)))
    exact (h.pairwise_disjoint hab).mono (hsub a) (hsub b)
  isCompact_compl_iUnion := h.isCompact_compl_iUnion_of_compact_collar hR hcollar

/-- Cutting the ends of a finite-ended asymptotically Euclidean structure on a complete `C¹`
Riemannian manifold (with extended Riemannian distance) at larger radii `R' ≥ R` preserves the
finite-ended structure. -/
theorem mono_radius_of_completeSpace {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsManifold I 1 M] {φ : ι → EuclideanSpace ℝ (Fin n) → M}
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) {R' : ι → ℝ} (hR : ∀ a, R a ≤ R' a) :
    IsFiniteEndedAsymptoticallyEuclidean I t R' φ :=
  h.mono_radius_of_compact_collar hR fun a ↦
    ⟨closure (φ a '' ((closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ ∩ closedBall 0 (R' a))),
      isCompact_iff_totallyBounded_isComplete.2
        ⟨((h.isAsymptoticallyEuclideanEnd a).totallyBounded_image_compl_inter_closedBall
          (R' a)).closure, isClosed_closure.isComplete⟩,
      subset_closure⟩

/-- Constant metric rescaling `g ↦ c • g` preserves finite-ended asymptotically Euclidean
structures, rescaling each excised radius by `√c` and each parametrization by
`y ↦ toWithMetric _ (φ a ((√c)⁻¹ • y))`. -/
theorem rescale (m : ℕ∞ω) [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)] {c : ℝ} (hc : 0 < c)
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) :
    let _ := h.finiteDimensional
    IsFiniteEndedAsymptoticallyEuclidean I t (fun a ↦ Real.sqrt c * R a)
      (fun a y ↦ WithMetric.toWithMetric (rescaledMetric I M m hc)
        (φ a ((Real.sqrt c)⁻¹ • y))) := by
  have : FiniteDimensional ℝ E := h.finiteDimensional
  set g_c := rescaledMetric I M m hc
  set s := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  have himage (a : ι) :
      (fun y ↦ WithMetric.toWithMetric g_c (φ a (s⁻¹ • y))) ''
          (closedBall (0 : EuclideanSpace ℝ (Fin n)) (s * R a))ᶜ =
        WithMetric.toWithMetric g_c '' (φ a '' (closedBall 0 (R a))ᶜ) := by
    have hcomp :
        (fun y ↦ WithMetric.toWithMetric g_c (φ a (s⁻¹ • y))) =
          WithMetric.toWithMetric g_c ∘ φ a ∘ (s⁻¹ • ·) :=
      funext fun y ↦ by simp only [Function.comp_apply]
    rw [hcomp, image_comp, image_comp, Set.image_smul, smul_compl_closedBall (inv_ne_zero hs.ne'),
      smul_zero, Real.norm_of_nonneg (inv_nonneg.2 hs.le), inv_mul_cancel_left₀ hs.ne']
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
theorem riemannianVolume_univ_eq_top [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) (ht : 0 < t) :
    let _ := h.finiteDimensional
    let _ := h.lindelofSpace
    riemannianVolume I M univ = ⊤ := by
  have : FiniteDimensional ℝ E := h.finiteDimensional
  have : LindelofSpace M := h.lindelofSpace
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
