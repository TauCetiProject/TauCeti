/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Asymptotics
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Rescale
import TauCeti.Geometry.Manifold.Riemannian.Distance
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing

/-!
# Finite-ended asymptotically Euclidean manifolds

This module extends `TauCeti.IsFiniteEndedAsymptoticallyEuclidean` (from
`TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic`) with topological, compact
truncation, scaling, and infinite-volume results.

Note that `IsFiniteEndedAsymptoticallyEuclidean.isCompact_compl_iUnion` controls only the complement
of the initial cover at radii `R`; cutting the ends at larger radii `R' ≥ R` need not leave a
compact complement on an incomplete manifold, so compact truncation is proved separately under a
compact-collar, properness, or Riemannian completeness hypothesis.

## Main results

* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.nonempty_manifold`: a manifold carrying a
  finite-ended asymptotically Euclidean structure is nonempty.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.isOpen_iUnion_image`: the union of the end
  images is open on any `C¹` manifold.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.isCompact_compl_iUnion_of_compact_collar`,
  `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.mono_radius_of_compact_collar`,
  `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.mono_radius_of_properSpace`,
  `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.mono_radius_of_completeSpace`: cutting the ends at
  larger radii preserves compactness of the complement under a compact-collar, properness, or
  completeness hypothesis.
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

/-- Pointwise operator bound on `mfderiv` of an asymptotically Euclidean end on an annulus
`R < ‖z‖ ≤ R₁`. -/
private theorem norm_mfderiv_le_of_compl_closedBall {R R₁ : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}
    (h : IsAsymptoticallyEuclideanEnd I t R φ) {C : ℝ}
    (hC : ∀ k ≤ 2, ∀ (i j : Fin n), ∀ x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ,
      ‖iteratedFDeriv ℝ k (fun y ↦ (pullbackMetricCoeff I φ y - 1) i j) x‖ ≤ C * ‖x‖ ^ (-t - k))
    {z : EuclideanSpace ℝ (Fin n)} (hz_gt : R < ‖z‖) (hz_le : ‖z‖ ≤ R₁)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z ((NormedSpace.fromTangentSpace z).symm v)‖ ≤
      ‖v‖ * (n : ℝ) * Real.sqrt (1 + max C 0 * max (R ^ (-t)) (R₁ ^ (-t))) := by
  let M₀ : ℝ := Real.sqrt (1 + max C 0 * max (R ^ (-t)) (R₁ ^ (-t)))
  have hbasis_norm (i : Fin n) :
      ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z
        ((NormedSpace.fromTangentSpace z).symm (EuclideanSpace.basisFun (Fin n) ℝ i))‖ ≤ M₀ := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [NormedSpace.fromTangentSpace_symm_apply, ← real_inner_self_eq_norm_sq,
      ← pullbackMetricCoeff_apply]
    have hz0 := hC 0 (Nat.zero_le 2) i i z (by simpa using hz_gt)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Matrix.sub_apply, Matrix.one_apply_eq,
      Nat.cast_zero, sub_zero] at hz0
    have hrpow : ‖z‖ ^ (-t) ≤ max (R ^ (-t)) (R₁ ^ (-t)) := by
      rcases le_total 0 (-t) with ht0 | ht0
      · exact (Real.rpow_le_rpow (norm_nonneg z) hz_le ht0).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_nonpos h.radius_pos hz_gt.le ht0).trans (le_max_left _ _)
    have hle1 : pullbackMetricCoeff I φ z i i - 1 ≤ max C 0 * max (R ^ (-t)) (R₁ ^ (-t)) :=
      (le_abs_self _).trans <| hz0.trans <|
        mul_le_mul (le_max_left C 0) hrpow (Real.rpow_nonneg (norm_nonneg z) _) (le_max_right C 0)
    linarith
  have hsum : v = ∑ i : Fin n,
      ((EuclideanSpace.basisFun (Fin n) ℝ).repr v i) • EuclideanSpace.basisFun (Fin n) ℝ i :=
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
  have hmf :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z ((NormedSpace.fromTangentSpace z).symm v) =
        ∑ i : Fin n, ((EuclideanSpace.basisFun (Fin n) ℝ).repr v i) •
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z
            ((NormedSpace.fromTangentSpace z).symm (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
    conv_lhs => rw [hsum]
    simp only [map_sum, map_smul]
  rw [hmf]
  calc ‖∑ i : Fin n, ((EuclideanSpace.basisFun (Fin n) ℝ).repr v i) •
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z
            ((NormedSpace.fromTangentSpace z).symm (EuclideanSpace.basisFun (Fin n) ℝ i))‖
      ≤ ∑ i : Fin n, ‖((EuclideanSpace.basisFun (Fin n) ℝ).repr v i) •
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z
            ((NormedSpace.fromTangentSpace z).symm (EuclideanSpace.basisFun (Fin n) ℝ i))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ * M₀ := Finset.sum_le_sum fun i _ ↦ by
        rw [norm_smul, Real.norm_eq_abs]
        have hcoord : |(EuclideanSpace.basisFun (Fin n) ℝ).repr v i| ≤ ‖v‖ := by
          simpa using PiLp.norm_apply_le v i
        exact mul_le_mul hcoord (hbasis_norm i) (norm_nonneg _) (norm_nonneg v)
    _ = ‖v‖ * (n : ℝ) * M₀ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- Along the radial segment from `x` (`R < ‖x‖ < R₁`) to `(R₁ / ‖x‖) • x`, every point `z`
satisfies `R < ‖z‖ ≤ R₁`. -/
private theorem radial_segment_norm_bounds {R R₁ : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hxR : R < ‖x‖) (hx_pos : 0 < ‖x‖) (hx_lt_R₁ : ‖x‖ < R₁)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ segment ℝ x ((R₁ / ‖x‖) • x)) :
    R < ‖z‖ ∧ ‖z‖ ≤ R₁ := by
  rw [segment_eq_image] at hz
  obtain ⟨τ, ⟨hτ0, hτ1⟩, rfl⟩ := hz
  have h1 : 1 ≤ R₁ / ‖x‖ := (one_le_div hx_pos).2 hx_lt_R₁.le
  have hscale : 1 ≤ (1 - τ) + τ * (R₁ / ‖x‖) := by nlinarith
  have hscale_ub : (1 - τ) + τ * (R₁ / ‖x‖) ≤ R₁ / ‖x‖ := by nlinarith
  have hnorm :
      ‖(1 - τ) • x + τ • ((R₁ / ‖x‖) • x)‖ = ((1 - τ) + τ * (R₁ / ‖x‖)) * ‖x‖ := by
    rw [show (1 - τ) • x + τ • ((R₁ / ‖x‖) • x) = ((1 - τ) + τ * (R₁ / ‖x‖)) • x by
      simp [add_smul, smul_smul], norm_smul, Real.norm_of_nonneg (by linarith)]
  rw [hnorm]
  exact ⟨hxR.trans_le (le_mul_of_one_le_left hx_pos.le hscale),
    (mul_le_mul_of_nonneg_right hscale_ub hx_pos.le).trans_eq (div_mul_cancel₀ _ hx_pos.ne')⟩

/-- Radial distance estimate from `φ x` (`R < ‖x‖ ≤ R'`) to the outer sphere `sphere 0 R₁`
(`R₁ = max R R' + 1`). -/
private theorem dist_image_radial_le {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    {R R' R₁ C : ℝ} (hR₁ : R₁ = max R R' + 1)
    {φ : EuclideanSpace ℝ (Fin n) → M} (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (hC : ∀ k ≤ 2, ∀ (i j : Fin n), ∀ z ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ,
      ‖iteratedFDeriv ℝ k (fun y ↦ (pullbackMetricCoeff I φ y - 1) i j) z‖ ≤ C * ‖z‖ ^ (-t - k))
    {x : EuclideanSpace ℝ (Fin n)} (hxR : R < ‖x‖) (hxR' : ‖x‖ ≤ R') :
    dist (φ x) (φ ((R₁ / ‖x‖) • x)) ≤
      R₁ * (n : ℝ) * Real.sqrt (1 + max C 0 * max (R ^ (-t)) (R₁ ^ (-t))) := by
  subst hR₁
  have hx_pos : 0 < ‖x‖ := h.radius_pos.trans hxR
  have hx_lt_R₁ : ‖x‖ < max R R' + 1 :=
    hxR'.trans_lt (lt_of_le_of_lt (le_max_right R R') (lt_add_one _))
  let y : EuclideanSpace ℝ (Fin n) := ((max R R' + 1) / ‖x‖) • x
  have hseg : ∀ z ∈ segment ℝ x y, R < ‖z‖ ∧ ‖z‖ ≤ max R R' + 1 := fun z hz ↦
    radial_segment_norm_bounds hxR hx_pos hx_lt_R₁ hz
  have hdiff : ∀ z ∈ segment ℝ x y, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I 1 φ z :=
    fun z hz ↦ (h.contMDiffOn.contMDiffAt
      (isClosed_closedBall.isOpen_compl.mem_nhds (by simpa using (hseg z hz).1))).of_le (by simp)
  have hnorm_yx : ‖y - x‖ ≤ max R R' + 1 := by
    have h1 : 1 ≤ (max R R' + 1) / ‖x‖ := (one_le_div hx_pos).2 hx_lt_R₁.le
    rw [show y - x = ((max R R' + 1) / ‖x‖ - 1) • x by simp [y, sub_smul], norm_smul,
      Real.norm_of_nonneg (sub_nonneg.2 h1), sub_mul, div_mul_cancel₀ _ hx_pos.ne', one_mul]
    linarith
  have hed :
      edist (φ x) (φ y) ≤
        ENNReal.ofReal ((max R R' + 1) * (n : ℝ) *
          Real.sqrt (1 + max C 0 * max (R ^ (-t)) ((max R R' + 1) ^ (-t)))) := by
    refine IsRiemannianManifold.edist_le_of_norm_mfderiv_le hdiff fun z hz ↦ ?_
    rw [← NormedSpace.fromTangentSpace_symm_apply z (y - x)]
    exact (norm_mfderiv_le_of_compl_closedBall h hC (hseg z hz).1 (hseg z hz).2 (y - x)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm_yx (Nat.cast_nonneg n))
        (Real.sqrt_nonneg _))
  rw [dist_edist]
  have hnonneg : 0 ≤ (max R R' + 1) * (n : ℝ) *
      Real.sqrt (1 + max C 0 * max (R ^ (-t)) ((max R R' + 1) ^ (-t))) :=
    mul_nonneg (mul_nonneg (by linarith [h.radius_pos, le_max_left R R']) (Nat.cast_nonneg n))
      (Real.sqrt_nonneg _)
  exact ENNReal.toReal_le_of_le_ofReal hnonneg hed

/-- On a Riemannian manifold, the image of the collar `(closedBall 0 R)ᶜ ∩ closedBall 0 R'` under
an asymptotically Euclidean end is bounded, since each point is joined radially to the compact
sphere of radius `max R R' + 1` along a segment of uniformly bounded differential. -/
private theorem isBounded_image_compl_inter_closedBall {M : Type*} [PseudoMetricSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] {R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (R' : ℝ) :
    Bornology.IsBounded
      (φ '' ((closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ ∩ closedBall 0 R')) := by
  set R₁ : ℝ := max R R' + 1
  have hR₁_gt : R < R₁ := lt_of_le_of_lt (le_max_left R R') (lt_add_one _)
  have hR₁_pos : 0 < R₁ := h.radius_pos.trans hR₁_gt
  have hsph_sub : sphere (0 : EuclideanSpace ℝ (Fin n)) R₁ ⊆ (closedBall 0 R)ᶜ := fun y hy ↦ by
    simpa [mem_sphere_zero_iff_norm.1 hy] using hR₁_gt
  have hsph_bdd : Bornology.IsBounded (φ '' sphere (0 : EuclideanSpace ℝ (Fin n)) R₁) :=
    ((isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) R₁).image_of_continuousOn
      (h.contMDiffOn.continuousOn.mono hsph_sub)).isBounded
  rcases (φ '' sphere (0 : EuclideanSpace ℝ (Fin n)) R₁).eq_empty_or_nonempty with hs | ⟨p₀, -⟩
  · have hempty :
        φ '' ((closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ ∩ closedBall 0 R') = ∅ := by
      refine eq_empty_of_subset_empty ?_
      rintro _ ⟨x, hx, rfl⟩
      have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (h.radius_pos.trans (by simpa using hx.1)).ne'
      have hy : (R₁ / ‖x‖) • x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) R₁ := by
        simp [norm_smul, abs_of_pos hR₁_pos, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hx0)]
      exact (Set.eq_empty_iff_forall_notMem.1 hs) _ ⟨(R₁ / ‖x‖) • x, hy, rfl⟩
    rw [hempty]
    exact Bornology.isBounded_empty
  · obtain ⟨r₀, hr₀⟩ := (Metric.isBounded_iff_subset_closedBall p₀).1 hsph_bdd
    obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
    let D : ℝ := R₁ * (n : ℝ) * Real.sqrt (1 + max C 0 * max (R ^ (-t)) (R₁ ^ (-t)))
    refine (Metric.isBounded_iff_subset_closedBall p₀).2 ⟨D + r₀, ?_⟩
    rintro _ ⟨x, ⟨hxR, hxR'⟩, rfl⟩
    have hxR_lt : R < ‖x‖ := by simpa using hxR
    have hx_pos : 0 < ‖x‖ := h.radius_pos.trans hxR_lt
    have hy_sph : (R₁ / ‖x‖) • x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) R₁ := by
      simp [norm_smul, abs_of_pos hR₁_pos, div_mul_cancel₀ _ hx_pos.ne']
    have hdist_xy : dist (φ x) (φ ((R₁ / ‖x‖) • x)) ≤ D :=
      dist_image_radial_le rfl h hC hxR_lt (by simpa using hxR')
    exact mem_closedBall.2 ((dist_triangle _ _ _).trans
      (add_le_add hdist_xy (mem_closedBall.1 (hr₀ ⟨_, hy_sph, rfl⟩))))

/-- Cutting the ends of a finite-ended asymptotically Euclidean structure on a proper `C¹`
Riemannian manifold at larger radii `R' ≥ R` preserves the finite-ended structure. -/
theorem mono_radius_of_properSpace {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    [ProperSpace M] [IsManifold I 1 M] {φ : ι → EuclideanSpace ℝ (Fin n) → M}
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) {R' : ι → ℝ} (hR : ∀ a, R a ≤ R' a) :
    IsFiniteEndedAsymptoticallyEuclidean I t R' φ :=
  h.mono_radius_of_compact_collar hR fun a ↦
    ⟨closure (φ a '' ((closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a))ᶜ ∩ closedBall 0 (R' a))),
      (isBounded_image_compl_inter_closedBall (h.isAsymptoticallyEuclideanEnd a)
        (R' a)).isCompact_closure,
      subset_closure⟩

/-- Cutting the ends of a finite-ended asymptotically Euclidean structure on a complete Riemannian
manifold at larger radii `R' ≥ R` preserves the finite-ended structure. -/
theorem mono_radius_of_completeSpace {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] {φ : ι → EuclideanSpace ℝ (Fin n) → M}
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) {R' : ι → ℝ} (hR : ∀ a, R a ≤ R' a) :
    IsFiniteEndedAsymptoticallyEuclidean I t R' φ := by
  have : ProperSpace M := Manifold.properSpace_of_completeSpace I
  exact h.mono_radius_of_properSpace hR

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
