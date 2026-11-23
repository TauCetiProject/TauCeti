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
    have hz0 := abs_pullbackMetricCoeff_sub_one_le hC (by simpa using hz_gt) (i := i) (j := i)
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at hz0
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

/-- Radial extended-distance estimate from `φ x` (`R < ‖x‖ < R₀ ≤ R₁`) to the outer sphere
`sphere 0 R₀`. -/
private theorem edist_image_radial_le {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    {R R₀ R₁ C : ℝ} (hR₀ : R₀ ≤ R₁)
    {φ : EuclideanSpace ℝ (Fin n) → M} (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (hC : ∀ k ≤ 2, ∀ (i j : Fin n), ∀ z ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ,
      ‖iteratedFDeriv ℝ k (fun y ↦ (pullbackMetricCoeff I φ y - 1) i j) z‖ ≤ C * ‖z‖ ^ (-t - k))
    {x : EuclideanSpace ℝ (Fin n)} (hxR : R < ‖x‖) (hxR₀ : ‖x‖ < R₀) :
    edist (φ x) (φ ((R₀ / ‖x‖) • x)) ≤
      ENNReal.ofReal ((R₀ - ‖x‖) * (n : ℝ) *
        Real.sqrt (1 + max C 0 * max (R ^ (-t)) (R₁ ^ (-t)))) := by
  have hx_pos : 0 < ‖x‖ := h.radius_pos.trans hxR
  let y : EuclideanSpace ℝ (Fin n) := (R₀ / ‖x‖) • x
  have hseg : ∀ z ∈ segment ℝ x y, R < ‖z‖ ∧ ‖z‖ ≤ R₁ := fun z hz ↦
    let ⟨hz1, hz2⟩ := radial_segment_norm_bounds hxR hx_pos hxR₀ hz
    ⟨hz1, hz2.trans hR₀⟩
  have hdiff : ∀ z ∈ segment ℝ x y, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I 1 φ z :=
    fun z hz ↦ (h.contMDiffOn.contMDiffAt
      (isClosed_closedBall.isOpen_compl.mem_nhds (by simpa using (hseg z hz).1))).of_le (by simp)
  have hnorm_yx : ‖y - x‖ = R₀ - ‖x‖ := by
    have h1 : 1 ≤ R₀ / ‖x‖ := (one_le_div hx_pos).2 hxR₀.le
    rw [show y - x = (R₀ / ‖x‖ - 1) • x by simp [y, sub_smul], norm_smul,
      Real.norm_of_nonneg (sub_nonneg.2 h1), sub_mul, div_mul_cancel₀ _ hx_pos.ne', one_mul]
  refine IsRiemannianManifold.edist_le_of_norm_mfderiv_le hdiff fun z hz ↦ ?_
  rw [← NormedSpace.fromTangentSpace_symm_apply z (y - x), ← hnorm_yx]
  exact norm_mfderiv_le_of_compl_closedBall h hC (hseg z hz).1 (hseg z hz).2 (y - x)

/-- Helper: given `ε > 0` in `ℝ≥0∞` and `0 ≤ M₁`, find `0 < η ≤ 1` with
`ofReal (η * M₁) < ε / 2`. -/
private theorem exists_pos_le_one_ofReal_mul_lt_half {ε : ℝ≥0∞} (hε : 0 < ε) {M₁ : ℝ}
    (hM₁ : 0 ≤ M₁) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ENNReal.ofReal (η * M₁) < ε / 2 := by
  obtain ⟨r, hr0, hr_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (ENNReal.half_pos hε.ne')
  have hr0' : (0 : ℝ) < r := NNReal.coe_pos.2 (ENNReal.coe_pos.1 hr0)
  refine ⟨min 1 ((r : ℝ) / (M₁ + 1)), lt_min zero_lt_one (div_pos hr0' (by linarith)),
    min_le_left _ _, ?_⟩
  have hmul : min 1 ((r : ℝ) / (M₁ + 1)) * M₁ ≤ r := by
    calc min 1 ((r : ℝ) / (M₁ + 1)) * M₁ ≤ ((r : ℝ) / (M₁ + 1)) * M₁ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hM₁
      _ = (r : ℝ) * (M₁ / (M₁ + 1)) := by ring
      _ ≤ (r : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one (by linarith)).2 (by linarith)) hr0'.le
      _ = r := mul_one _
  exact (ENNReal.ofReal_le_ofReal hmul).trans_lt (by simpa using hr_lt)

/-- Helper: the truncated inner collar `((ball 0 (R + η))ᶜ ∩ closedBall 0 R') ∪ sphere 0 (R + η)`
is compact and lies inside `(closedBall 0 R)ᶜ` when `0 < η`. -/
private theorem isCompact_truncCollar {R R' η : ℝ} (hη : 0 < η) :
    IsCompact (((ball (0 : EuclideanSpace ℝ (Fin n)) (R + η))ᶜ ∩ closedBall 0 R') ∪
        sphere 0 (R + η)) ∧
      ((ball (0 : EuclideanSpace ℝ (Fin n)) (R + η))ᶜ ∩ closedBall 0 R') ∪ sphere 0 (R + η) ⊆
        (closedBall 0 R)ᶜ := by
  refine ⟨((isCompact_closedBall 0 R').of_isClosed_subset
      (isOpen_ball.isClosed_compl.inter isClosed_closedBall) inter_subset_right).union
      (isCompact_sphere 0 (R + η)), ?_⟩
  rintro z (⟨hz, -⟩ | hz)
  · simp only [mem_compl_iff, mem_ball_zero_iff, not_lt, mem_closedBall_zero_iff] at hz ⊢
    linarith
  · simp only [mem_sphere_zero_iff_norm] at hz
    simp only [mem_compl_iff, mem_closedBall_zero_iff, not_le, hz]
    linarith

/-- On an extended-metric Riemannian manifold, the image of the collar
`(closedBall 0 R)ᶜ ∩ closedBall 0 R'` under an asymptotically Euclidean end is totally bounded,
since it is approximated in `edist` by compact inner truncations using the uniform radial
derivative bound. -/
private theorem totallyBounded_image_compl_inter_closedBall {M : Type*} [PseudoEMetricSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] {R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (R' : ℝ) :
    TotallyBounded (φ '' ((closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ ∩ closedBall 0 R')) := by
  rw [EMetric.totallyBounded_iff]
  intro ε hε
  -- Step 1: Choose a radial collar thickness `0 < η ≤ 1` so radial travel across `η` is `< ε / 2`.
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  set R₁ : ℝ := R + 1
  let M₁ : ℝ := (n : ℝ) * Real.sqrt (1 + max C 0 * max (R ^ (-t)) (R₁ ^ (-t)))
  have hM₁ : 0 ≤ M₁ := mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)
  obtain ⟨η, hη_pos, hη_le1, hη_mul⟩ := exists_pos_le_one_ofReal_mul_lt_half hε hM₁
  -- Step 2: Cover the compact truncated collar `A` by finitely many `(ε / 2)`-balls.
  let A : Set (EuclideanSpace ℝ (Fin n)) :=
    ((ball (0 : EuclideanSpace ℝ (Fin n)) (R + η))ᶜ ∩ closedBall 0 R') ∪ sphere 0 (R + η)
  obtain ⟨hA_comp, hA_sub⟩ := isCompact_truncCollar (n := n) (R := R) (R' := R') hη_pos
  have hφA_tb : TotallyBounded (φ '' A) :=
    (hA_comp.image_of_continuousOn (h.contMDiffOn.continuousOn.mono hA_sub)).totallyBounded
  obtain ⟨t₀, ht₀_fin, ht₀_cov⟩ :=
    EMetric.totallyBounded_iff.1 hφA_tb (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨t₀, ht₀_fin, ?_⟩
  -- Step 3: Points with `R + η ≤ ‖x‖` lie directly in `A`; points with `R < ‖x‖ < R + η`
  -- lie within `ε / 2` of their radial projection onto `sphere 0 (R + η) ⊆ A`.
  rintro _ ⟨x, ⟨hxR, hxR'⟩, rfl⟩
  have hxR_lt : R < ‖x‖ := by simpa using hxR
  rcases le_or_gt (R + η) ‖x‖ with hx_ge | hx_lt
  · have hxA : x ∈ A := Or.inl ⟨by simpa [mem_ball_zero_iff] using hx_ge, hxR'⟩
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (ht₀_cov ⟨x, hxA, rfl⟩)
    exact mem_iUnion₂.2 ⟨p, hp, Metric.eball_subset_eball ENNReal.half_le_self hxp⟩
  · have hx_pos : 0 < ‖x‖ := h.radius_pos.trans hxR_lt
    have hRη_pos : 0 < R + η := by linarith [h.radius_pos]
    let y : EuclideanSpace ℝ (Fin n) := ((R + η) / ‖x‖) • x
    have hyA : y ∈ A := Or.inr <| by
      simp [y, norm_smul, abs_of_pos hRη_pos, div_mul_cancel₀ _ hx_pos.ne']
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 (ht₀_cov ⟨y, hyA, rfl⟩)
    have hed : edist (φ x) (φ y) < ε / 2 := by
      have h1 : edist (φ x) (φ y) ≤ ENNReal.ofReal ((R + η - ‖x‖) * M₁) := by
        simpa only [mul_assoc] using
          edist_image_radial_le (R₁ := R₁) (by linarith) h hC hxR_lt hx_lt
      have h2 : (R + η - ‖x‖) * M₁ ≤ η * M₁ :=
        mul_le_mul_of_nonneg_right (by linarith) hM₁
      exact h1.trans_lt ((ENNReal.ofReal_le_ofReal h2).trans_lt hη_mul)
    refine mem_iUnion₂.2 ⟨p, hp, ?_⟩
    rw [Metric.mem_eball] at hyp ⊢
    exact (edist_triangle _ (φ y) _).trans_lt
      ((ENNReal.add_lt_add hed hyp).trans_eq (ENNReal.add_halves ε))

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
        ⟨(totallyBounded_image_compl_inter_closedBall (h.isAsymptoticallyEuclideanEnd a)
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
    rw [show ((fun y ↦ WithMetric.toWithMetric g_c (φ a (s⁻¹ • y))) :
        EuclideanSpace ℝ (Fin n) → WithMetric g_c) =
        WithMetric.toWithMetric g_c ∘ φ a ∘ (s⁻¹ • ·) from rfl,
      image_comp, image_comp, IsAsymptoticallyEuclideanEnd.image_inv_smul_compl_closedBall hs]
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
