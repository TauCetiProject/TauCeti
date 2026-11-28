/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Distance
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Rescale
import TauCeti.Analysis.Normed.Module.Ball.Exterior
import TauCeti.Topology.MetricSpace.Annulus

/-!
# Finite-ended asymptotically Euclidean manifolds

This module extends `TauCeti.IsFiniteEndedAsymptoticallyEuclidean` (from
`TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic`) with topological, compact
truncation, compact exhaustion, and scaling results.

Note that `IsFiniteEndedAsymptoticallyEuclidean.isCompact_compl_iUnion` controls only the complement
of the initial cover at radii `R`; cutting the ends at larger radii `R' ≥ R` need not leave a
compact complement on an incomplete manifold, so compact truncation is proved separately under a
compact-collar or Riemannian completeness hypothesis. On a complete Riemannian manifold of positive
order, truncating the ends at radii `R a + k` yields a `CompactExhaustion M`.

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
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.compactExhaustion`: on a complete Riemannian
  manifold of positive order, cutting the ends at radii `R a + k` gives a `CompactExhaustion M`.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.rescale`: constant metric rescaling `g ↦ c • g`
  preserves finite-ended asymptotically Euclidean structures.

## References

* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  661–693.
* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, Trans. Amer. Math. Soc. 377 (2024), 5271–5288, Definition 2.3 (arXiv:2108.11972v2).
-/

public section

noncomputable section

open Bornology Bundle Filter Metric Set TopologicalSpace
open scoped ContDiff Manifold Pointwise Topology

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

/-- For a positive-order end `φ` on a Hausdorff `C¹` Riemannian manifold, the closure of the
exterior image at radius `r + (k + 1)` is contained in the exterior image at radius `r + k`. -/
private theorem closure_image_compl_closedBall_succ_subset
    {M : Type*} [PseudoEMetricSpace M] [T2Space M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    [IsManifold I 1 M] {r : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}
    (h : IsAsymptoticallyEuclideanEnd I t r φ) (ht : 0 < t) (k : ℕ) :
    closure (φ '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (r + ((k + 1 : ℕ) : ℝ)))ᶜ) ⊆
      φ '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (r + k))ᶜ := by
  intro p hp
  -- Choose `a ≥ r` so `‖dφ_z v‖ ≥ (1 / 2) ‖v‖` for `‖z‖ > a` and `p ∉ φ '' (closedBall 0 a)ᶜ`.
  obtain ⟨r₀, -, hr₀⟩ :=
    (hasBasis_cobounded_compl_closedBall (0 : EuclideanSpace ℝ (Fin n))).eventually_iff.1
      (h.eventually_abs_norm_mfderiv_sub_norm_le ht (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨a, ha, hpa⟩ := ((eventually_ge_atTop (max r₀ r)).and
    (h.eventually_notMem_image_compl_closedBall p)).exists
  have hc (z) (hz : z ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) a)ᶜ)
      (v : EuclideanSpace ℝ (Fin n)) :
      (1 / 2 : ℝ) * ‖v‖ ≤ ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z v‖ := by
    have hz₀ := hr₀ (compl_subset_compl.2 (closedBall_subset_closedBall
      ((le_max_left r₀ r).trans ha)) hz) v
    linarith [neg_abs_le (‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z v‖ - ‖v‖)]
  -- By the extended-distance lower bound, any `φ z ∈ eball p 1` has `‖z‖ ≤ a + 2`.
  let R₀ : ℝ := a + 2
  have hR₀ {z : EuclideanSpace ℝ (Fin n)} (hzb : φ z ∈ eball p 1) : ‖z‖ ≤ R₀ := by
    have hed := (h.ofReal_mul_sub_le_riemannianEDist ((le_max_right r₀ r).trans ha)
      (by norm_num) hc hpa z).trans_eq (IsRiemannianManifold.out (I := I) (φ z) p).symm
    have hlt : ENNReal.ofReal ((1 / 2 : ℝ) * (‖z‖ - a)) < ENNReal.ofReal 1 := by
      simpa only [ENNReal.ofReal_one] using hed.trans_lt (mem_eball.1 hzb)
    linarith [(ENNReal.ofReal_lt_ofReal_iff one_pos).1 hlt]
  -- Restrict to the compact annulus `A = {z | r + (k + 1) ≤ ‖z‖ ≤ R₀}`.
  let A : Set (EuclideanSpace ℝ (Fin n)) :=
    {z | r + ((k + 1 : ℕ) : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ R₀}
  have hA_comp : IsCompact A := by
    simpa only [A, sub_zero] using
      isCompact_setOf_le_norm_sub_le (0 : EuclideanSpace ℝ (Fin n)) (r + ((k + 1 : ℕ) : ℝ)) R₀
  have hAk : A ⊆ (closedBall (0 : EuclideanSpace ℝ (Fin n)) (r + k))ᶜ := fun z hz ↦ by
    simp only [mem_compl_iff, mem_closedBall_zero_iff, not_le]
    have hk : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self k
    linarith [hz.1]
  have hAR : A ⊆ (closedBall (0 : EuclideanSpace ℝ (Fin n)) r)ᶜ :=
    hAk.trans (compl_subset_compl.2 (closedBall_subset_closedBall
      (le_add_of_nonneg_right (Nat.cast_nonneg k))))
  -- Because `A` is compact and `φ` is continuous on `(closedBall 0 r)ᶜ`, `φ '' A` is closed.
  have hφA_closed : IsClosed (φ '' A) :=
    (hA_comp.image_of_continuousOn (h.contMDiffOn.continuousOn.mono hAR)).isClosed
  -- Every neighbourhood of `p` meets `φ '' (closedBall 0 (r + k + 1))ᶜ` inside `eball p 1`,
  -- whose preimages lie in `A`; hence `p ∈ closure (φ '' A) = φ '' A`.
  have hp_cl : p ∈ closure (φ '' A) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨q, ⟨hqU, hqb⟩, z, hz, rfl⟩ :=
      mem_closure_iff_nhds.1 hp (U ∩ eball p 1) (inter_mem hU (eball_mem_nhds p one_pos))
    have hz_gt : r + ((k + 1 : ℕ) : ℝ) < ‖z‖ := by simpa using hz
    exact ⟨φ z, hqU, z, ⟨hz_gt.le, hR₀ hqb⟩, rfl⟩
  rw [hφA_closed.closure_eq] at hp_cl
  exact image_mono hAk hp_cl

/-- A complete Hausdorff `C¹` finite-ended asymptotically Euclidean manifold (with extended
Riemannian distance) of positive order admits a compact exhaustion whose `k`-th stage is the
complement of the end exteriors at radii `R a + k`. -/
def compactExhaustion {M : Type*} [PseudoEMetricSpace M] [T2Space M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsManifold I 1 M] {φ : ι → EuclideanSpace ℝ (Fin n) → M}
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) (ht : 0 < t) : CompactExhaustion M where
  toFun k := (⋃ a, φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a + k))ᶜ)ᶜ
  isCompact' k :=
    (h.mono_radius_of_completeSpace fun a ↦ le_add_of_nonneg_right
      (Nat.cast_nonneg k)).isCompact_compl_iUnion
  subset_interior_succ' k := by
    have := h.finite
    rw [interior_compl, compl_subset_compl, closure_iUnion_of_finite]
    exact iUnion_mono fun a ↦
      closure_image_compl_closedBall_succ_subset (h.isAsymptoticallyEuclideanEnd a) ht k
  iUnion_eq' := by
    classical
    have := h.finite
    let : Fintype ι := Fintype.ofFinite ι
    ext p
    simp only [mem_iUnion, mem_compl_iff, mem_univ, iff_true, not_exists]
    have hfa (a : ι) : ∃ r : ℝ, ∀ s, r ≤ s → p ∉ φ a '' (closedBall 0 s)ᶜ :=
      eventually_atTop.1
        ((h.isAsymptoticallyEuclideanEnd a).eventually_notMem_image_compl_closedBall p)
    choose f hf using hfa
    choose g hg using fun a ↦ exists_nat_ge (f a - R a)
    refine ⟨Finset.univ.sup g, fun a ↦ hf a _ ?_⟩
    have hga : (g a : ℝ) ≤ (Finset.univ.sup g : ℕ) :=
      Nat.cast_le.2 (Finset.le_sup (Finset.mem_univ a))
    linarith [hg a]

/-- The `k`-th stage of `IsFiniteEndedAsymptoticallyEuclidean.compactExhaustion` is the
complement of the union of the end exteriors at radii `R a + k`. -/
@[simp]
theorem compactExhaustion_apply {M : Type*} [PseudoEMetricSpace M] [T2Space M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsManifold I 1 M] {φ : ι → EuclideanSpace ℝ (Fin n) → M}
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) (ht : 0 < t) (k : ℕ) :
    h.compactExhaustion ht k =
      (⋃ a, φ a '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R a + k))ᶜ)ᶜ := by
  rfl

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

end IsFiniteEndedAsymptoticallyEuclidean

end TauCeti

end
