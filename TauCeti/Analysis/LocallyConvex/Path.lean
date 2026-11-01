/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Order.ProjIcc

/-!
# Smoothing paths by finite convex combinations

A continuous path in a real topological vector space can be approximated by finitely many of
its values with smooth nonnegative scalar weights summing to one. The approximation is relative
to the endpoints and has constant tails. The error is measured in an arbitrary convex
neighbourhood of zero, against the original path with a fixed smooth change of parameter.

In a locally convex space, the approximation can be chosen to stay in any prescribed open set
containing the path. This applies to spaces of smooth sections, which need not be normable:
smoothness here is expressed by the finite scalar weights, rather than by a norm on the target.
Convex constraints shared by the sampled values are preserved. In particular, when smoothing
paths of metrics, values fixed on a spatial subset remain fixed there.

The construction uses Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`, by Yury
Kudryashov, and `Real.smoothTransition`. It is the usual partition-of-unity smoothing argument.
-/

public section

open Set Filter
open scoped Topology BigOperators ContDiff Manifold

noncomputable section

namespace ContinuousMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E]

/-- A continuous path admits finite convex combinations with smooth scalar weights and exact
endpoint tails. Their error, relative to the path at `smoothTransition (3 * t - 1)`, lies in any
specified convex neighbourhood of zero. No norm, completeness or local convexity is required. -/
theorem exists_smooth_convexCombination_sub_mem (f : C(unitInterval, E))
    {W : Set E} (hW : W ∈ 𝓝 (0 : E)) (hconv : Convex ℝ W) :
    ∃ (s : Finset unitInterval) (w : s → ℝ → ℝ),
      (∀ i, ContDiff ℝ ∞ (w i)) ∧
      (∀ i t, 0 ≤ w i t) ∧ (∀ t, ∑ i, w i t = 1) ∧
      (∀ t, t ≤ 1 / 3 → (∑ i, w i t • f i.1) = f 0) ∧
      (∀ t, 2 / 3 ≤ t → (∑ i, w i t • f i.1) = f 1) ∧
      ∀ t, (∑ i, w i t • f i.1) -
        f ⟨Real.smoothTransition (3 * t - 1),
          Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ ∈ W := by
  classical
  let p : ℝ → unitInterval := projIcc 0 1 zero_le_one
  have hp : Continuous p := continuous_projIcc
  -- Choose sample neighbourhoods that exclude an endpoint unless it is the sample itself.
  let U : unitInterval → Set ℝ := fun a ↦
    {t | f a - f (p t) ∈ interior W} ∩
      (if a = 0 then univ else {0}ᶜ) ∩ (if a = 1 then univ else {1}ᶜ)
  have hUo (a : unitInterval) : IsOpen (U a) := by
    have h : IsOpen {t | f a - f (p t) ∈ interior W} :=
      isOpen_interior.preimage (continuous_const.sub (f.continuous.comp hp))
    exact (h.inter (by split_ifs <;> simp)).inter (by split_ifs <;> simp)
  have hUa (a : unitInterval) : (a : ℝ) ∈ U a := by
    have hzero : (0 : E) ∈ interior W := mem_interior_iff_mem_nhds.2 hW
    simp only [U, mem_inter_iff, mem_ofPred_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [p] using hzero
    · split_ifs with ha
      · trivial
      · simpa using ha
    · split_ifs with ha
      · trivial
      · simpa using ha
  obtain ⟨s, hs⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).elim_finite_subcover U hUo
    (fun t ht ↦ mem_iUnion_of_mem (⟨t, ht⟩ : unitInterval) (hUa ⟨t, ht⟩))
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ) isClosed_Icc
    (fun i : s ↦ U i.1) (fun i ↦ hUo i.1) (by
      intro t ht
      obtain ⟨a, ha, hta⟩ := mem_iUnion₂.mp (hs ht)
      exact mem_iUnion_of_mem (⟨a, ha⟩ : s) hta)
  let θ : ℝ → ℝ := fun t ↦ Real.smoothTransition (3 * t - 1)
  have hθ : ContDiff ℝ ∞ θ := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hθmem (t : ℝ) : θ t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hsum (t : ℝ) : ∑ i : s, ρ i (θ t) = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (hθmem t)
  have hactive {i : s} {t : ℝ} (hi : ρ i t ≠ 0) : t ∈ U i.1 :=
    hρ i (subset_closure hi)
  -- At an endpoint, every nonzero weight is attached to that endpoint.
  have hend (a : unitInterval) (ha : a = 0 ∨ a = 1) :
      ∑ i : s, ρ i a • f i.1 = f a := by
    have heq (i : s) : ρ i a • f i.1 = ρ i a • f a := by
      by_cases hi : ρ i a = 0
      · simp [hi]
      have h := hactive hi
      have hia : i.1 = a := by
        rcases ha with rfl | rfl
        · by_contra hi0
          simpa [U, hi0] using h.1.2
        · by_contra hi1
          simpa [U, hi1] using h.2
      rw [hia]
    rw [Finset.sum_congr rfl (fun i _ ↦ heq i), ← Finset.sum_smul]
    have hsum' : ∑ i : s, ρ i a = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one a.2
    rw [hsum', one_smul]
  refine ⟨s, fun i t ↦ ρ i (θ t), fun i ↦ ?_, fun i t ↦ ρ.nonneg i _, hsum,
    fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ↦ ?_⟩
  · exact (ρ i).contMDiff.contDiff.comp hθ
  · have htθ : θ t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    simpa [htθ] using hend 0 (Or.inl rfl)
  · have htθ : θ t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    simpa [htθ] using hend 1 (Or.inr rfl)
  -- A convex combination of the active errors remains in the prescribed neighbourhood.
  · have hmem : (∑ᶠ i : s, ρ i (θ t) • (f i.1 - f (p (θ t)))) ∈ W :=
      hconv.finsum_mem (fun i ↦ ρ.nonneg i _) (ρ.sum_eq_one (hθmem t))
        (fun i hi ↦ interior_subset (hactive hi).1.1)
    simpa only [finsum_eq_sum_of_fintype, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hsum, one_smul, p, projIcc_of_mem _ (hθmem t)] using hmem

/-- In a locally convex space, a continuous path in an open set can be replaced by finite
convex combinations of its values with smooth scalar weights. The combinations stay in the
open set for every real parameter and agree exactly with the endpoints on constant tails.
The target need not be normable or complete. -/
theorem exists_smooth_convexCombination_mem [LocallyConvexSpace ℝ E]
    (f : C(unitInterval, E)) {U : Set E} (hU : IsOpen U) (hf : ∀ t, f t ∈ U) :
    ∃ (s : Finset unitInterval) (w : s → ℝ → ℝ),
      (∀ i, ContDiff ℝ ∞ (w i)) ∧
      (∀ i t, 0 ≤ w i t) ∧ (∀ t, ∑ i, w i t = 1) ∧
      (∀ t, t ≤ 1 / 3 → (∑ i, w i t • f i.1) = f 0) ∧
      (∀ t, 2 / 3 ≤ t → (∑ i, w i t • f i.1) = f 1) ∧
      ∀ t, (∑ i, w i t • f i.1) ∈ U := by
  -- Compactness supplies a single perturbation neighbourhood for the entire path.
  have hprod : {q : E × unitInterval | f q.2 + q.1 ∈ U} ∈
      𝓝 (0 : E) ×ˢ 𝓝ˢ (univ : Set unitInterval) :=
    isCompact_univ.mem_prod_nhdsSet_of_forall fun t _ ↦ by
      rw [← nhds_prod_eq]
      exact (hU.preimage ((f.continuous.comp continuous_snd).add continuous_fst)).mem_nhds
        (by simpa using hf t)
  have hN : {z | ∀ t, f t + z ∈ U} ∈ 𝓝 (0 : E) := by
    simpa only [nhdsSet_univ, mem_prod_top, mem_ofPred_eq] using hprod
  obtain ⟨W, hW, hWN⟩ := (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.1 hN
  obtain ⟨s, w, hw, hnonneg, hsum, hleft, hright, herr⟩ :=
    f.exists_smooth_convexCombination_sub_mem hW.1 hW.2
  refine ⟨s, w, hw, hnonneg, hsum, hleft, hright, fun t ↦ ?_⟩
  simpa only [add_sub_cancel] using hWN (herr t)
    ⟨Real.smoothTransition (3 * t - 1),
      Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

end ContinuousMap
