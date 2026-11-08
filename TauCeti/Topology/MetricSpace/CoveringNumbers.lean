/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Topology.MetricSpace.CoveringNumbers
-- Private: `ENat.toENNReal_iSup` is used only in a proof.
import Mathlib.Algebra.Order.Floor.Extended

/-!
# Packing numbers and separated sets

Two metric facts about `ε`-separated sets, used to bound packing and covering numbers.

## Main results

* `TauCeti.packingNumber_le_of_forall_finset_card_le`: a finite bound on the sizes of the finite
  `ε`-separated subsets of a set bounds its packing number.
* `Metric.IsSeparated.pairwiseDisjoint_closedBall`: the closed balls of radius `ε / 2` around
  the points of an `ε`-separated set are pairwise disjoint.
-/

public section

open Metric Set
open scoped ENNReal NNReal

namespace TauCeti

/-- If every finite `ε`-separated subset of `A` has at most `B ≠ ∞` elements, then the packing
number of `A` at scale `ε` is at most `B`. -/
theorem packingNumber_le_of_forall_finset_card_le {X : Type*} [PseudoEMetricSpace X] {ε : ℝ≥0}
    {A : Set X} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (h : ∀ s : Finset X, (s : Set X) ⊆ A → IsSeparated ε (s : Set X) → (s.card : ℝ≥0∞) ≤ B) :
    (packingNumber ε A : ℝ≥0∞) ≤ B := by
  rw [packingNumber]
  simp only [ENat.toENNReal_iSup]
  refine iSup₂_le fun C hCA ↦ iSup_le fun hC ↦ ?_
  rcases C.finite_or_infinite with hCf | hCi
  · rw [hCf.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
    exact h hCf.toFinset (by simpa using hCA) (by simpa using hC)
  · -- An infinite separated subset would contain finite separated subsets of every size.
    exfalso
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hB
    obtain ⟨s, hsC, rfl⟩ := hCi.exists_subset_card_eq n
    exact (h s (hsC.trans hCA) (hC.subset hsC)).not_gt hn

end TauCeti

namespace Metric

/-- The closed balls of radius `ε / 2` around the points of an `ε`-separated set are pairwise
disjoint. -/
theorem IsSeparated.pairwiseDisjoint_closedBall {X : Type*} [PseudoMetricSpace X] {ε : ℝ≥0}
    {C : Set X} (hC : IsSeparated ε C) : C.PairwiseDisjoint fun x ↦ closedBall x (ε / 2) := by
  intro x hx y hy hxy
  refine closedBall_disjoint_closedBall ?_
  have h : (ε : ℝ≥0∞) < edist x y := hC hx hy hxy
  rw [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nndist] at h
  linarith

end Metric
