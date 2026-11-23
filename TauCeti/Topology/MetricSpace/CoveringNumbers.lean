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
# Packing and covering numbers via finite subsets

Facts relating `ℕ∞`-valued packing and external covering numbers to finite separated sets and
finite covers.

## Main results

* `TauCeti.packingNumber_le_of_forall_finset_card_le`: a finite bound on the sizes of the finite
  `ε`-separated subsets of a set bounds its packing number.
* `Metric.IsSeparated.pairwiseDisjoint_closedBall`: the closed balls of radius `ε / 2` around
  the points of an `ε`-separated set are pairwise disjoint.
* `Metric.externalCoveringNumber_le_natCast_iff`: `externalCoveringNumber ε A ≤ k` if and only if
  `A` admits a finite `ε`-cover of cardinality at most `k`.
* `Metric.div_two_le_of_externalCoveringNumber_lt_card` and `Metric.IsCover.div_two_le_of_card_lt`:
  if `A` contains a finite subset of mutual distance at least `δ` strictly larger than an
  `ε`-cover, then `δ / 2 ≤ ε`.
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

/-- The external covering number of `A` at radius `ε` is at most a natural number `k` if and only
if `A` admits a finite `ε`-cover of cardinality at most `k`. -/
theorem externalCoveringNumber_le_natCast_iff {X : Type*} [PseudoEMetricSpace X] {ε : ℝ≥0}
    {A : Set X} {k : ℕ} :
    externalCoveringNumber ε A ≤ k ↔ ∃ N : Finset X, N.card ≤ k ∧ IsCover ε A N := by
  constructor
  · intro h
    have hlt : externalCoveringNumber ε A < (k : ℕ∞) + 1 :=
      (ENat.lt_add_one_iff (ENat.natCast_ne_top k)).mpr h
    simp only [externalCoveringNumber, iInf_lt_iff] at hlt
    obtain ⟨C, hC, hcard⟩ := hlt
    have hle : C.encard ≤ k := (ENat.lt_add_one_iff (ENat.natCast_ne_top k)).mp hcard
    have hfin : C.Finite := encard_lt_top_iff.mp (hle.trans_lt (ENat.natCast_lt_top k))
    refine ⟨hfin.toFinset, ?_, by simpa using hC⟩
    rwa [← Nat.cast_le (α := ℕ∞), ← hfin.encard_eq_coe_toFinset_card]
  · rintro ⟨N, hcard, hcov⟩
    exact hcov.externalCoveringNumber_le_encard.trans (by simpa using hcard)

/-- If `A` contains a finite subset `s` of points at mutual distance at least `δ` and the external
covering number of `A` at radius `ε` is strictly less than `s.card`, then `δ / 2 ≤ ε`. -/
theorem div_two_le_of_externalCoveringNumber_lt_card {X : Type*} [PseudoMetricSpace X] {ε : ℝ≥0}
    {A : Set X} {s : Finset X} {δ : ℝ} (hsA : (s : Set X) ⊆ A)
    (hsep : (s : Set X).Pairwise (δ ≤ dist · ·)) (hlt : externalCoveringNumber ε A < s.card) :
    δ / 2 ≤ ε := by
  by_contra! h
  have hsep' : IsSeparated (2 * ε : ℝ≥0) (s : Set X) := by
    intro x hx y hy hxy
    rw [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nndist, NNReal.coe_mul,
      NNReal.coe_ofNat]
    linarith [hsep hx hy hxy]
  have hle : (s.card : ℕ∞) ≤ externalCoveringNumber ε A := by
    simpa using (hsep'.encard_le_packingNumber hsA).trans
      (packingNumber_two_mul_le_externalCoveringNumber ε A)
  exact hlt.not_ge hle

/-- Pigeonhole principle for metric covers: if `N` is an `ε`-cover of `A` and `s ⊆ A` has
strictly more points than `N` at mutual distance at least `δ`, then `δ / 2 ≤ ε`. -/
theorem IsCover.div_two_le_of_card_lt {X : Type*} [PseudoMetricSpace X] {ε : ℝ≥0}
    {A : Set X} {s N : Finset X} {δ : ℝ} (hcov : IsCover ε A N) (hsA : (s : Set X) ⊆ A)
    (hsep : (s : Set X).Pairwise (δ ≤ dist · ·)) (hcard : N.card < s.card) :
    δ / 2 ≤ ε :=
  div_two_le_of_externalCoveringNumber_lt_card hsA hsep <|
    hcov.externalCoveringNumber_le_encard.trans_lt (by simpa using hcard)

end Metric
