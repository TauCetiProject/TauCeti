/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic

/-!
# Clusters of marks in a cyclic word

A set of marked positions in `ZMod N` has clusters of depth `j` if a mark either has no mark
within the preceding `j` positions, or has one at distance `e ≤ j` and no other within the
preceding `e + j` positions. When `2 * j < N`, all the backwards distances tested are shorter
than a full turn. We give a criterion in terms of the number of marks in each window of the
integer lift of the word; it applies without choosing a cut in the cycle.
-/

public section

namespace Set

variable {N j L : ℕ} {S T : Set (ZMod N)}

/-- If a mark at `i` has a preceding mark at distance `e` with `0 < e ≤ j`, any mark at a
positive backwards distance at most `e + j` must be that same predecessor. -/
def HasMarkClusters (S : Set (ZMod N)) (j : ℕ) : Prop :=
  ∀ i ∈ S, ∀ e : ℕ, 0 < e → e ≤ j → i - e ∈ S →
    ∀ d : ℕ, 0 < d → d ≤ e + j → i - d ∈ S → d = e

/-- Unfolds `Set.HasMarkClusters` to its defining condition. -/
theorem hasMarkClusters_def : S.HasMarkClusters j ↔
    ∀ i ∈ S, ∀ e : ℕ, 0 < e → e ≤ j → i - e ∈ S →
      ∀ d : ℕ, 0 < d → d ≤ e + j → i - d ∈ S → d = e :=
  Iff.rfl

/-- Uses a mark at `i` and a marked predecessor at distance `e ≤ j` to identify any marked
predecessor within distance `e + j`. -/
theorem HasMarkClusters.eq (h : S.HasMarkClusters j) {i : ZMod N} (hi : i ∈ S) {d e : ℕ}
    (he : 0 < e) (hej : e ≤ j) (hem : i - e ∈ S) (hd : 0 < d) (hdj : d ≤ e + j)
    (hdm : i - d ∈ S) : d = e :=
  h i hi e he hej hem d hd hdj hdm

/-- The empty set of marks has clusters of every depth. -/
@[simp]
theorem hasMarkClusters_empty : (∅ : Set (ZMod N)).HasMarkClusters j :=
  fun _ hi ↦ hi.elim

/-- At most one mark gives clusters of every depth below the period. The bound on the depth is
needed: for `N = 1` a single mark is its own predecessor at every distance. -/
theorem HasMarkClusters.of_subsingleton (hS : S.Subsingleton) (hj : j < N) :
    S.HasMarkClusters j := by
  intro i hi e he hej hem
  have h0 : ((e : ℕ) : ZMod N) = 0 := sub_eq_self.1 (hS hem hi)
  have hdvd : N ∣ e := (ZMod.natCast_eq_zero_iff e N).1 h0
  exact absurd (Nat.le_of_dvd he hdvd) (by omega)

/-- Each marked position is either isolated from its preceding `j` positions or has a unique
marked predecessor within the enlarged window. -/
theorem hasMarkClusters_iff : S.HasMarkClusters j ↔
    ∀ i ∈ S, (∀ e : ℕ, 0 < e → e ≤ j → i - e ∉ S) ∨
      ∃ e : ℕ, 0 < e ∧ e ≤ j ∧ i - e ∈ S ∧
        ∀ d : ℕ, 0 < d → d ≤ e + j → i - d ∈ S → d = e := by
  classical
  constructor
  · intro h i hi
    by_cases h' : ∃ e : ℕ, 0 < e ∧ e ≤ j ∧ i - e ∈ S
    · obtain ⟨e, he, hej, hmem⟩ := h'
      exact Or.inr ⟨e, he, hej, hmem, h i hi e he hej hmem⟩
    · exact Or.inl fun e he hej hmem ↦ h' ⟨e, he, hej, hmem⟩
  · intro h i hi e he hej hmem d hd hde hdmem
    rcases h i hi with hnone | ⟨a, _, _, _, ha⟩
    · exact (hnone e he hej hmem).elim
    · have hea := ha e he (by omega) hmem
      exact hea ▸ ha d hd (by omega) hdmem

/-- Deleting marked positions preserves the cluster property. -/
theorem HasMarkClusters.mono (h : S.HasMarkClusters j) (hTS : T ⊆ S) : T.HasMarkClusters j :=
  fun i hi e he hej hem d hd hdj hdm ↦ h i (hTS hi) e he hej (hTS hem) d hd hdj (hTS hdm)

/-- If every window of `L` consecutive integer positions contains at most two marks, a marked
position cannot have two distinct marked predecessors at positive distances less than `L`. -/
theorem eq_of_sub_mem_of_encard_window_le_two
    (h : ∀ k : ℤ, {i ∈ Ico k (k + L) | (i : ZMod N) ∈ S}.encard ≤ 2)
    {i : ZMod N} (hi : i ∈ S) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hdL : d < L) (heL : e < L)
    (hdm : i - d ∈ S) (hem : i - e ∈ S) : d = e := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective i
  by_contra hne
  let k : ℤ := a + 1 - L
  let W : Set ℤ := {b ∈ Ico k (k + L) | (b : ZMod N) ∈ S}
  have hwin (t : ℕ) (ht : t < L) : a - t ∈ Ico k (k + L) := by
    dsimp [k]
    exact ⟨by omega, by omega⟩
  have ha : a ∈ W := ⟨by simpa using hwin 0 (by omega), hi⟩
  have hda : a - d ∈ W := ⟨hwin d hdL, by simpa using hdm⟩
  have hea : a - e ∈ W := ⟨hwin e heL, by simpa using hem⟩
  have hthree : ({a, a - d, a - e} : Set ℤ).encard = 3 :=
    encard_eq_three.2 ⟨a, a - d, a - e, by omega, by omega, by omega, rfl⟩
  have hle : ({a, a - d, a - e} : Set ℤ).encard ≤ W.encard :=
    encard_le_encard (insert_subset ha (insert_subset hda (singleton_subset_iff.2 hea)))
  have hbad : (3 : ℕ∞) ≤ 2 := hthree ▸ hle.trans (h k)
  exact (by decide : ¬ (3 : ℕ∞) ≤ 2) hbad

/-- At most two marks in every `L`-position window gives clusters of depth `j` if the current
position and its preceding `2 * j` positions fit in a window. -/
theorem HasMarkClusters.of_encard_window_le_two
    (h : ∀ k : ℤ, {i ∈ Ico k (k + L) | (i : ZMod N) ∈ S}.encard ≤ 2) (hj : 2 * j < L) :
    S.HasMarkClusters j :=
  fun _ hi _ he hej hem _ hd hdj hdm ↦
    eq_of_sub_mem_of_encard_window_le_two h hi hd he (by omega) (by omega) hdm hem

end Set
