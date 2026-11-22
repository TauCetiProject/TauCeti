/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Regular

/-!
# Cofinal neighbourhood shrinking in normal spaces

In a normal space, any cofinal family of neighbourhoods of a closed set `A` contains a member whose
closure lies inside a given open neighbourhood of `A`
(`TauCeti.normal_exists_closure_subset_of_cofinal`).
For a countable cofinal family `U : ℕ → Set X` of open neighbourhoods of `A`, iterating this gives a
shrinking index sequence `TauCeti.shrinkingNhdsSetIndex` with
`closure (U (φ (n + 1))) ⊆ U (φ n) ∩ U (n + 1)` and `U (φ n) ⊆ U n`.
-/

public section

open Set Topology

namespace TauCeti

/-- In a normal space, any cofinal family of neighborhoods of a closed set `A` contains a member
whose closure lies inside a given open neighborhood `V` of `A`. -/
theorem normal_exists_closure_subset_of_cofinal {X : Type*} {ι : Sort*} [TopologicalSpace X]
    [NormalSpace X] {A V : Set X} (hA : IsClosed A) (hV : IsOpen V) (hAV : A ⊆ V)
    {U : ι → Set X} (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ i, U i ⊆ W) :
    ∃ i, closure (U i) ⊆ V := by
  obtain ⟨W, hW_open, hAW, hW_cl⟩ := normal_exists_closure_subset hA hV hAV
  exact let ⟨i, hi⟩ := hU_cofinal hW_open hAW; ⟨i, (closure_mono hi).trans hW_cl⟩

section CofinalNeighborhoods

variable {X : Type*} [TopologicalSpace X] [hNorm : NormalSpace X] {A : Set X} (hA : IsClosed A)
  {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
  (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
include hNorm hA hU_open hAU hU_cofinal

/-- Shrinking index sequence extracted from a countable cofinal open neighbourhood family of `A`. -/
noncomputable def shrinkingNhdsSetIndex : ℕ → ℕ
  | 0 => 0
  | n + 1 => (normal_exists_closure_subset_of_cofinal hA
      ((hU_open (shrinkingNhdsSetIndex n)).inter (hU_open (n + 1)))
      (subset_inter (hAU _) (hAU (n + 1))) hU_cofinal).choose

/-- At `0`, `shrinkingNhdsSetIndex` starts at `0`. -/
@[simp] lemma shrinkingNhdsSetIndex_zero :
    shrinkingNhdsSetIndex hA hU_open hAU hU_cofinal 0 = 0 := (rfl)

/-- The closure of `U (shrinkingNhdsSetIndex ... (n + 1))` lies in the intersection of
`U (shrinkingNhdsSetIndex ... n)` and `U (n + 1)`. -/
lemma closure_apply_shrinkingNhdsSetIndex_succ_subset_inter (n : ℕ) :
    closure (U (shrinkingNhdsSetIndex hA hU_open hAU hU_cofinal (n + 1))) ⊆
      U (shrinkingNhdsSetIndex hA hU_open hAU hU_cofinal n) ∩ U (n + 1) :=
  (normal_exists_closure_subset_of_cofinal hA
    ((hU_open (shrinkingNhdsSetIndex hA hU_open hAU hU_cofinal n)).inter (hU_open (n + 1)))
    (subset_inter (hAU _) (hAU (n + 1))) hU_cofinal).choose_spec

/-- Each selected neighbourhood `U (shrinkingNhdsSetIndex ... n)` is contained in `U n`. -/
lemma apply_shrinkingNhdsSetIndex_subset :
    ∀ n, U (shrinkingNhdsSetIndex hA hU_open hAU hU_cofinal n) ⊆ U n
  | 0 => Subset.rfl
  | n + 1 => subset_closure.trans <|
      (closure_apply_shrinkingNhdsSetIndex_succ_subset_inter hA hU_open hAU hU_cofinal n).trans
        inter_subset_right

end CofinalNeighborhoods

end TauCeti
