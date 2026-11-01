/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic

/-!
# Combining diffeotopies with disjoint supports

Finitely many diffeotopies of `M`, each fixing every point outside a compact subset of its own
set `W i`, with the sets `W i` pairwise disjoint, combine into one diffeotopy which acts as each
of them on its own set. If the `i`-th motion carries `a i` to `b i` on `A`, and both `a i` and
`b i` map `A` into `W i`, then the combined motion carries every `a i` to `b i` on `A`, and fixes
every point outside a compact subset of the union of the `W i`
(`TauCeti.exists_diffeotopy_final_comp_eqOn_of_pairwise_disjoint`). The combined motion is the
composite of the given ones.

This lets independent local motions, for instance of the labels of a configuration, be performed
simultaneously.
-/

public section

noncomputable section

open Set Function
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {ι X : Type*}

/-- Motions of finitely many labels with supports in pairwise disjoint sets `W i`, each matching
`a i` with `b i` on `A`, combine into one motion matching every label, provided `a i` and `b i`
map `A` into `W i`. The combined motion fixes every point outside a compact subset of the union
of the `W i`. -/
theorem exists_diffeotopy_final_comp_eqOn_of_pairwise_disjoint (s : Finset ι) {W : ι → Set M}
    (hW : Pairwise (Disjoint on W)) {a b : ι → X → M} {A : Set X}
    (ha : ∀ i, MapsTo (a i) A (W i)) (hb : ∀ i, MapsTo (b i) A (W i))
    (h : ∀ i, ∃ Φ : Diffeotopy J n M, ∃ K : Set M, IsCompact K ∧ K ⊆ W i ∧
      (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧ EqOn (Φ.final ∘ a i) (b i) A) :
    ∃ Φ : Diffeotopy J n M, ∃ K : Set M, IsCompact K ∧ K ⊆ ⋃ i ∈ s, W i ∧
      (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧ ∀ i ∈ s, EqOn (Φ.final ∘ a i) (b i) A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨Diffeotopy.refl _ _ _, ∅, isCompact_empty, empty_subset _,
      fun t y _ ↦ Diffeotopy.refl_apply _, by simp⟩
  | @insert j s hjs ih =>
    obtain ⟨Φ, K, hK, hKW, hΦK, hΦ⟩ := ih
    obtain ⟨Ψ, L, hL, hLW, hΨL, hΨ⟩ := h j
    -- Points of `W i` for `i ∈ s` lie outside `L ⊆ W j`, and points of `W j` lie outside `K`.
    have hL' (i) (hi : i ∈ s) (y) (hy : y ∈ W i) : y ∉ L := fun hyL ↦
      (hW (ne_of_mem_of_not_mem hi hjs)).ne_of_mem hy (hLW hyL) rfl
    have hK' (y) (hy : y ∈ W j) : y ∉ K := fun hyK ↦ by
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hKW hyK)
      exact (hW (ne_of_mem_of_not_mem hi hjs)).ne_of_mem hyi hy rfl
    refine ⟨Φ.trans Ψ, K ∪ L, hK.union hL, union_subset ?_ ?_, fun t y hy ↦ ?_,
      fun i hi x hx ↦ ?_⟩
    · exact hKW.trans <| iUnion₂_mono' fun i hi ↦ ⟨i, Finset.mem_insert_of_mem hi, subset_rfl⟩
    · exact hLW.trans <| subset_biUnion_of_mem (u := W) (Finset.mem_insert_self j s)
    · rw [mem_union, not_or] at hy
      rw [Diffeotopy.trans_apply, hΦK t y hy.1, hΨL t y hy.2]
    · rw [comp_apply, Diffeotopy.final_trans, Diffeomorph.coe_trans, comp_apply]
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rw [Diffeotopy.final_apply Φ, hΦK 1 _ (hK' _ (ha i hx))]
        exact hΨ hx
      · rw [← comp_apply (f := Φ.final), hΦ i hi hx, Diffeotopy.final_apply]
        exact hΨL 1 _ (hL' i hi _ (hb i hx))

end TauCeti
