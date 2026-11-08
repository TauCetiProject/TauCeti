/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.Basic

/-!
# Pulling back noncrossing partitions along monotone maps

Let `f : α → β` be a map between linear orders that is monotone on a finite set `s` of positions.
Its fibres cut `s` into consecutive intervals, and they form the partition `σ_f` of `s` into the
fibres of `f`. Pulling back a partition of the image `f '' s` along `f`
(`Finpartition.comap`) preserves and reflects noncrossingness, so it is an order embedding
`NC(f '' s) ↪o NC(s)`, and its image is the upper interval `[σ_f, 1_s]` of `NC(s)`.

For `s = Finset.univ : Finset (Fin n)` and a monotone surjection `f : Fin n → Fin m`, the partition
`σ_f` is the interval partition grouping the positions `1, …, n` into `m` consecutive blocks, and
the embedding is the lift `NC(m) ↪o NC(n)` of noncrossing partitions of the blocks. This is the
combinatorial input of the formula for free cumulants whose arguments are products of consecutive
letters.

## Main definitions

* `TauCeti.NoncrossingPartition.comap hf` — the order embedding `NC(f '' s) ↪o NC(s)` given by
  pulling back along a map `f` that is monotone on `s`.

## Main results

* `Finpartition.isNoncrossing_comap_iff` — the pullback of a partition of `f '' s` along a map
  that is monotone on `s` is noncrossing exactly when the partition is.
* `TauCeti.NoncrossingPartition.exists_comap_eq_iff` — a noncrossing partition of `s` is a
  pullback exactly when it is coarser than the partition `σ_f` of `s` into the fibres of `f`.
* `TauCeti.NoncrossingPartition.mem_part_union_part_of_sup_comap_bot_eq_top` — if `f` identifies
  only two adjacent positions `i ≤ j` of `s` and `π ⊔ σ_f = 1`, then `s` is the union of the parts
  of `π` through `i` and `j`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 9 and
  Notation 11.9.
-/

public section

open Finset

namespace Finpartition

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {s : Finset α} {f : α → β}
  {P : Finpartition (s.image f)}

/-- The pullback of a partition of `f '' s` along a map `f` that is monotone on `s` is noncrossing
exactly when the partition is. -/
theorem isNoncrossing_comap_iff (hf : MonotoneOn f s) :
    (P.comap f).IsNoncrossing ↔ P.IsNoncrossing := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- Points `y₁ < y₂ < y₃ < y₄` of `f '' s` have preimages `x₁ < x₂ < x₃ < x₄` in `s`.
    rw [isNoncrossing_iff]
    intro C hC D hD _ hy₁ _ hy₂ _ hy₃ _ hy₄ h₁₂ h₂₃ h₃₄
    obtain ⟨x₁, hx₁, rfl⟩ := mem_image.1 (P.le hC hy₁)
    obtain ⟨x₂, hx₂, rfl⟩ := mem_image.1 (P.le hD hy₂)
    obtain ⟨x₃, hx₃, rfl⟩ := mem_image.1 (P.le hC hy₃)
    obtain ⟨x₄, hx₄, rfl⟩ := mem_image.1 (P.le hD hy₄)
    rw [isNoncrossing_iff, parts_comap] at h
    have := h _ (mem_image_of_mem _ hC) _ (mem_image_of_mem _ hD) x₁ (mem_filter.2 ⟨hx₁, hy₁⟩) x₂
      (mem_filter.2 ⟨hx₂, hy₂⟩) x₃ (mem_filter.2 ⟨hx₃, hy₃⟩) x₄ (mem_filter.2 ⟨hx₄, hy₄⟩)
      (hf.reflect_lt hx₁ hx₂ h₁₂) (hf.reflect_lt hx₂ hx₃ h₂₃) (hf.reflect_lt hx₃ hx₄ h₃₄)
    have hx₁D : x₁ ∈ {x ∈ s | f x ∈ D} := this ▸ mem_filter.2 ⟨hx₁, hy₁⟩
    exact P.eq_of_mem_parts hC hD hy₁ (mem_filter.1 hx₁D).2
  · -- Points `x₁ < x₂ < x₃ < x₄` of `s` have images `f x₁ ≤ f x₂ ≤ f x₃ ≤ f x₄`; two equal
    -- consecutive images already lie in both parts.
    rw [isNoncrossing_iff, parts_comap]
    intro X hX Y hY x₁ hx₁ x₂ hx₂ x₃ hx₃ x₄ hx₄ h₁₂ h₂₃ h₃₄
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hX
    obtain ⟨D, hD, rfl⟩ := mem_image.1 hY
    rw [mem_filter] at hx₁ hx₂ hx₃ hx₄
    suffices C = D by rw [this]
    rcases (hf hx₁.1 hx₂.1 h₁₂.le).lt_or_eq with h₁₂' | h₁₂'
    · rcases (hf hx₂.1 hx₃.1 h₂₃.le).lt_or_eq with h₂₃' | h₂₃'
      · rcases (hf hx₃.1 hx₄.1 h₃₄.le).lt_or_eq with h₃₄' | h₃₄'
        · exact isNoncrossing_iff.1 h C hC D hD _ hx₁.2 _ hx₂.2 _ hx₃.2 _ hx₄.2 h₁₂' h₂₃' h₃₄'
        · exact P.eq_of_mem_parts hC hD hx₃.2 (h₃₄' ▸ hx₄.2)
      · exact P.eq_of_mem_parts hC hD (h₂₃' ▸ hx₃.2) hx₂.2
    · exact P.eq_of_mem_parts hC hD (h₁₂' ▸ hx₁.2) hx₂.2

/-- The pullback of a noncrossing partition of `f '' s` along a map `f` that is monotone on `s` is
noncrossing. -/
theorem IsNoncrossing.comap (hf : MonotoneOn f s) (hP : P.IsNoncrossing) :
    (P.comap f).IsNoncrossing :=
  (isNoncrossing_comap_iff hf).2 hP

end Finpartition

namespace TauCeti.NoncrossingPartition

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {s : Finset α} {f : α → β}

/-- Pulling back along a map `f` that is monotone on `s` embeds the noncrossing partitions of the
image `f '' s` into the noncrossing partitions of `s`, as the partitions coarser than the
partition of `s` into the fibres of `f` (`TauCeti.NoncrossingPartition.exists_comap_eq_iff`). -/
def comap (hf : MonotoneOn f s) : NoncrossingPartition (s.image f) ↪o NoncrossingPartition s :=
  OrderEmbedding.ofMapLEIff (fun ρ => ⟨ρ.1.comap f, ρ.2.comap hf⟩) fun _ _ =>
    Finpartition.comap_le_comap_iff

@[simp, norm_cast]
theorem coe_comap (hf : MonotoneOn f s) (ρ : NoncrossingPartition (s.image f)) :
    (comap hf ρ : Finpartition s) = (ρ : Finpartition (s.image f)).comap f :=
  (rfl)

@[simp]
theorem comap_top (hf : MonotoneOn f s) : comap hf ⊤ = ⊤ :=
  Subtype.ext Finpartition.comap_top

/-- A noncrossing partition of `s` is the pullback of a noncrossing partition of `f '' s` along a
map `f` that is monotone on `s` exactly when it is coarser than the partition of `s` into the
fibres of `f`. -/
theorem exists_comap_eq_iff {hf : MonotoneOn f s} {π : NoncrossingPartition s} :
    (∃ ρ, comap hf ρ = π) ↔ comap hf ⊥ ≤ π := by
  refine ⟨fun ⟨ρ, hρ⟩ => hρ ▸ (comap hf).monotone bot_le, fun h => ?_⟩
  have h' : (comap hf ⊥ : Finpartition s) ≤ π := Subtype.coe_le_coe.2 h
  rw [coe_comap, coe_bot] at h'
  obtain ⟨P, hP⟩ := Finpartition.exists_comap_eq_iff.2 h'
  exact ⟨⟨P, (Finpartition.isNoncrossing_comap_iff hf).1 (hP ▸ π.2)⟩, Subtype.ext hP⟩

/-- Let `f` be monotone on `s` and identify no two positions other than `i ≤ j`, which are adjacent
in `s`. If the join in `NC(s)` of `π` with the partition `σ_f` into the fibres of `f` is `1`, then
`s` is the union of the parts of `π` through `i` and `j`: merging these two parts gives a
noncrossing partition above `π` and `σ_f`. -/
theorem mem_part_union_part_of_sup_comap_bot_eq_top (hf : MonotoneOn f s) {i j : α}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≤ j) (hadj : ∀ z ∈ s, z ≤ i ∨ j ≤ z)
    (hfeq : ∀ {u v}, u ∈ s → v ∈ s → f u = f v → u ≠ v → (u = i ∨ u = j) ∧ (v = i ∨ v = j))
    {π : NoncrossingPartition s} (hπ : π ⊔ comap hf ⊥ = ⊤) {z : α}
    (hz : z ∈ s) :
    z ∈ π.1.part i ∪ π.1.part j := by
  have hpair : {i, j} ⊆ s := fun u hu => by
    rcases mem_insert.1 hu with rfl | hu
    exacts [hi, (mem_singleton.1 hu) ▸ hj]
  have hji : (Finpartition.pairPartition s i j hpair).part j =
      (Finpartition.pairPartition s i j hpair).part i :=
    ((Finpartition.pairPartition s i j hpair).mem_part_iff_part_eq_part hj hi).1 (by
      rw [Finpartition.part_pairPartition]; exact mem_insert_of_mem (mem_singleton_self j))
  -- The fibres of `f` lie in the parts of `pairPartition s i j`.
  have hσ : comap hf ⊥ ≤ (⟨Finpartition.pairPartition s i j hpair,
      Finpartition.isNoncrossing_pairPartition hpair⟩ : NoncrossingPartition s) := by
    refine Finpartition.le_iff_forall_part_subset.2 fun x w hw => ?_
    by_cases hxs : x ∈ s
    swap
    · rw [Finpartition.part_eq_empty _ |>.2 hxs] at hw
      exact absurd hw (notMem_empty _)
    rw [coe_comap, coe_bot, Finpartition.part_comap_bot hxs] at hw
    obtain ⟨hws, hwx⟩ := mem_filter.1 hw
    rcases eq_or_ne w x with rfl | hne
    · exact Finpartition.mem_part_self _ |>.2 hws
    obtain ⟨hw', hx'⟩ := hfeq hws hxs hwx hne
    have hmem : ∀ {u}, u = i ∨ u = j →
        u ∈ (Finpartition.pairPartition s i j hpair).part i := by
      rintro u (rfl | rfl)
      · rw [Finpartition.part_pairPartition]; exact mem_insert_self _ _
      · rw [Finpartition.part_pairPartition]; exact mem_insert_of_mem (mem_singleton_self _)
    have hxi : (Finpartition.pairPartition s i j hpair).part x =
        (Finpartition.pairPartition s i j hpair).part i := by
      rcases hx' with rfl | rfl
      · rfl
      · exact hji
    rw [hxi]
    exact hmem hw'
  have htop := top_le_iff.1 (hπ ▸ sup_le_sup_left hσ π)
  have hu := (sup_pairPartition_eq_top_iff hpair hij hadj π).1 htop
  rw [hu]
  exact hz

end TauCeti.NoncrossingPartition
