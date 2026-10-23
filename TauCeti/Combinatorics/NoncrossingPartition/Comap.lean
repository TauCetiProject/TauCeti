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
    have hlt {x y : α} (hx : x ∈ s) (hy : y ∈ s) (hxy : f x < f y) : x < y :=
      lt_of_not_ge fun h => hxy.not_ge (hf hy hx h)
    rw [isNoncrossing_iff, parts_comap] at h
    have := h _ (mem_image_of_mem _ hC) _ (mem_image_of_mem _ hD) x₁ (mem_filter.2 ⟨hx₁, hy₁⟩) x₂
      (mem_filter.2 ⟨hx₂, hy₂⟩) x₃ (mem_filter.2 ⟨hx₃, hy₃⟩) x₄ (mem_filter.2 ⟨hx₄, hy₄⟩)
      (hlt hx₁ hx₂ h₁₂) (hlt hx₂ hx₃ h₂₃) (hlt hx₃ hx₄ h₃₄)
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
  obtain ⟨P, hP⟩ := Finpartition.exists_comap_eq_iff.2 (show _ ≤ π.1 from h)
  exact ⟨⟨P, (Finpartition.isNoncrossing_comap_iff hf).1 (hP ▸ π.2)⟩, Subtype.ext hP⟩

end TauCeti.NoncrossingPartition
