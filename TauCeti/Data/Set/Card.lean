/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card

/-!
# Cardinalities of images, of complements, of preimages under division and of sigma fibres

Two maps on a common index type that identify the same pairs of indices take equally many values
on every set of indices (`Set.encard_image_eq_encard_image_of_eq_iff`): the second map factors
through the first by a map that is injective on its values.

For `n > 0`, every natural number `j` is the quotient `i / n` of exactly the `n` natural numbers
`n * j, …, n * j + n - 1`. Hence for `n > 0` the preimage of a finite set `S ⊆ ℕ` under
`i ↦ i / n` has `n` times as many elements as `S`. This is the counting fact behind sequences that
repeat each term `n` times, such as the singular values of a block sum of `n` copies of one map.

Adding a fresh element to a set removes one element from its complement
(`Set.encard_compl_insert_add_one`).

The points of the range of an injective map `φ` into a sigma type that lie in the fibre over `i`
are counted by the arguments that `φ` maps into that fibre (`Set.ncard_preimage_sigmaMk_range`).

The statement `Set.ncard_preimage_div` needs no hypotheses: `Set.ncard` is `0` on infinite sets,
and `i / 0 = 0` makes the preimage under division by zero either `∅` or all of `ℕ`, so both
sides are `0` when `S` is infinite or `n = 0`.
-/

public section

namespace Set

/-- Two maps that identify the same pairs of indices take equally many values on every set of
indices. -/
theorem encard_image_eq_encard_image_of_eq_iff {ι α β : Type*} {f : ι → α} {g : ι → β}
    (h : ∀ i j, f i = f j ↔ g i = g j) (I : Set ι) : (f '' I).encard = (g '' I).encard := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp [Set.eq_empty_of_isEmpty I]
  -- `g` factors through `f` by a map that is injective on the values of `f`.
  have hfg : g.FactorsThrough f := fun i j hij => (h i j).mp hij
  have hφ : g = Function.extend f g (fun _ => g i₀) ∘ f :=
    funext fun i => (hfg.extend_apply _ i).symm
  rw [hφ, Set.image_comp]
  refine (Set.InjOn.encard_image ?_).symm
  rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩ hij
  rw [hfg.extend_apply, hfg.extend_apply] at hij
  exact (h i j).mpr hij

/-- Adding a fresh element to a set removes one element from its complement. -/
theorem encard_compl_insert_add_one {α : Type*} {s : Set α} {x : α} (hx : x ∉ s) :
    (insert x s)ᶜ.encard + 1 = sᶜ.encard := by
  rw [← encard_sdiff_singleton_add_one (mem_compl hx), insert_eq, compl_union, sdiff_eq,
    inter_comm]

/-- The points of the range of an injective map into a sigma type lying over the index `i` are
counted by the arguments mapped over `i`. -/
theorem ncard_preimage_sigmaMk_range {κ α : Type*} {Y : κ → Type*}
    {φ : α → Σ i, Y i} (hφ : Function.Injective φ) (i : κ) :
    (Sigma.mk i ⁻¹' range φ).ncard = {a | (φ a).1 = i}.ncard := by
  have himage : range φ ∩ range (Sigma.mk i) = φ '' {a | (φ a).1 = i} := by
    rw [range_sigmaMk]
    ext z
    constructor
    · rintro ⟨⟨a, rfl⟩, hi⟩
      exact ⟨a, hi, rfl⟩
    · rintro ⟨a, hi, rfl⟩
      exact ⟨⟨a, rfl⟩, hi⟩
  rw [← preimage_inter_range, ncard_preimage_of_injective_subset_range sigma_mk_injective
    inter_subset_right, himage, ncard_image_of_injective _ hφ]

/-- The preimage of a set `S ⊆ ℕ` under `i ↦ i / n` has `n` times as many elements as `S`. Both
sides are `0` when `S` is infinite or `n = 0`. -/
theorem ncard_preimage_div (S : Set ℕ) (n : ℕ) : ((· / n) ⁻¹' S).ncard = S.ncard * n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · -- Division by zero is constantly zero, so the preimage is `∅` or all of `ℕ`.
    by_cases h0 : 0 ∈ S
    · simp [Set.preimage, Nat.div_zero, h0]
    · simp [Set.preimage, Nat.div_zero, h0]
  have h : (· / n) ⁻¹' S = (fun p : ℕ × Fin n ↦ n * p.1 + p.2) '' (S ×ˢ univ) := by
    ext i
    simp only [mem_preimage, mem_image, mem_prod, mem_univ, and_true, Prod.exists]
    refine ⟨fun hi ↦ ⟨i / n, ⟨i % n, Nat.mod_lt _ hn⟩, hi, Nat.div_add_mod i n⟩, ?_⟩
    rintro ⟨j, b, hj, rfl⟩
    rwa [Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt, add_zero]
  rw [h, ncard_image_of_injective _ fun p q hpq ↦ ?_, ncard_prod, ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  have hp := p.2.isLt
  have hq := q.2.isLt
  have h₁ : p.1 = q.1 := by
    simpa [Nat.mul_add_div hn, Nat.div_eq_of_lt hp, Nat.div_eq_of_lt hq] using
      congrArg (· / n) hpq
  exact Prod.ext h₁ (Fin.ext (by simpa [h₁] using hpq))

end Set
