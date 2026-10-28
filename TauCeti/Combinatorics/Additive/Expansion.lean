/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Expansion of finite sets under a finite set of acting elements

Let a monoid `α` act on a type `β`, and let `D ⊆ α` be finite. We say that `D` expands finite
sets by a factor `c` if

```text
c · |F| ≤ |D • F|        for every finite F ⊆ β.
```

This file proves two consequences of such an expansion bound.

* Expansion iterates: if `D` expands by `c ≥ 0`, then the pointwise power `D ^ n` expands by
  `c ^ n`.
* Expansion by a natural number `k` gives, by Hall's marriage theorem for an infinite index type
  with finite neighbour sets, an injection `j : β × Fin k → β` moving each point by an element
  of `D`: `j (x, i) = d • x` for some `d ∈ D`. Each point of `β` is thus sent to `k` distinct
  points, in a way that is injective overall.

For a group without Følner sets these give the finite set and the injection used to construct a
paradoxical decomposition, the hard direction of Tarski's alternative.

## Main results

* `Finset.pow_mul_card_le_card_pow_smul`: if `c · |F| ≤ |D • F|` for all finite `F` and `c ≥ 0`,
  then `c ^ n · |F| ≤ |D ^ n • F|`.
* `Finset.exists_injective_of_mul_card_le_card_smul`: if `k · |F| ≤ |D • F|` for all finite `F`,
  there is an injective `j : β × Fin k → β` with `j (x, i) = d • x` for some `d ∈ D`.

## References

* T. Ceccherini-Silberstein, R. Grigorchuk, P. de la Harpe, *Amenability and paradoxical
  decompositions for pseudogroups and for discrete metric spaces*, Theorem 35.
* A. Garrido, *An introduction to amenable groups*, proof of Theorem 1.11.
-/

public section

open Function
open scoped Pointwise

namespace Finset

variable {α β : Type*}

/-- **Iterated expansion.** If a finite set `D` of a monoid expands every finite set by a factor
`c ≥ 0`, then its `n`-th pointwise power expands every finite set by the factor `c ^ n`. -/
theorem pow_mul_card_le_card_pow_smul [Monoid α] [MulAction α β] [DecidableEq α] [DecidableEq β]
    {D : Finset α} {c : ℝ} (hc : 0 ≤ c) (h : ∀ F : Finset β, c * #F ≤ #(D • F)) (n : ℕ)
    (F : Finset β) : c ^ n * #F ≤ #(D ^ n • F) := by
  induction n generalizing F with
  | zero => simp
  | succ n ih =>
    -- `D ^ (n + 1) • F = D • (D ^ n • F)`, and each factor of `D` contributes a factor `c`.
    rw [pow_succ' c, pow_succ' D, mul_smul, mul_assoc]
    exact (mul_le_mul_of_nonneg_left (ih F) hc).trans (h _)

/-- **Hall's theorem for expanding sets.** If a finite set `D` acting on `β` satisfies
`k · |F| ≤ |D • F|` for every finite `F ⊆ β`, then there is an injective map
`j : β × Fin k → β` moving each point by an element of `D`: `j (x, i) = d • x` for some `d ∈ D`.

This applies Hall's marriage theorem to the neighbour sets `D • {x}` indexed by `β × Fin k`. -/
theorem exists_injective_of_mul_card_le_card_smul [SMul α β] [DecidableEq β] {D : Finset α}
    {k : ℕ} (h : ∀ F : Finset β, k * #F ≤ #(D • F)) :
    ∃ j : β × Fin k → β, Injective j ∧ ∀ p, ∃ d ∈ D, d • p.1 = j p := by
  classical
  obtain ⟨j, hj, hjD⟩ := (all_card_le_biUnion_card_iff_exists_injective
    fun p : β × Fin k ↦ D.image (· • p.1)).1 fun s ↦ by
      -- A finite set `s` of indices lies over its projection `F` to `β`, so `|s| ≤ k · |F|`,
      -- while its neighbours cover `D • F`.
      set F := s.image Prod.fst
      have hsF : #s ≤ k * #F := by
        calc #s ≤ #(F ×ˢ (univ : Finset (Fin k))) :=
              card_le_card fun p hp ↦ mem_product.2 ⟨mem_image_of_mem _ hp, mem_univ _⟩
          _ = k * #F := by rw [card_product, card_univ, Fintype.card_fin, mul_comm]
      have hDF : D • F ⊆ s.biUnion fun p ↦ D.image (· • p.1) := by
        intro x hx
        obtain ⟨d, hd, y, hy, rfl⟩ := mem_smul.1 hx
        obtain ⟨p, hp, rfl⟩ := mem_image.1 hy
        exact mem_biUnion.2 ⟨p, hp, mem_image_of_mem _ hd⟩
      exact hsF.trans ((h F).trans (card_le_card hDF))
  exact ⟨j, hj, fun p ↦ mem_image.1 (hjD p)⟩

end Finset
