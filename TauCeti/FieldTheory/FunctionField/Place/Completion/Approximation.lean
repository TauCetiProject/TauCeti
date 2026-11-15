/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Approximation
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic

/-!
# Weak approximation in the completions

Given finitely many distinct places `P i` of `F / k`, completed functions `x i ∈ F̂_{P i}` and
prescribed orders `b i`, a single function `y ∈ F` agrees with every `x i` to order `b i` at
`P i`. Each `x i` is first approximated by a function of `F` (density of `F` in `F̂_{P i}`,
`TauCeti.Place.exists_sub_completionEmbedding_mem_filtration`), and these functions are then
approximated simultaneously by weak approximation in `F` (`TauCeti.Place.exists_forall_ord_sub_eq`).

## Main results

* `TauCeti.Place.exists_forall_sub_completionEmbedding_mem_filtration`: weak approximation in
  the completions at finitely many distinct places.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.3.1.
-/

public section

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **Weak approximation in the completions.** Given finitely many distinct places `P i`,
completed functions `x i` at them and prescribed orders `b i`, a single function `y` of `F`
agrees with every `x i` to order `b i` at `P i`. -/
theorem exists_forall_sub_completionEmbedding_mem_filtration {ι : Type*} [Finite ι]
    {P : ι → Place k F} (hP : Function.Injective P) (x : ∀ i, (P i).Completion) (b : ι → ℤ) :
    ∃ y : F, ∀ i, x i - (P i).completionEmbedding y ∈ (P i).completionPlace.filtration (b i) := by
  choose z hz using fun i ↦ (P i).exists_sub_completionEmbedding_mem_filtration (x i) (b i)
  obtain ⟨y, hy⟩ := exists_forall_ord_sub_eq hP z b
  refine ⟨y, fun i ↦ ?_⟩
  have h : (P i).completionEmbedding (y - z i) ∈ (P i).completionPlace.filtration (b i) :=
    (P i).completionEmbedding_mem_filtration_iff.mpr (hy i ▸ (P i).mem_filtration_ord (y - z i))
  have := sub_mem (hz i) h
  rwa [map_sub, sub_sub_sub_cancel_right] at this

end TauCeti.Place
