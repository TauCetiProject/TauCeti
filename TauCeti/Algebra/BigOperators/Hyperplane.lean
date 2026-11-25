/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Sums over the parallel hyperplanes of a finite field

Let `F` be a finite field with `q` elements and `a : ι → F`. The level sets of the linear form
`u ↦ ∑ᵢ aᵢ uᵢ` on `F ^ ι` are `q` parallel hyperplanes. If `aⱼ ≠ 0`, translation of the `j`-th
coordinate permutes them transitively, so a function invariant under that translation has the same
sum over each of them, and its sum over all of `F ^ ι` is `q` times its sum over any one of them.

## Main results

* `TauCeti.card_smul_sum_filter_sum_mul_eq`: if `aⱼ ≠ 0` and `g` is invariant under translation of
  the `j`-th coordinate, then `q • ∑_{∑ᵢ aᵢ uᵢ = b} g(u) = ∑_u g(u)`.
-/

public section

open Finset

namespace TauCeti

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]

/-- If `aⱼ ≠ 0` and `g` is invariant under translation of the `j`-th coordinate, then summing `g`
over all tuples is summing it over the `q` parallel hyperplanes `∑ᵢ aᵢ uᵢ = c`, on each of which
it has the same sum. -/
theorem card_smul_sum_filter_sum_mul_eq {M : Type*} [AddCommMonoid M] {a : ι → F} {j : ι}
    (hj : a j ≠ 0) {g : (ι → F) → M} (hg : ∀ u c, g (u + Pi.single j c) = g u) (b : F) :
    Fintype.card F • ∑ u : ι → F with ∑ i, a i * u i = b, g u = ∑ u, g u := by
  have key : ∀ c, ∑ u : ι → F with ∑ i, a i * u i = c, g u =
      ∑ u : ι → F with ∑ i, a i * u i = b, g u := by
    intro c
    rw [sum_filter, sum_filter, ← Equiv.sum_comp (Equiv.addRight (Pi.single j ((c - b) / a j)))]
    refine sum_congr rfl fun u _ ↦ ?_
    have hsum : ∑ i, a i * (u i + Pi.single (M := fun _ ↦ F) j ((c - b) / a j) i) =
        ∑ i, a i * u i + (c - b) := by
      simp [mul_add, sum_add_distrib, Pi.single_apply, mul_div_cancel₀ _ hj]
    have hiff : ∑ i, a i * u i + (c - b) = c ↔ ∑ i, a i * u i = b := by
      constructor <;> intro h <;> linear_combination h
    simp only [Equiv.coe_addRight, Pi.add_apply, hsum, hg, hiff]
  rw [← sum_fiberwise univ (fun u : ι → F ↦ ∑ i, a i * u i) g]
  simp [key, card_univ]

end TauCeti
