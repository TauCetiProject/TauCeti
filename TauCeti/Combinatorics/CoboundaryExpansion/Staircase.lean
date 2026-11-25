/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.GroupTheory.Perm.MovedNorm
import TauCeti.Combinatorics.CoboundaryExpansion.GraphCochain
import TauCeti.Combinatorics.CoboundaryExpansion.StarBound
import TauCeti.Combinatorics.SimpleGraph.Staircase
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Positivity

/-!
# Kozlov's staircase graphs and the binary coboundary constant

Kozlov's staircase graph `SimpleGraph.staircase q t` on `q (2 t + 1)` vertices is cut-minimal
(`SimpleGraph.isCutMinimal_staircase`) and satisfies
`#oddTriangleFinset = q (2 t + 1) / 3 * #edgeFinset`
(`SimpleGraph.card_oddTriangleFinset_staircase`). Its cochain, a transposition on the
edges and `1` elsewhere, therefore has ratio `q (2 t + 1) / 3`
(`SimpleGraph.h1_complete_movedNorm_le_of_isCutMinimal`), which gives

* `h1_complete_movedNorm_le_of_card_eq_mul`: `h1 (complete V) (movedNorm α) ≤ card V / 3`
  whenever `card V = q (2 t + 1)` with `t ≥ 1`, for every finite type `α`.

With `α = Fin 3` it covers the vertex counts that are not multiples of four in the `Sym(3)`
theorem. With `α = Fin 2`, together with the star bound, it gives Kozlov's theorem:

* `h1_complete_movedNorm_fin_two`: the binary coboundary constant
  `h1 (complete V) (movedNorm (Fin 2))` is `card V / 3` whenever `card V` is not a power of two.

Every such `card V` other than `0` is `q (2 t + 1)` with `q, t ≥ 1`, through an odd prime factor.
Nothing is asserted at powers of two, which are never of the form `q (2 t + 1)` with `t ≥ 1`.

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136,
  Definition 3.2 and §3.1 (staircase graphs), Lemma 3.8 and Corollary 3.13 (cut-minimality),
  Lemma 3.10 (triangle count), Theorem 4.2.
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792,
  Corollary 7 and Theorem 8 (the `Sym(3)` transfer).
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: this file adapts the staircase witness of `CoboundaryK3/Staircase.lean`, with
  the counting replaced by `SimpleGraph.staircase`.
-/

public section

namespace TauCeti

open Finset Equiv TwoComplex

variable {V α : Type*} [Fintype V] [LinearOrder V] [Fintype α] [DecidableEq α]

/-- **The staircase upper bound.** If `card V = q (2 t + 1)` with `t ≥ 1`, then
`h1 (complete V) (movedNorm α) ≤ card V / 3`, witnessed by Kozlov's staircase graph
`SimpleGraph.staircase q t`. -/
theorem h1_complete_movedNorm_le_of_card_eq_mul {q t : ℕ} (ht : 0 < t)
    (hV : Fintype.card V = q * (2 * t + 1)) :
    h1 (complete V) (Perm.movedNorm α) ≤ (Fintype.card V : ℝ) / 3 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · -- Without vertices every cochain is a coboundary and the constant is `0`.
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp (by simpa using hV)
    rw [h1_eq_zero_of_forall_gaugeDist_eq_zero fun c => le_antisymm
      ((c.gaugeDist_le_cost _ 1).trans_eq (by simp [Cochain.cost_complete])) (c.gaugeDist_nonneg _)]
    positivity
  let W := Fin (q * t) ⊕ Fin (q * t) ⊕ Fin q
  let _ : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  have hW : Fintype.card W = q * (2 * t + 1) := by
    simp only [W, Fintype.card_sum, Fintype.card_fin]
    ring
  rw [h1_complete_eq_of_card_eq Perm.isConjInvariant_movedNorm (hV.trans hW.symm)]
  have hE2 := SimpleGraph.two_mul_card_edgeFinset_staircase q t
  have hE : 0 < #(SimpleGraph.staircase q t).edgeFinset := by
    have : 0 < q ^ 2 * t * (t + 1) := by positivity
    omega
  refine (SimpleGraph.h1_complete_movedNorm_le_of_isCutMinimal _
    (SimpleGraph.isCutMinimal_staircase q t) hE).trans_eq ?_
  have hE' : (#(SimpleGraph.staircase q t).edgeFinset : ℝ) ≠ 0 := by positivity
  rw [SimpleGraph.card_oddTriangleFinset_staircase, mul_div_cancel_right₀ _ hE', hV]
  push_cast
  ring

/-- **Kozlov's theorem.** The binary coboundary constant `h1 (complete V) (movedNorm (Fin 2))` of
the complete complex is `card V / 3` whenever `card V` is not a power of two. -/
theorem h1_complete_movedNorm_fin_two (hpow : ¬ ∃ a : ℕ, Fintype.card V = 2 ^ a) :
    h1 (complete V) (Perm.movedNorm (Fin 2)) = (Fintype.card V : ℝ) / 3 := by
  obtain ⟨_, hp, ⟨q, hq⟩, t, rfl⟩ :=
    (Fintype.card V).eq_two_pow_or_exists_odd_prime_and_dvd.resolve_left hpow
  have ht : 0 < t := by have := hp.one_lt; omega
  refine le_antisymm (h1_complete_movedNorm_le_of_card_eq_mul (q := q) ht (by rw [hq]; ring)) ?_
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · rw [hq, mul_zero, Nat.cast_zero, zero_div]
    exact h1_nonneg _ _
  · have hV : 3 ≤ Fintype.card V := hq ▸ (show 3 ≤ 2 * t + 1 by omega).trans
      (Nat.le_mul_of_pos_right _ hq0)
    exact card_div_three_le_h1_of_nontrivial hV _ Perm.isConjInvariant_movedNorm

end TauCeti
