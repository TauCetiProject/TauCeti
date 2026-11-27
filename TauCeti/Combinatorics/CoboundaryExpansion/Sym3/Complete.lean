/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.CoboundaryExpansion.Replication
import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.MovedNorm
import TauCeti.Combinatorics.CoboundaryExpansion.Staircase
import TauCeti.Combinatorics.CoboundaryExpansion.StarBound
import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Basic
import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.CheegerConstant
import TauCeti.GroupTheory.Perm.FinThree.Basic
import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The `Sym(3)` coboundary constant of the complete complex is `k/3`

For every finite linearly ordered `V` with `3 ≤ Fintype.card V`:

* `h1_complete_movedNorm_fin_three`: `h1 (complete V) (movedNorm (Fin 3)) = card V / 3`;
* `h1Norm_complete_movedNorm_fin_three`: in the normalized convention the value is
  `card V / (card V - 2)`;
* `h1_complete_fin_four`: the seed value `h1 (complete (Fin 4)) (movedNorm (Fin 3)) = 4 / 3`;
* `h1Sym_complete`: the infimum `h1Sym (complete V)` of the constants over all permutation degrees
  `n ≥ 2` is also `card V / 3`, since degree `3` attains the star bound.

Beasley, Corollary 7, is the replicated-seed witness for `k = 4 q`: the seed of
Proposition 5 has defect `8 q ^ 3` and gauge distance `6 q ^ 2`, so the ratio is `k / 3`.
That is `defect_replicatedSeed`, `gaugeDist_replicatedSeed` and
`defect_div_gaugeDist_replicatedSeedOfCardEq`.
Beasley, Theorem 8 (the moved-point count, k/3 for every k ≥ 4) is
`h1_complete_movedNorm_fin_three` for `4 ≤ card V`; the Lean theorem also covers
`card V = 3`.

The lower bound is the star bound `card_div_three_le_h1_of_nontrivial`.
For the upper bound, every `k ≥ 3` is `4 q` or `(2 t + 1) q` with `t, q ≥ 1`.

* `k = (2 t + 1) q`: Kozlov's staircase graph `SimpleGraph.staircase q t`
  (`h1_complete_movedNorm_le_of_card_eq_mul`).
* `k = 4 q`: the `k = 4` seed `Sym3.seed`, with the three transpositions on the pairs `(1, 2)`,
  `(1, 3)`, `(2, 3)`, replicated on `Fin 4 ×ₗ Fin q`. Its defect is `8 q ^ 3`
  and its gauge distance is `6 q ^ 2` by `Cochain.gaugeDist_replicate`, giving the required
  quotient `4 q / 3`.
  `Sym3.replicatedSeed q = (Cochain.ofLt (complete (Fin 4)) seed).replicate (Fin q)` has defect
  `8 q ^ 3` and gauge distance `6 q ^ 2` (`defect_replicatedSeed`, `gaugeDist_replicatedSeed`,
  from `defect_ofLt_seed` and `gaugeDist_ofLt_seed`), the identity gauge costs `6 q ^ 2`
  (`cost_replicatedSeed_one`), and `Sym3.replicatedSeedOfCardEq` carries it to any `V` with
  `card V = 4 q`, where its ratio is `card V / 3`
  (`Sym3.defect_div_gaugeDist_replicatedSeedOfCardEq`).

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792,
  Proposition 5, Corollary 7 and Theorem 8.
* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136,
  Definition 3.2 (staircase graphs), Lemma 3.8 and Corollary 3.13 (cut-minimality).
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: the `k = 4` seed `Sym3.seed` comes from `CoboundaryK3/Basic.lean`, and the
  assembly of the seeds follows `CoboundaryK3/Constant.lean` and `CoboundaryK3/Staircase.lean`.
-/

public section

namespace TauCeti

open Finset Equiv Equiv.Perm TwoComplex

namespace Sym3

/-- The `k = 4` seed of Proposition 5: `swap 1 2`, `swap 0 1`, `swap 0 2` on the ordered pairs
`(1, 2)`, `(1, 3)`, `(2, 3)` and `1` on all other ordered pairs; it is read on `u < v` (via
`Cochain.ofLt`). -/
def seed (u v : Fin 4) : Perm (Fin 3) :=
  if u = 1 ∧ v = 2 then swap 1 2 else if u = 1 ∧ v = 3 then swap 0 1
  else if u = 2 ∧ v = 3 then swap 0 2 else 1

/-- The values of the seed: `swap 1 2`, `swap 0 1`, `swap 0 2` on `(1, 2)`, `(1, 3)`, `(2, 3)`
and `1` elsewhere. -/
theorem seed_def (u v : Fin 4) :
    seed u v = if u = 1 ∧ v = 2 then swap 1 2 else if u = 1 ∧ v = 3 then swap 0 1
      else if u = 2 ∧ v = 3 then swap 0 2 else 1 :=
  (rfl)

/-- The seed is `1` on the three edges at the vertex `0`. -/
theorem seed_zero_of_pos : ∀ v : Fin 4, 0 < v → seed 0 v = 1 := by decide

/-- The seed carries the three transpositions of `Perm (Fin 3)` on the edges `(1, 2)`, `(1, 3)`,
`(2, 3)`, one each. -/
theorem insert_seed_eq_setOf_isSwap :
    ({seed 1 2, seed 1 3, seed 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap} := by
  rw [setOf_isSwap_perm_fin_three]
  ext σ
  simp only [seed, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide +revert

/-- The seed has moved-point defect `8`: each of its four triangles has a transposition as
holonomy. -/
theorem defect_ofLt_seed :
    (Cochain.ofLt (complete (Fin 4)) seed).defect (movedNorm (Fin 3)) = 8 := by
  rw [Cochain.defect_ofLt_complete_movedNorm]
  exact_mod_cast
    (by decide +kernel : ∑ p ∈ univ.filter (fun p : Fin 4 × Fin 4 × Fin 4 =>
        p.1 < p.2.1 ∧ p.2.1 < p.2.2),
      (seed p.1 p.2.1 * seed p.2.1 p.2.2 * (seed p.1 p.2.2)⁻¹).support.card = 8)

/-- The identity gauge costs `6` against the seed: its three non-identity edges are
transpositions. -/
theorem cost_ofLt_seed_one :
    (Cochain.ofLt (complete (Fin 4)) seed).cost (movedNorm (Fin 3)) (fun _ => 1) = 6 := by
  rw [Cochain.cost_ofLt_complete_movedNorm]
  simp only [inv_one, one_mul, mul_one]
  exact_mod_cast
    (by decide +kernel : ∑ p ∈ univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2),
      (seed p.1 p.2).support.card = 6)

/-- The seed has gauge distance `6`, attained by the identity gauge. -/
theorem gaugeDist_ofLt_seed :
    (Cochain.ofLt (complete (Fin 4)) seed).gaugeDist (movedNorm (Fin 3)) = 6 := by
  refine le_antisymm (((Cochain.ofLt (complete (Fin 4)) seed).gaugeDist_le_cost _
    (fun _ => 1)).trans cost_ofLt_seed_one.le) ?_
  refine (Cochain.le_gaugeDist_iff _ _).mpr fun β => ?_
  rw [← Cochain.mul_costErr_eq_cost, Cochain.costErr_ofLt_complete]
  have hle := two_le_sum_distErr_fin_four_of_eq_setOf_isSwap seed seed_zero_of_pos
    insert_seed_eq_setOf_isSwap β
  linarith

/-- The replicated seed on `Fin 4 ×ₗ Fin q`: the balanced replication of the cochain of `seed`,
so `seed` between clusters and `1` inside a cluster. -/
noncomputable def replicatedSeed (q : ℕ) :
    Cochain (complete (Fin 4 ×ₗ Fin q)) (Perm (Fin 3)) :=
  (Cochain.ofLt (complete (Fin 4)) seed).replicate (Fin q)

/-- `replicatedSeed q` is the balanced replication of the cochain of `seed`. -/
theorem replicatedSeed_def (q : ℕ) : replicatedSeed q =
    (Cochain.ofLt (complete (Fin 4)) seed).replicate (Fin q) :=
  (rfl)

/-- Replication multiplies the seed defect `8` by `q ^ 3`. -/
theorem defect_replicatedSeed (q : ℕ) :
    (replicatedSeed q).defect (movedNorm (Fin 3)) = 8 * (q : ℝ) ^ 3 := by
  rw [replicatedSeed, Cochain.defect_replicate, defect_ofLt_seed, Fintype.card_fin]
  ring

/-- Replication multiplies the seed gauge distance `6` by `q ^ 2`. -/
theorem gaugeDist_replicatedSeed (q : ℕ) :
    (replicatedSeed q).gaugeDist (movedNorm (Fin 3)) = 6 * (q : ℝ) ^ 2 := by
  rw [replicatedSeed, Cochain.gaugeDist_replicate, gaugeDist_ofLt_seed, Fintype.card_fin]
  ring

/-- The identity gauge costs `6 q ^ 2` against the replicated seed. -/
theorem cost_replicatedSeed_one (q : ℕ) :
    (replicatedSeed q).cost (movedNorm (Fin 3)) (fun _ => 1) = 6 * (q : ℝ) ^ 2 := by
  rw [replicatedSeed]
  have hγ : (fun _ : Fin 4 => (1 : Perm (Fin 3))) ∘
      (fun x : Fin 4 ×ₗ Fin q => (ofLex x).1) = fun _ => 1 := by
    funext _
    simp [Function.comp_apply]
  rw [← hγ, Cochain.cost_replicate_comp, cost_ofLt_seed_one, Fintype.card_fin]
  ring

/-- The upper bound when `card V = 4 q`. -/
private theorem h1_complete_le_of_card_eq_four_mul {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hV : Fintype.card V = 4 * q) :
    h1 (complete V) (movedNorm (Fin 3)) ≤ (Fintype.card V : ℝ) / 3 := by
  rw [h1_complete_eq_of_card_eq isConjInvariant_movedNorm (W := Fin 4 ×ₗ Fin q)
    (by rw [hV, Fintype.card_lex, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin])]
  refine (h1_complete_lex_le_card_mul_div (ι := Fin q) (α := Cochain.ofLt (complete (Fin 4)) seed)
    (by rw [gaugeDist_ofLt_seed]; norm_num)).trans_eq ?_
  rw [defect_ofLt_seed, gaugeDist_ofLt_seed, Fintype.card_fin, hV]
  push_cast
  ring

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The replicated seed carried to any `V` with `Fintype.card V = 4 * q`, by the vertex
relabelling of `h1_complete_eq_of_card_eq`. -/
noncomputable def replicatedSeedOfCardEq {q : ℕ} (hV : Fintype.card V = 4 * q) :
    Cochain (complete V) (Perm (Fin 3)) :=
  (replicatedSeed q).relabelComplete (Fintype.equivOfCardEq <| by
    rw [Fintype.card_lex, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hV])

omit [LinearOrder V] in
/-- `replicatedSeedOfCardEq` is `replicatedSeed q` relabelled along a cardinality bijection. -/
theorem replicatedSeedOfCardEq_def {q : ℕ} (hV : Fintype.card V = 4 * q) :
    replicatedSeedOfCardEq hV =
      (replicatedSeed q).relabelComplete (Fintype.equivOfCardEq <| by
        rw [Fintype.card_lex, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hV]) :=
  (rfl)

end Sym3

/-- The upper bound `h1 (complete V) (movedNorm (Fin 3)) ≤ card V / 3` for `3 ≤ card V`: write
`card V` as `4 q` or `(2 t + 1) q` with `t, q ≥ 1`. -/
private theorem h1_complete_movedNorm_fin_three_le {V : Type*} [Fintype V] [LinearOrder V]
    (hV : 3 ≤ Fintype.card V) :
    h1 (complete V) (movedNorm (Fin 3)) ≤ (Fintype.card V : ℝ) / 3 := by
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (by omega : 2 < Fintype.card V) with
    ⟨q, hq⟩ | ⟨p, hp, ⟨q, hq⟩, t, rfl⟩
  · exact Sym3.h1_complete_le_of_card_eq_four_mul hq
  · have ht : 0 < t := by have := hp.one_lt; omega
    exact h1_complete_movedNorm_le_of_card_eq_mul (q := q) ht (by rw [hq]; ring)

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The `Sym(3)` coboundary constant `h1 (complete V) (movedNorm (Fin 3))` of the complete complex
equals `Fintype.card V / 3` whenever `3 ≤ Fintype.card V` (Beasley, Theorem 8, stated there for
`k ≥ 4`). -/
theorem h1_complete_movedNorm_fin_three (hV : 3 ≤ Fintype.card V) :
    h1 (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / 3 := by
  refine le_antisymm ?_ (card_div_three_le_h1_of_nontrivial hV _ isConjInvariant_movedNorm)
  exact h1_complete_movedNorm_fin_three_le hV

/-- The normalized `Sym(3)` coboundary constant `h1Norm (complete V) (movedNorm (Fin 3))` of the
complete complex equals `k / (k - 2)` for `k = Fintype.card V ≥ 3`. -/
theorem h1Norm_complete_movedNorm_fin_three (hV : 3 ≤ Fintype.card V) :
    h1Norm (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / (Fintype.card V - 2) := by
  have h : (Fintype.card V : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
    linarith
  rw [h1Norm_complete hV, h1_complete_movedNorm_fin_three hV]
  field_simp

/-- The same-degree permutation coboundary constant `h1Sym (complete V)`, the infimum over all
degrees `n ≥ 2` of `h1 (complete V) (movedNorm (Fin n))`, equals `Fintype.card V / 3` whenever
`3 ≤ Fintype.card V`: every degree is bounded below by the star bound, and degree `3` attains
it. -/
theorem h1Sym_complete (hV : 3 ≤ Fintype.card V) :
    h1Sym (complete V) = (Fintype.card V : ℝ) / 3 :=
  le_antisymm ((h1Sym_le_h1_movedNorm _ (by norm_num)).trans_eq
    (h1_complete_movedNorm_fin_three hV)) (card_div_three_le_h1Sym hV)

/-- On the complete complex with four vertices the `Sym(3)` coboundary constant is `4/3`. -/
theorem h1_complete_fin_four : h1 (complete (Fin 4)) (movedNorm (Fin 3)) = 4 / 3 := by
  simpa using h1_complete_movedNorm_fin_three (V := Fin 4) (by simp)

namespace Sym3

/-- `defect / gaugeDist` of the carried seed equals `Fintype.card V / 3`. -/
theorem defect_div_gaugeDist_replicatedSeedOfCardEq {q : ℕ}
    (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).defect (movedNorm (Fin 3)) /
        (replicatedSeedOfCardEq hV).gaugeDist (movedNorm (Fin 3)) =
      (Fintype.card V : ℝ) / 3 := by
  simp only [replicatedSeedOfCardEq, Cochain.defect_relabelComplete isConjInvariant_movedNorm,
    Cochain.gaugeDist_relabelComplete, replicatedSeed, Cochain.defect_div_gaugeDist_replicate,
    defect_ofLt_seed, gaugeDist_ofLt_seed, Fintype.card_fin, hV]
  push_cast
  ring

/-- `defect / gaugeDist` of the carried seed equals `h1 (complete V) (movedNorm (Fin 3))`. -/
theorem defect_div_gaugeDist_replicatedSeedOfCardEq_eq_h1 {q : ℕ}
    (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).defect (movedNorm (Fin 3)) /
        (replicatedSeedOfCardEq hV).gaugeDist (movedNorm (Fin 3)) =
      h1 (complete V) (movedNorm (Fin 3)) := by
  rw [defect_div_gaugeDist_replicatedSeedOfCardEq hV]
  by_cases hq : q = 0
  · have hc : Fintype.card V = 0 := by simp [hV, hq]
    let _ := Fintype.card_eq_zero_iff.mp hc
    rw [hc, Nat.cast_zero, zero_div]
    exact (h1_eq_zero_of_forall_gaugeDist_eq_zero fun α => by
      rw [show α = 1 from Cochain.ext fun v => isEmptyElim v, Cochain.gaugeDist_one]).symm
  · exact (h1_complete_movedNorm_fin_three (by omega : 3 ≤ Fintype.card V)).symm

end Sym3

end TauCeti
