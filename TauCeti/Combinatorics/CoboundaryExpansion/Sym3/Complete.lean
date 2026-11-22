/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.CoboundaryExpansion.Replication
import TauCeti.Combinatorics.CoboundaryExpansion.StarBound
import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Basic
import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Staircase
import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree
import TauCeti.GroupTheory.Perm.FinThree.Basic
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
* `h1_complete_fin_four` through `h1_complete_fin_eight`: the values `4 / 3`, `5 / 3`, `6 / 3`,
  `7 / 3` and `8 / 3`;
* `h1_complete_movedNorm_fin_three_of_four_dvd`: the same identity when `4 ∣ card V` and
  `4 ≤ card V` (Beasley, Corollary 7).

The lower bound is the star bound `card_div_three_le_h1_of_nontrivial`.
For the upper bound, every `k ≥ 3` is `4 q` or `(2 t + 1) q` with `t, q ≥ 1`.

* `k = (2 t + 1) q`: Kozlov's staircase graph `SimpleGraph.staircase q t`
  (`h1_complete_movedNorm_fin_three_le_of_card_eq_mul`).
* `k = 4 q`: the seed `Sym3.seed`, with the three transpositions on the pairs `(1, 2)`,
  `(1, 3)`, `(2, 3)`, has defect `8` (`defect_seed`) and gauge distance `6` (`gaugeDist_seed`).
  The identity gauge costs `6` (`cost_one_seed`), and every gauge costs at least `6`: the cost is
  `3` times the cross-degree pair cost (`Equiv.Perm.mul_distErr_mul_inv_eq_movedNorm`) and the
  seed infimum is `2` (`ciInf_sum_distErr_fin_four_three_of_eq_setOf_isSwap`). Its balanced
  replication `Sym3.replicatedSeed q = (Cochain.ofLt (complete (Fin 4)) seed).replicate (Fin q)`
  has defect `8 q ^ 3` and gauge distance `6 q ^ 2` (`defect_replicatedSeed`,
  `gaugeDist_replicatedSeed`, from `Cochain.defect_replicate` and `Cochain.gaugeDist_replicate`),
  and the identity gauge costs `6 q ^ 2` (`cost_one_replicatedSeed`).
  `Sym3.replicatedSeedOfCardEq` carries that cochain to any `V` with `card V = 4 q`.
  `Sym3.defect_div_gaugeDist_replicatedSeedOfCardEq` is the ratio `card V / 3`, and
  `Sym3.defect_div_gaugeDist_replicatedSeedOfCardEq_eq_h1` identifies it with `h1`.
  `h1_complete_lex_le_card_mul_div` gives the upper bound `h1 ≤ q * (8 / 6) = 4 q / 3`.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792,
  Proposition 5, Corollary 7 and Theorem 8.
* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136,
  Definition 3.2 (staircase graphs), Lemma 3.8 and Corollary 3.13 (cut-minimality).
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: the `k = 4` seed, called `w4` there, comes from `CoboundaryK3/Basic.lean`, and
  the assembly of the seeds follows `CoboundaryK3/Constant.lean` and `CoboundaryK3/Staircase.lean`.
-/

public section

namespace TauCeti

open Finset Equiv Equiv.Perm TwoComplex

namespace Sym3

/-- The four-vertex seed of Proposition 5, the edge labelling called `w4` in
`CoboundaryK3/Basic.lean`: `swap 1 2`, `swap 0 1` and `swap 0 2` on the ordered pairs
`(1, 2)`, `(1, 3)` and `(2, 3)`, and `1` on every other ordered pair. `Cochain.ofLt` reads it
on `u < v`. -/
def seed (u v : Fin 4) : Perm (Fin 3) :=
  if u = 1 ∧ v = 2 then swap 1 2 else if u = 1 ∧ v = 3 then swap 0 1
  else if u = 2 ∧ v = 3 then swap 0 2 else 1

/-- `seed` is `swap 1 2`, `swap 0 1`, `swap 0 2` on `(1, 2)`, `(1, 3)`, `(2, 3)`, and `1`
elsewhere. -/
theorem seed_apply (u v : Fin 4) : seed u v =
    if u = 1 ∧ v = 2 then swap 1 2 else if u = 1 ∧ v = 3 then swap 0 1
    else if u = 2 ∧ v = 3 then swap 0 2 else 1 :=
  (rfl)

/-- The seed has moved-point defect `8`. -/
theorem defect_seed :
    (Cochain.ofLt (complete (Fin 4)) seed).defect (movedNorm (Fin 3)) = 8 := by
  rw [Cochain.defect_ofLt_complete_movedNorm]
  have h8 : ∑ p ∈ univ.filter fun p : Fin 4 × Fin 4 × Fin 4 => p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      (seed p.1 p.2.1 * seed p.2.1 p.2.2 * (seed p.1 p.2.2)⁻¹).support.card = 8 := by
    decide +kernel
  exact_mod_cast h8

/-- The identity gauge costs `6` against the seed: its three non-identity edges are
transpositions. -/
theorem cost_one_seed :
    (Cochain.ofLt (complete (Fin 4)) seed).cost (movedNorm (Fin 3)) (fun _ => 1) = 6 := by
  rw [Cochain.cost_ofLt_complete_movedNorm]
  simp only [inv_one, one_mul, mul_one]
  have h6 : ∑ p ∈ univ.filter fun p : Fin 4 × Fin 4 => p.1 < p.2,
      (seed p.1 p.2).support.card = 6 := by
    decide +kernel
  exact_mod_cast h6

/-- The seed has gauge distance `6`, attained by the identity gauge. -/
theorem gaugeDist_seed :
    (Cochain.ofLt (complete (Fin 4)) seed).gaugeDist (movedNorm (Fin 3)) = 6 := by
  refine le_antisymm (((Cochain.ofLt (complete (Fin 4)) seed).gaugeDist_le_cost _
    (fun _ => 1)).trans cost_one_seed.le) ?_
  have h0 : ∀ v : Fin 4, 0 < v → seed 0 v = 1 := by decide
  have hsw : ({seed 1 2, seed 1 3, seed 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap} := by
    rw [setOf_isSwap_perm_fin_three]
    ext σ
    simp only [seed, Set.mem_insert_iff, Set.mem_singleton_iff]
    decide +revert
  refine (Cochain.le_gaugeDist_iff _ _).mpr fun β => ?_
  rw [Cochain.cost_complete]
  have hS : univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2) =
      ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)) := by
    ext p
    simp
  rw [hS]
  have hterm : ∀ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
      movedNorm (Fin 3) ((β e.1)⁻¹ * (Cochain.ofLt (complete (Fin 4)) seed) e.1 e.2 * β e.2) =
        3 * distErr (seed e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
    intro e he
    have hlt : e.1 < e.2 := by simpa using he
    rw [Cochain.ofLt_apply_of_lt _ ((adj_complete _ _).mpr hlt.ne) hlt,
      ← mul_distErr_mul_inv_eq_movedNorm]
    norm_num
  rw [sum_congr rfl hterm, ← mul_sum]
  have hle := two_le_sum_distErr_fin_four_of_eq_setOf_isSwap seed h0 hsw β
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
  rw [replicatedSeed, Cochain.defect_replicate, defect_seed, Fintype.card_fin]
  ring

/-- Replication multiplies the seed gauge distance `6` by `q ^ 2`. -/
theorem gaugeDist_replicatedSeed (q : ℕ) :
    (replicatedSeed q).gaugeDist (movedNorm (Fin 3)) = 6 * (q : ℝ) ^ 2 := by
  rw [replicatedSeed, Cochain.gaugeDist_replicate, gaugeDist_seed, Fintype.card_fin]
  ring

/-- The identity gauge costs `6 q ^ 2` against the replicated seed: edges inside a cluster carry
`1`, and each edge of `seed` is copied `q ^ 2` times. -/
theorem cost_one_replicatedSeed (q : ℕ) :
    (replicatedSeed q).cost (movedNorm (Fin 3)) (fun _ => 1) = 6 * (q : ℝ) ^ 2 := by
  have h := cost_one_seed
  rw [Cochain.cost_complete] at h
  rw [Cochain.cost_complete, Fintype.sum_filter_lt_lex (V := Fin 4) (ι := Fin q)]
  simp only [inv_one, one_mul, mul_one] at h ⊢
  have hin : ∀ (v : Fin 4) (a b : Fin q),
      movedNorm (Fin 3) (replicatedSeed q (toLex (v, a)) (toLex (v, b))) = 0 := by
    intro v a b
    simp [replicatedSeed, Cochain.replicate_apply, ofLex_toLex, map_one_eq_zero]
  have hout : ∀ (e : Fin 4 × Fin 4) (a b : Fin q),
      movedNorm (Fin 3) (replicatedSeed q (toLex (e.1, a)) (toLex (e.2, b))) =
        movedNorm (Fin 3) ((Cochain.ofLt (complete (Fin 4)) seed) e.1 e.2) := by
    intro e a b
    simp [replicatedSeed, Cochain.replicate_apply, ofLex_toLex]
  simp only [hin, hout, sum_const_zero, zero_add, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] at h ⊢
  rw [h]
  ring

/-- The upper bound when `card V = 4 q`: replicate the seed, whose ratio is `8 / 6`. -/
private theorem h1_complete_le_of_card_eq_four_mul {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hV : Fintype.card V = 4 * q) :
    h1 (complete V) (movedNorm (Fin 3)) ≤ (Fintype.card V : ℝ) / 3 := by
  rw [h1_complete_eq_of_card_eq isConjInvariant_movedNorm (W := Fin 4 ×ₗ Fin q)
    (by rw [hV, Fintype.card_lex, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin])]
  refine (h1_complete_lex_le_card_mul_div (ι := Fin q)
    (by rw [gaugeDist_seed]; norm_num)).trans_eq ?_
  rw [defect_seed, gaugeDist_seed, Fintype.card_fin, hV]
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
    have hq0 : 0 < q := Nat.pos_of_ne_zero fun h => by simp [h] at hq; omega
    exact h1_complete_movedNorm_fin_three_le_of_card_eq_mul hq0 ht (by rw [hq]; ring)

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

/-- On the complete complex with four vertices the `Sym(3)` coboundary constant is `4/3`. -/
theorem h1_complete_fin_four : h1 (complete (Fin 4)) (movedNorm (Fin 3)) = 4 / 3 := by
  simpa using h1_complete_movedNorm_fin_three (V := Fin 4) (by simp)

/-- `h1 (complete (Fin 5)) (movedNorm (Fin 3)) = 5 / 3` (Beasley, Theorem 4). -/
theorem h1_complete_fin_five : h1 (complete (Fin 5)) (movedNorm (Fin 3)) = 5 / 3 := by
  simpa using h1_complete_movedNorm_fin_three (V := Fin 5) (by simp)

/-- `h1 (complete (Fin 6)) (movedNorm (Fin 3)) = 6 / 3` (Beasley, Theorem 4). -/
theorem h1_complete_fin_six : h1 (complete (Fin 6)) (movedNorm (Fin 3)) = 6 / 3 := by
  simpa using h1_complete_movedNorm_fin_three (V := Fin 6) (by simp)

/-- `h1 (complete (Fin 7)) (movedNorm (Fin 3)) = 7 / 3` (Beasley, Theorem 4). -/
theorem h1_complete_fin_seven : h1 (complete (Fin 7)) (movedNorm (Fin 3)) = 7 / 3 := by
  simpa using h1_complete_movedNorm_fin_three (V := Fin 7) (by simp)

/-- `h1 (complete (Fin 8)) (movedNorm (Fin 3)) = 8 / 3` (Beasley, Theorem 4). -/
theorem h1_complete_fin_eight : h1 (complete (Fin 8)) (movedNorm (Fin 3)) = 8 / 3 := by
  simpa using h1_complete_movedNorm_fin_three (V := Fin 8) (by simp)

/-- Whenever `4 ∣ Fintype.card V` and `4 ≤ Fintype.card V`,
`h1 (complete V) (movedNorm (Fin 3)) = card V / 3` (Beasley, Corollary 7). This is the
`4 ∣ card V` case of `h1_complete_movedNorm_fin_three`. -/
theorem h1_complete_movedNorm_fin_three_of_four_dvd (h4 : 4 ∣ Fintype.card V)
    (hV : 4 ≤ Fintype.card V) :
    h1 (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / 3 := by
  obtain ⟨q, hq⟩ := h4
  rw [h1_complete_movedNorm_fin_three (by omega), hq]

namespace Sym3

/-- `defect / gaugeDist` of the carried seed equals `Fintype.card V / 3`. -/
theorem defect_div_gaugeDist_replicatedSeedOfCardEq {q : ℕ} (hq : 0 < q)
    (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).defect (movedNorm (Fin 3)) /
        (replicatedSeedOfCardEq hV).gaugeDist (movedNorm (Fin 3)) =
      (Fintype.card V : ℝ) / 3 := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [replicatedSeedOfCardEq, Cochain.defect_relabelComplete isConjInvariant_movedNorm,
    Cochain.gaugeDist_relabelComplete, replicatedSeed, Cochain.defect_div_gaugeDist_replicate,
    defect_seed, gaugeDist_seed, Fintype.card_fin, hV]
  field_simp [hq']
  push_cast
  ring

/-- `defect / gaugeDist` of the carried seed equals `h1 (complete V) (movedNorm (Fin 3))`. -/
theorem defect_div_gaugeDist_replicatedSeedOfCardEq_eq_h1 {q : ℕ} (hq : 0 < q)
    (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).defect (movedNorm (Fin 3)) /
        (replicatedSeedOfCardEq hV).gaugeDist (movedNorm (Fin 3)) =
      h1 (complete V) (movedNorm (Fin 3)) := by
  have h3 : 3 ≤ Fintype.card V := by omega
  rw [defect_div_gaugeDist_replicatedSeedOfCardEq hq hV, h1_complete_movedNorm_fin_three h3]

end Sym3

end TauCeti
