/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
import TauCeti.Combinatorics.CoboundaryExpansion.Replication
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
* `h1_complete_fin_four`: the seed value `h1 (complete (Fin 4)) (movedNorm (Fin 3)) = 4 / 3`.

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
  `Sym3.replicatedSeedOfCardEq` carries that cochain to any `V` with `card V = 4 q`, preserving
  defect, gauge distance and identity-gauge cost, and `Sym3.replicatedSeedOfCardEq_attains` is
  the resulting ratio `card V / 3`, equal to `h1`. `h1_complete_lex_le_card_mul_div` gives the
  upper bound `h1 ≤ q * (8 / 6) = 4 q / 3`.

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

/-- The moved-point defect of `Cochain.ofLt (complete (Fin k)) f` is the sum, over `u < v < w`,
of the number of points moved by `f u v * f v w * (f u w)⁻¹`. -/
theorem defect_ofLt_movedNorm {k : ℕ} (f : Fin k → Fin k → Perm (Fin 3)) :
    (Cochain.ofLt (complete (Fin k)) f).defect (movedNorm (Fin 3)) =
      (∑ p ∈ univ.filter fun p : Fin k × Fin k × Fin k => p.1 < p.2.1 ∧ p.2.1 < p.2.2,
        (f p.1 p.2.1 * f p.2.1 p.2.2 * (f p.1 p.2.2)⁻¹).support.card : ℝ) := by
  rw [Cochain.defect_complete]
  have h :
      ∀ p ∈ univ.filter fun p : Fin k × Fin k × Fin k => p.1 < p.2.1 ∧ p.2.1 < p.2.2,
        movedNorm (Fin 3)
            ((Cochain.ofLt (complete (Fin k)) f).holonomy p.1 p.2.1 p.2.2) =
          (((f p.1 p.2.1 * f p.2.1 p.2.2 * (f p.1 p.2.2)⁻¹).support.card : ℕ) : ℝ) := by
    intro p hp
    rw [mem_filter] at hp
    rw [Cochain.holonomy_ofLt_complete _ hp.2.1 hp.2.2, movedNorm_apply]
  rw [sum_congr rfl h, ← Nat.cast_sum]

/-- The moved-point cost of a gauge `β` against `Cochain.ofLt (complete (Fin k)) α` is the sum,
over `u < v`, of the number of points moved by `(β u)⁻¹ * α u v * β v`. -/
theorem cost_ofLt_movedNorm {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3))
    (β : Fin k → Perm (Fin 3)) :
    (Cochain.ofLt (complete (Fin k)) α).cost (movedNorm (Fin 3)) β =
      (∑ p ∈ univ.filter fun p : Fin k × Fin k => p.1 < p.2,
        ((β p.1)⁻¹ * α p.1 p.2 * β p.2).support.card : ℝ) := by
  rw [Cochain.cost_complete]
  have h : ∀ p ∈ univ.filter fun p : Fin k × Fin k => p.1 < p.2,
      movedNorm (Fin 3) ((β p.1)⁻¹ *
        (Cochain.ofLt (complete (Fin k)) α) p.1 p.2 * β p.2) =
        (((β p.1)⁻¹ * α p.1 p.2 * β p.2).support.card : ℝ) := by
    intro p hp
    rw [mem_filter] at hp
    rw [Cochain.ofLt_apply_of_lt _ ((adj_complete _ _).mpr hp.2.ne) hp.2, movedNorm_apply]
  rw [sum_congr rfl h, ← Nat.cast_sum]

/-- The seed has moved-point defect `8`. -/
theorem defect_seed :
    (Cochain.ofLt (complete (Fin 4)) seed).defect (movedNorm (Fin 3)) = 8 := by
  rw [defect_ofLt_movedNorm]
  have h8 : ∑ p ∈ univ.filter fun p : Fin 4 × Fin 4 × Fin 4 => p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      (seed p.1 p.2.1 * seed p.2.1 p.2.2 * (seed p.1 p.2.2)⁻¹).support.card = 8 := by
    decide +kernel
  exact_mod_cast h8

/-- The identity gauge costs `6` against the seed: its three non-identity edges are
transpositions. -/
theorem cost_one_seed :
    (Cochain.ofLt (complete (Fin 4)) seed).cost (movedNorm (Fin 3)) (fun _ => 1) = 6 := by
  rw [cost_ofLt_movedNorm]
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
  have hinf := ciInf_sum_distErr_fin_four_three_of_eq_setOf_isSwap seed h0 hsw
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
  have hbdd : BddBelow (Set.range fun β' : Fin 4 → Perm (Fin 3) =>
      ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
        distErr (seed e.1 e.2) (β' e.1 * (β' e.2)⁻¹)) :=
    ⟨0, by rintro _ ⟨β', rfl⟩; exact sum_nonneg fun _ _ => distErr_nonneg _ _⟩
  have hle : (2 : ℝ) ≤ ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
      distErr (seed e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
    rw [← hinf]
    exact ciInf_le hbdd β
  linarith

/-- The replicated seed on `Fin 4 ×ₗ Fin q`: the balanced replication of the cochain of `seed`,
so `seed` between clusters and `1` inside a cluster. -/
noncomputable def replicatedSeed (q : ℕ) :
    Cochain (complete (Fin 4 ×ₗ Fin q)) (Perm (Fin 3)) :=
  (Cochain.ofLt (complete (Fin 4)) seed).replicate (Fin q)

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
    (gaugeDist_seed.symm ▸ (by norm_num : (0 : ℝ) < 6))).trans_eq ?_
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

/-- The carried seed has the same defect `8 q ^ 3` as `replicatedSeed q`. -/
theorem defect_replicatedSeedOfCardEq {q : ℕ} (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).defect (movedNorm (Fin 3)) = 8 * (q : ℝ) ^ 3 := by
  rw [replicatedSeedOfCardEq, Cochain.defect_relabelComplete isConjInvariant_movedNorm,
    defect_replicatedSeed]

/-- The carried seed has the same gauge distance `6 q ^ 2` as `replicatedSeed q`. -/
theorem gaugeDist_replicatedSeedOfCardEq {q : ℕ} (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).gaugeDist (movedNorm (Fin 3)) = 6 * (q : ℝ) ^ 2 := by
  rw [replicatedSeedOfCardEq, Cochain.gaugeDist_relabelComplete, gaugeDist_replicatedSeed]

/-- The identity gauge costs `6 q ^ 2` against the carried seed. -/
theorem cost_one_replicatedSeedOfCardEq {q : ℕ} (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).cost (movedNorm (Fin 3)) (fun _ => 1) = 6 * (q : ℝ) ^ 2 := by
  rw [replicatedSeedOfCardEq, Cochain.cost_relabelComplete]
  refine (congrArg ((replicatedSeed q).cost (movedNorm (Fin 3))) ?_).trans
    (cost_one_replicatedSeed q)
  funext _
  simp only [Function.comp_apply]

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

namespace Sym3

/-- The relabelled replicated seed attains `h1`: its ratio is `card V / 3`, hence equal to
`h1 (complete V) (movedNorm (Fin 3))`. -/
theorem replicatedSeedOfCardEq_attains {q : ℕ} (hq : 0 < q) (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).defect (movedNorm (Fin 3)) /
        (replicatedSeedOfCardEq hV).gaugeDist (movedNorm (Fin 3)) =
      (Fintype.card V : ℝ) / 3 ∧
    (replicatedSeedOfCardEq hV).defect (movedNorm (Fin 3)) /
        (replicatedSeedOfCardEq hV).gaugeDist (movedNorm (Fin 3)) =
      h1 (complete V) (movedNorm (Fin 3)) := by
  have h3 : 3 ≤ Fintype.card V := by omega
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr : (replicatedSeedOfCardEq hV).defect (movedNorm (Fin 3)) /
      (replicatedSeedOfCardEq hV).gaugeDist (movedNorm (Fin 3)) =
      (Fintype.card V : ℝ) / 3 := by
    rw [defect_replicatedSeedOfCardEq, gaugeDist_replicatedSeedOfCardEq, hV]
    field_simp [hq']
    push_cast
    ring
  exact ⟨hr, hr.trans (h1_complete_movedNorm_fin_three h3).symm⟩

end Sym3

end TauCeti
