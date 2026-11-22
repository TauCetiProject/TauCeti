/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Replication
import TauCeti.Combinatorics.CoboundaryExpansion.Replication
import TauCeti.Combinatorics.CoboundaryExpansion.StarBound
import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Basic
import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Staircase
import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree
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
* `h1_complete_fin_four`: the seed value `h1 (complete (Fin 4)) (movedNorm (Fin 3)) = 4 / 3`.

The lower bound is the star bound `card_div_three_le_h1_of_nontrivial`.
For the upper bound, every `k ≥ 3` is `4 q` or `(2 t + 1) q` with `t, q ≥ 1`.

* `k = (2 t + 1) q`: Kozlov's staircase graph `SimpleGraph.staircase q t`
  (`h1_complete_movedNorm_fin_three_le_of_card_eq_mul`).
* `k = 4 q`: the seed `Sym3.w4`, with the three transpositions on the pairs `(1, 2)`,
  `(1, 3)`, `(2, 3)`, has defect `8` (by `decide`) and gauge distance `6`. The identity gauge
  costs `6`, and every gauge costs at least `6`: the cost is `3` times the cross-degree pair cost
  (`Equiv.Perm.mul_distErr_mul_inv_eq_movedNorm`) and the seed infimum is `2`
  (`ciInf_sum_distErr_fin_four_three_of_eq_setOf_isSwap`). Its balanced replication
  `Sym3.replicatedSeed q = (Cochain.ofLt (complete (Fin 4)) w4).replicate (Fin q)` has defect
  `8 q ^ 3` and gauge distance `6 q ^ 2` (`Cochain.defect_replicate`,
  `Cochain.gaugeDist_replicate`), so `h1_complete_lex_le_card_mul_div` gives
  `h1 ≤ q * (8 / 6) = 4 q / 3`.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792,
  Proposition 5, Corollary 7 and Theorem 8.
* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136,
  Definition 3.2 (staircase graphs), Lemma 3.8 and Corollary 3.13 (cut-minimality).
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: the `k = 4` seed `w4` comes from `CoboundaryK3/Basic.lean`, and the assembly
  of the seeds follows `CoboundaryK3/Constant.lean` and `CoboundaryK3/Staircase.lean`.
-/

public section

namespace TauCeti

open Finset Equiv Equiv.Perm TwoComplex

namespace Sym3

/-- The `k = 4` seed of Proposition 5: `swap 1 2`, `swap 0 1`, `swap 0 2` on the ordered pairs
`(1, 2)`, `(1, 3)`, `(2, 3)` and `1` on all other ordered pairs; it is read on `u < v` (via
`Cochain.ofLt`). -/
def w4 (u v : Fin 4) : Perm (Fin 3) :=
  if u = 1 ∧ v = 2 then swap 1 2 else if u = 1 ∧ v = 3 then swap 0 1
  else if u = 2 ∧ v = 3 then swap 0 2 else 1

private theorem defect_w4 :
    (Cochain.ofLt (complete (Fin 4)) w4).defect (movedNorm (Fin 3)) = 8 := by
  rw [Cochain.defect_complete]
  have h : ∀ p ∈ (univ.filter fun p : Fin 4 × Fin 4 × Fin 4 => p.1 < p.2.1 ∧ p.2.1 < p.2.2),
      movedNorm (Fin 3) ((Cochain.ofLt (complete (Fin 4)) w4).holonomy p.1 p.2.1 p.2.2) =
        ((#(w4 p.1 p.2.1 * w4 p.2.1 p.2.2 * (w4 p.1 p.2.2)⁻¹).support : ℕ) : ℝ) := by
    intro p hp
    rw [mem_filter] at hp
    rw [Cochain.holonomy_ofLt_complete _ hp.2.1 hp.2.2, movedNorm_apply]
  rw [sum_congr rfl h, ← Nat.cast_sum]
  have h8 : ∑ p ∈ (univ.filter fun p : Fin 4 × Fin 4 × Fin 4 => p.1 < p.2.1 ∧ p.2.1 < p.2.2),
      #(w4 p.1 p.2.1 * w4 p.2.1 p.2.2 * (w4 p.1 p.2.2)⁻¹).support = 8 := by
    decide +kernel
  rw [h8]
  norm_num

/-- The replicated seed on `Fin 4 ×ₗ Fin q`: the balanced replication of the cochain of `w4`, so
`w4` between clusters and `1` inside a cluster. -/
noncomputable def replicatedSeed (q : ℕ) :
    Cochain (complete (Fin 4 ×ₗ Fin q)) (Perm (Fin 3)) :=
  (Cochain.ofLt (complete (Fin 4)) w4).replicate (Fin q)

/-- Replication multiplies the seed defect `8` by `q ^ 3`. -/
theorem replicatedSeed_defect (q : ℕ) :
    (replicatedSeed q).defect (movedNorm (Fin 3)) = 8 * (q : ℝ) ^ 3 := by
  rw [replicatedSeed, Cochain.defect_replicate, defect_w4, Fintype.card_fin]
  ring

/-- The replicated seed read on `u < v`: `w4` between clusters and `1` inside a cluster. -/
private theorem replicatedSeed_eq_ofLt (q : ℕ) : replicatedSeed q =
    Cochain.ofLt (complete (Fin 4 ×ₗ Fin q)) fun x y =>
      if (ofLex x).1 = (ofLex y).1 then 1 else w4 (ofLex x).1 (ofLex y).1 := by
  refine Cochain.ext fun x y hxy => ?_
  rw [replicatedSeed, Cochain.replicate_apply]
  rcases lt_or_gt_of_ne ((adj_complete _ _).mp hxy) with h | h
  · rw [Cochain.ofLt_apply_of_lt _ hxy h]
    split_ifs with hij
    · rw [hij]
      exact Cochain.ofLt_apply_of_not_adj _ (by simp)
    · exact Cochain.ofLt_apply_of_lt _ ((adj_complete _ _).mpr hij)
        (lt_of_le_of_ne (Prod.Lex.monotone_fst _ _ h.le) hij)
  · rw [Cochain.ofLt_apply_of_gt _ hxy h]
    split_ifs with hij
    · rw [hij, inv_one]
      exact Cochain.ofLt_apply_of_not_adj _ (by simp)
    · exact Cochain.ofLt_apply_of_gt _ ((adj_complete _ _).mpr (Ne.symm hij))
        (lt_of_le_of_ne (Prod.Lex.monotone_fst _ _ h.le) hij)

/-- Every gauge costs at least `6 q ^ 2` against the replication of `w4` on `Fin 4 ×ₗ Fin q`. -/
private theorem six_mul_sq_le_gaugeDist_lex (q : ℕ) :
    (6 * q ^ 2 : ℝ) ≤ (Cochain.ofLt (complete (Fin 4 ×ₗ Fin q)) fun x y =>
      if (ofLex x).1 = (ofLex y).1 then 1 else w4 (ofLex x).1 (ofLex y).1).gaugeDist
        (movedNorm (Fin 3)) := by
  have h0 : ∀ v : Fin 4, 0 < v → w4 0 v = 1 := by decide
  have hsw : ({w4 1 2, w4 1 3, w4 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap} := by
    rw [setOf_isSwap_perm_fin_three]
    ext σ
    simp only [w4, Set.mem_insert_iff, Set.mem_singleton_iff]
    decide +revert
  have hinf := card_sq_mul_ciInf_le_ciInf_sum_distErr_lex (ι := Fin q) w4 3
  rw [ciInf_sum_distErr_fin_four_three_of_eq_setOf_isSwap w4 h0 hsw, Fintype.card_fin] at hinf
  refine (Cochain.le_gaugeDist_iff _ _).mpr fun β => ?_
  rw [Cochain.cost_complete]
  have hterm : ∀ e ∈ (univ.filter fun p : (Fin 4 ×ₗ Fin q) × (Fin 4 ×ₗ Fin q) => p.1 < p.2),
      movedNorm (Fin 3) ((β e.1)⁻¹ * (Cochain.ofLt (complete (Fin 4 ×ₗ Fin q)) fun x y =>
        if (ofLex x).1 = (ofLex y).1 then 1 else w4 (ofLex x).1 (ofLex y).1) e.1 e.2 * β e.2) =
      3 * distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else w4 (ofLex e.1).1 (ofLex e.2).1)
        (β e.1 * (β e.2)⁻¹) := by
    intro e he
    rw [mem_filter] at he
    rw [Cochain.ofLt_apply_of_lt _ ((adj_complete _ _).mpr he.2.ne) he.2,
      ← mul_distErr_mul_inv_eq_movedNorm]
    norm_num
  rw [sum_congr rfl hterm, ← mul_sum]
  have hle := ciInf_le (⟨0, Set.forall_mem_range.2 fun β' => sum_nonneg fun _ _ =>
    distErr_nonneg _ _⟩ : BddBelow (Set.range fun β' : (Fin 4 ×ₗ Fin q) → Perm (Fin 3) =>
      ∑ e ∈ (univ.filter fun p : (Fin 4 ×ₗ Fin q) × (Fin 4 ×ₗ Fin q) => p.1 < p.2),
        distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else w4 (ofLex e.1).1 (ofLex e.2).1)
          (β' e.1 * (β' e.2)⁻¹))) β
  linarith


/-- The identity gauge costs `6` against the seed: its three non-identity edges are
transpositions. -/
private theorem cost_one_w4 :
    (Cochain.ofLt (complete (Fin 4)) w4).cost (movedNorm (Fin 3)) (fun _ => 1) = 6 := by
  rw [Cochain.cost_complete]
  have h : ∀ p ∈ (univ.filter fun p : Fin 4 × Fin 4 => p.1 < p.2),
      movedNorm (Fin 3) ((1 : Perm (Fin 3))⁻¹ *
        (Cochain.ofLt (complete (Fin 4)) w4) p.1 p.2 * 1) =
        ((#(w4 p.1 p.2).support : ℕ) : ℝ) := by
    intro p hp
    rw [mem_filter] at hp
    rw [Cochain.ofLt_apply_of_lt _ ((adj_complete _ _).mpr hp.2.ne) hp.2, inv_one, one_mul,
      mul_one, movedNorm_apply]
  rw [sum_congr rfl h, ← Nat.cast_sum]
  have h6 : ∑ p ∈ (univ.filter fun p : Fin 4 × Fin 4 => p.1 < p.2), #(w4 p.1 p.2).support = 6 := by
    decide +kernel
  rw [h6]
  norm_num

/-- The seed has gauge distance `6`, attained by the identity gauge. -/
private theorem gaugeDist_w4 :
    (Cochain.ofLt (complete (Fin 4)) w4).gaugeDist (movedNorm (Fin 3)) = 6 := by
  refine le_antisymm (((Cochain.ofLt (complete (Fin 4)) w4).gaugeDist_le_cost _
    (fun _ => 1)).trans cost_one_w4.le) ?_
  have h := six_mul_sq_le_gaugeDist_lex 1
  rw [← replicatedSeed_eq_ofLt, replicatedSeed, Cochain.gaugeDist_replicate,
    Fintype.card_fin] at h
  simpa using h

/-- Replication multiplies the seed gauge distance `6` by `q ^ 2`. -/
theorem replicatedSeed_gaugeDist (q : ℕ) :
    (replicatedSeed q).gaugeDist (movedNorm (Fin 3)) = 6 * (q : ℝ) ^ 2 := by
  rw [replicatedSeed, Cochain.gaugeDist_replicate, gaugeDist_w4, Fintype.card_fin]
  ring

/-- The identity gauge attains the gauge distance `6 q ^ 2` of the replicated seed: edges inside a
cluster carry `1`, and each edge of `w4` is copied `q ^ 2` times. -/
theorem replicatedSeed_cost_one (q : ℕ) :
    (replicatedSeed q).cost (movedNorm (Fin 3)) (fun _ => 1) = 6 * (q : ℝ) ^ 2 := by
  have h := cost_one_w4
  rw [Cochain.cost_complete] at h
  rw [Cochain.cost_complete, Fintype.sum_filter_lt_lex (V := Fin 4) (ι := Fin q)]
  simp only [inv_one, one_mul, mul_one] at h ⊢
  have hin : ∀ (v : Fin 4) (a b : Fin q),
      movedNorm (Fin 3) ((replicatedSeed q).toFun (toLex (v, a)) (toLex (v, b))) = 0 := by
    intro v a b
    rw [replicatedSeed, Cochain.replicate_apply,
      Cochain.ofLt_apply_of_not_adj _ (by simp), map_one_eq_zero]
  have hout : ∀ (e : Fin 4 × Fin 4) (a b : Fin q),
      movedNorm (Fin 3) ((replicatedSeed q).toFun (toLex (e.1, a)) (toLex (e.2, b))) =
        movedNorm (Fin 3) ((Cochain.ofLt (complete (Fin 4)) w4).toFun e.1 e.2) := by
    intro e a b
    rw [replicatedSeed, Cochain.replicate_apply]
    rfl
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
    (gaugeDist_w4.symm ▸ (by norm_num : (0 : ℝ) < 6))).trans_eq ?_
  rw [defect_w4, gaugeDist_w4, Fintype.card_fin, hV]
  push_cast
  ring

end Sym3

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The replicated seed carried to any `V` with `Fintype.card V = 4 * q`, by the vertex
relabelling of `h1_complete_eq_of_card_eq`. -/
noncomputable def replicatedSeedOfCardEq {q : ℕ} (hV : Fintype.card V = 4 * q) :
    Cochain (complete V) (Perm (Fin 3)) :=
  (Sym3.replicatedSeed q).relabelComplete (Fintype.equivOfCardEq <| by
    rw [Fintype.card_lex, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hV])

theorem replicatedSeedOfCardEq_defect {q : ℕ} (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).defect (movedNorm (Fin 3)) = 8 * (q : ℝ) ^ 3 := by
  rw [replicatedSeedOfCardEq,
    Cochain.defect_relabelComplete isConjInvariant_movedNorm, Sym3.replicatedSeed_defect]

theorem replicatedSeedOfCardEq_gaugeDist {q : ℕ} (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).gaugeDist (movedNorm (Fin 3)) = 6 * (q : ℝ) ^ 2 := by
  rw [replicatedSeedOfCardEq, Cochain.gaugeDist_relabelComplete, Sym3.replicatedSeed_gaugeDist]

theorem replicatedSeedOfCardEq_cost_one {q : ℕ} (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).cost (movedNorm (Fin 3)) (fun _ => 1) = 6 * (q : ℝ) ^ 2 := by
  rw [replicatedSeedOfCardEq, Cochain.cost_relabelComplete]
  convert Sym3.replicatedSeed_cost_one q using 2
  funext
  rfl

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

/-- The relabelled replicated seed attains `h1`: `defect / gaugeDist = card V / 3`. -/
theorem replicatedSeedOfCardEq_attains {q : ℕ} (hq : 0 < q) (hV : Fintype.card V = 4 * q) :
    (replicatedSeedOfCardEq hV).defect (movedNorm (Fin 3)) /
        (replicatedSeedOfCardEq hV).gaugeDist (movedNorm (Fin 3)) =
      (Fintype.card V : ℝ) / 3 ∧
    (replicatedSeedOfCardEq hV).defect (movedNorm (Fin 3)) /
        (replicatedSeedOfCardEq hV).gaugeDist (movedNorm (Fin 3)) =
      h1 (complete V) (movedNorm (Fin 3)) := by
  have h3 : 3 ≤ Fintype.card V := by omega
  rw [replicatedSeedOfCardEq_defect, replicatedSeedOfCardEq_gaugeDist,
    h1_complete_movedNorm_fin_three h3, hV]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  constructor
  · field_simp [hq']
    push_cast
    ring
  · field_simp [hq']
    push_cast
    ring

end TauCeti
