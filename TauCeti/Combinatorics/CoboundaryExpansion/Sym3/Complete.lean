/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Replication
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
  `(1, 3)`, `(2, 3)`, replicated on `Fin 4 ×ₗ Fin q` as `Sym3.replicatedSeed`. Its defect is
  `8 q ^ 3`
  (`Cochain.defect_ofLt_lex`; `8` by `decide` for the seed), and every gauge costs at least
  `6 q ^ 2`: the cost is `3` times the cross-degree pair cost
  (`Equiv.Perm.mul_distErr_mul_inv_eq_movedNorm`), replication multiplies its infimum by at least
  `q ^ 2` (`card_sq_mul_ciInf_le_ciInf_sum_distErr_lex`) and the seed infimum is `2`
  (`ciInf_sum_distErr_fin_four_three_of_eq_setOf_isSwap`). So `h1_le_div` gives
  `h1 ≤ 8 q ^ 3 / (6 q ^ 2) = 4 q / 3`.

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

/-- The replicated seed on `Fin 4 ×ₗ Fin q`: `w4` between clusters and `1` inside a cluster. -/
noncomputable def replicatedSeed (q : ℕ) :
    Cochain (complete (Fin 4 ×ₗ Fin q)) (Perm (Fin 3)) :=
  Cochain.ofLt (complete (Fin 4 ×ₗ Fin q)) fun x y =>
    if (ofLex x).1 = (ofLex y).1 then 1 else w4 (ofLex x).1 (ofLex y).1

/-- Replication multiplies the seed defect `8` by `q ^ 3`. -/
theorem replicatedSeed_defect (q : ℕ) :
    (replicatedSeed q).defect (movedNorm (Fin 3)) = 8 * (q : ℝ) ^ 3 := by
  rw [replicatedSeed, Cochain.defect_ofLt_lex, defect_w4, Fintype.card_fin]
  ring

private theorem w4_support_sum :
    ∑ i : Fin 4, ∑ j : Fin 4,
      (if i < j then (w4 i j).support.card else 0 : ℕ) = 6 := by
  decide +kernel

/-- The identity gauge on the replicated seed costs `6 q ^ 2`: the three non-identity edges of
`w4` are transpositions, and each is copied `q ^ 2` times. -/
theorem replicatedSeed_cost_one (q : ℕ) :
    (replicatedSeed q).cost (movedNorm (Fin 3)) (fun _ => 1) = 6 * (q : ℝ) ^ 2 := by
  rw [Cochain.cost_complete, sum_filter, Fintype.sum_prod_type]
  simp only [inv_one, one_mul, mul_one]
  have hterm : ∀ x y : Fin 4 ×ₗ Fin q,
      (if x < y then movedNorm (Fin 3) ((replicatedSeed q).toFun x y) else 0) =
        if x < y then movedNorm (Fin 3)
          (if (ofLex x).1 = (ofLex y).1 then (1 : Perm (Fin 3))
            else w4 (ofLex x).1 (ofLex y).1) else 0 := by
    intro x y
    by_cases hlt : x < y
    · rw [ite_eq_left hlt, ite_eq_left hlt, replicatedSeed,
        Cochain.ofLt_apply_of_lt _ ((adj_complete _ _).mpr hlt.ne) hlt]
    · rw [ite_eq_right hlt, ite_eq_right hlt]
  conv_lhs =>
    arg 2
    ext x
    arg 2
    ext y
    rw [hterm x y]
  simp_rw [← Equiv.sum_comp (toLex : Fin 4 × Fin q ≃ Fin 4 ×ₗ Fin q), Fintype.sum_prod_type]
  have hbody : ∀ (i j : Fin 4) (a b : Fin q),
      (if toLex (i, a) < toLex (j, b) then
          movedNorm (Fin 3)
            (if (ofLex (toLex (i, a))).1 = (ofLex (toLex (j, b))).1 then 1
              else w4 (ofLex (toLex (i, a))).1 (ofLex (toLex (j, b))).1) else 0) =
        (if i < j then ((w4 i j).support.card : ℝ) else 0) := by
    intro i j a b
    have hi : (ofLex (toLex (i, a))).1 = i := congrArg Prod.fst (ofLex_toLex (i, a))
    have hj : (ofLex (toLex (j, b))).1 = j := congrArg Prod.fst (ofLex_toLex (j, b))
    by_cases hij : i < j
    · have hlt : toLex (i, a) < toLex (j, b) := Prod.Lex.toLex_lt_toLex.mpr (Or.inl hij)
      rw [ite_eq_left hlt, hi, hj, ite_eq_right hij.ne, ite_eq_left hij, movedNorm_apply]
    · rw [ite_eq_right hij]
      by_cases hlt : toLex (i, a) < toLex (j, b)
      · rw [ite_eq_left hlt, hi, hj]
        rcases Prod.Lex.toLex_lt_toLex.mp hlt with h | ⟨rfl, -⟩
        · exact absurd h hij
        · simp
      · rw [ite_eq_right hlt]
  have hsum :
      (∑ i : Fin 4, ∑ a : Fin q, ∑ j : Fin 4, ∑ b : Fin q,
        if toLex (i, a) < toLex (j, b) then
          movedNorm (Fin 3)
            (if (ofLex (toLex (i, a))).1 = (ofLex (toLex (j, b))).1 then 1
              else w4 (ofLex (toLex (i, a))).1 (ofLex (toLex (j, b))).1) else 0) =
      ∑ i : Fin 4, ∑ (_ : Fin q), ∑ j : Fin 4, ∑ (_ : Fin q),
        if i < j then ((w4 i j).support.card : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => hbody i j a b
  rw [hsum]
  simp_rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h6 : (∑ i : Fin 4, ∑ j : Fin 4,
      (if i < j then ((w4 i j).support.card : ℝ) else 0)) = 6 := by
    exact_mod_cast w4_support_sum
  simp_rw [← Finset.mul_sum]
  rw [h6]
  ring

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

/-- The identity gauge attains the gauge distance of the replicated seed: every gauge costs at
least `6 q ^ 2`, and `fun _ => 1` costs exactly that. -/
theorem replicatedSeed_gaugeDist (q : ℕ) :
    (replicatedSeed q).gaugeDist (movedNorm (Fin 3)) = 6 * (q : ℝ) ^ 2 := by
  refine le_antisymm (((replicatedSeed q).gaugeDist_le_cost _ (fun _ => 1)).trans
    (le_of_eq (replicatedSeed_cost_one q))) ?_
  simpa [replicatedSeed] using six_mul_sq_le_gaugeDist_lex q

theorem replicatedSeed_gaugeDist_eq_cost_one (q : ℕ) :
    (replicatedSeed q).gaugeDist (movedNorm (Fin 3)) =
      (replicatedSeed q).cost (movedNorm (Fin 3)) (fun _ => 1) := by
  rw [replicatedSeed_gaugeDist, replicatedSeed_cost_one]

theorem replicatedSeed_defect_one : (replicatedSeed 1).defect (movedNorm (Fin 3)) = 8 := by
  rw [replicatedSeed_defect]; norm_num

theorem replicatedSeed_defect_two : (replicatedSeed 2).defect (movedNorm (Fin 3)) = 64 := by
  rw [replicatedSeed_defect]; norm_num

theorem replicatedSeed_defect_three : (replicatedSeed 3).defect (movedNorm (Fin 3)) = 216 := by
  rw [replicatedSeed_defect]; norm_num

theorem replicatedSeed_gaugeDist_one : (replicatedSeed 1).gaugeDist (movedNorm (Fin 3)) = 6 := by
  rw [replicatedSeed_gaugeDist]; norm_num

theorem replicatedSeed_gaugeDist_two : (replicatedSeed 2).gaugeDist (movedNorm (Fin 3)) = 24 := by
  rw [replicatedSeed_gaugeDist]; norm_num

theorem replicatedSeed_gaugeDist_three : (replicatedSeed 3).gaugeDist (movedNorm (Fin 3)) = 54 := by
  rw [replicatedSeed_gaugeDist]; norm_num

theorem replicatedSeed_ratio_one :
    (replicatedSeed 1).defect (movedNorm (Fin 3)) /
        (replicatedSeed 1).gaugeDist (movedNorm (Fin 3)) = 4 / 3 := by
  rw [replicatedSeed_defect_one, replicatedSeed_gaugeDist_one]
  norm_num

theorem replicatedSeed_ratio_two :
    (replicatedSeed 2).defect (movedNorm (Fin 3)) /
        (replicatedSeed 2).gaugeDist (movedNorm (Fin 3)) = 8 / 3 := by
  rw [replicatedSeed_defect_two, replicatedSeed_gaugeDist_two]
  norm_num

theorem replicatedSeed_ratio_three :
    (replicatedSeed 3).defect (movedNorm (Fin 3)) /
        (replicatedSeed 3).gaugeDist (movedNorm (Fin 3)) = 4 := by
  rw [replicatedSeed_defect_three, replicatedSeed_gaugeDist_three]
  norm_num

/-- The upper bound when `card V = 4 q`. -/
private theorem h1_complete_le_of_card_eq_four_mul {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hq : 0 < q) (hV : Fintype.card V = 4 * q) :
    h1 (complete V) (movedNorm (Fin 3)) ≤ (Fintype.card V : ℝ) / 3 := by
  rw [h1_complete_eq_of_card_eq isConjInvariant_movedNorm (W := Fin 4 ×ₗ Fin q)
    (by rw [hV, Fintype.card_lex, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin])]
  have hgd := six_mul_sq_le_gaugeDist_lex q
  have hpos : (0 : ℝ) < 6 * q ^ 2 := by positivity
  refine (h1_le_div (hpos.trans_le hgd)).trans ?_
  rw [Cochain.defect_ofLt_lex, defect_w4, Fintype.card_fin, hV]
  calc (q : ℝ) ^ 3 * 8 / _ ≤ (q : ℝ) ^ 3 * 8 / (6 * q ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hpos hgd
    _ = ((4 * q : ℕ) : ℝ) / 3 := by
        have hq' : (q : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
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
  · exact Sym3.h1_complete_le_of_card_eq_four_mul (by omega) hq
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
