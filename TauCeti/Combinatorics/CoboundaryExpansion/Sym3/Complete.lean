/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.StarBound
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Staircase
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
For the upper bound, every `k ≥ 3` is `4 q` or `(2 t + 1) q` with
`t, q ≥ 1`. The seeds are a private `k = 4` witness (defect `8`, every gauge costs at least `6`,
checked by `decide +kernel`) and Kozlov's staircase `Sym3.stair (2 t + 1)` (defect
`t (t + 1) (2 t + 1) / 3`, every gauge costs at least `t (t + 1)`). Balanced replication multiplies
the defect by `q ^ 3` and the gauge lower bound by `q ^ 2`, so `K_k` carries a cochain with
`3 N ≤ k D` and `0 < D`, and `h1_le_div` applies.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, Zenodo, doi:10.5281/zenodo.22090958, Corollary 7 and Theorem 8.
* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136,
  Definition 3.2 (staircase graphs), Lemma 3.8 and Corollary 3.13 (cut-minimality).
-/

public section

open Equiv Equiv.Perm TauCeti.TwoComplex

namespace TauCeti

namespace Sym3

/-- The `k = 4` seed: `t12`, `t01`, `t02` on the edges `{1, 2}`, `{1, 3}`, `{2, 3}` and `1` on the
other edges. -/
private def w4 (u v : Fin 4) : S3 :=
  if u = 1 ∧ v = 2 then t12 else if u = 1 ∧ v = 3 then t01 else if u = 2 ∧ v = 3 then t02 else 1

private theorem defect_w4 : defect w4 = 8 := by decide +kernel

private theorem cost_w4_ge (β : Fin 4 → S3) : 6 ≤ cost w4 β :=
  cost_ge_of_forall_cons_one w4 6 (by decide +kernel) β

/-- Every `k ≥ 3` is `4 q` or `(2 t + 1) q` with `t ≥ 1` and `q ≥ 1`. -/
private theorem exists_mul_eq (n : ℕ) : ∀ k, k ≤ n → 3 ≤ k →
    ∃ m q, 0 < q ∧ k = m * q ∧ (m = 4 ∨ ∃ t, 1 ≤ t ∧ m = 2 * t + 1) := by
  induction n with
  | zero => intro k hk h3; omega
  | succ n ih =>
    intro k hk h3
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨t, ht⟩
    · by_cases hj2 : j = 2
      · exact ⟨4, 1, by norm_num, by omega, Or.inl rfl⟩
      · obtain ⟨m, q, hq, hjm, hm⟩ := ih j (by omega) (by omega)
        exact ⟨m, 2 * q, by omega, by rw [hj, hjm]; ring, hm⟩
    · exact ⟨k, 1, by norm_num, by ring, Or.inr ⟨t, by omega, ht⟩⟩

/-- For every `k ≥ 3`, some `Sym(3)` cochain on `K_k` has a positive gauge lower bound `D` with
`3 N ≤ k D`. -/
private theorem exists_seed (k : ℕ) (hk : 3 ≤ k) : ∃ (α : Fin k → Fin k → S3) (D : ℕ),
    0 < D ∧ (∀ β, D ≤ cost α β) ∧ 3 * defect α ≤ k * D := by
  obtain ⟨m, q, hq, rfl, hm⟩ := exists_mul_eq k k le_rfl hk
  obtain ⟨α, D, hD, hcost, hN⟩ : ∃ (α : Fin m → Fin m → S3) (D : ℕ),
      0 < D ∧ (∀ β, D ≤ cost α β) ∧ 3 * defect α ≤ m * D := by
    rcases hm with rfl | ⟨t, ht, rfl⟩
    · exact ⟨w4, 6, by norm_num, cost_w4_ge, by rw [defect_w4]⟩
    · exact ⟨stair (2 * t + 1), t * (t + 1), Nat.mul_pos (by omega) (by omega),
        stair_cost_lower t, (stair_defect_mul t).le⟩
  refine ⟨rep q α, q ^ 2 * D, Nat.mul_pos (pow_pos hq 2) hD, cost_rep_ge α D hcost, ?_⟩
  rw [defect_rep]
  calc 3 * (q ^ 3 * defect α) = q ^ 3 * (3 * defect α) := by ring
    _ ≤ q ^ 3 * (m * D) := Nat.mul_le_mul_left _ hN
    _ = m * q * (q ^ 2 * D) := by ring

end Sym3

/-- The upper bound on `K_k` for every `k ≥ 3`. -/
private theorem h1_complete_fin_le (k : ℕ) (hk : 3 ≤ k) :
    h1 (complete (Fin k)) (movedNorm (Fin 3)) ≤ (k : ℝ) / 3 := by
  obtain ⟨α, D, hD, hcost, hN⟩ := Sym3.exists_seed k hk
  set c := Cochain.ofLt (complete (Fin k)) α
  have hDc : (D : ℝ) ≤ c.gaugeDist (movedNorm (Fin 3)) :=
    (c.le_gaugeDist_iff _).mpr fun β => by rw [Sym3.cost_ofLt]; exact_mod_cast hcost β
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  refine (h1_le_div (hD'.trans_le hDc)).trans ?_
  rw [Sym3.defect_ofLt]
  refine (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hD' hDc).trans ?_
  rw [div_le_div_iff₀ hD' (by norm_num)]
  exact_mod_cast (by omega : Sym3.defect α * 3 ≤ k * D)

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The permutation coboundary constant of the complete complex is `k/3` for every `k ≥ 3`,
attained with values in `Sym(3)` (Beasley, Theorem 8, stated there for `k ≥ 4`; the same seeds
cover `k = 3`). -/
theorem h1_complete_movedNorm_fin_three (hV : 3 ≤ Fintype.card V) :
    h1 (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / 3 := by
  refine le_antisymm ?_ (card_div_three_le_h1_of_nontrivial hV _ isConjInvariant_movedNorm)
  rw [h1_complete_eq_of_card_eq isConjInvariant_movedNorm (Fintype.card_fin _).symm]
  exact h1_complete_fin_le _ hV

/-- The same constant in the normalized convention:
`(k choose 2) / (k choose 3) · k/3 = k/(k-2)` for every `k ≥ 3`. -/
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

end TauCeti
