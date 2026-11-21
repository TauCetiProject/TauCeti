/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Invariance
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unequal-degree thresholds, arbitrary-vertex replication, and staircase cross-degree bounds

Comparing a degree-`n` permutation cochain against a vertex gauge of unequal degree `m ≠ n` incurs
at least `1 / (n + 1)` per edge (`1 / 4` when `n = 3`, with sharper bounds `1 / 3` at `m = 2` and
`1 - 3 / m` for `5 ≤ m`). Whenever the equal-degree gauge-cost infimum lies at or below this
unequal-degree baseline, no gauge in a different symmetric group can beat the cochain's own degree.
This file develops that threshold principle and applies it—together with relabelling invariance—to
both families of complete-complex extremizers:

* **Unequal-degree threshold exactness**
  (`Finset.ciInf_sum_distErr_mul_inv_le_of_le_card_div_add_one`,
  `Finset.ciInf₂_sum_distErr_mul_inv_eq_ciInf_of_le_card_div_add_one`, and
  `Finset.ciInf₂_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div_of_le`): on any finite edge set `E`,
  if the equal-degree `movedNorm (Fin n)` gauge-cost infimum (`2 ≤ n`) is at most `n * #E / (n + 1)`
  (`3 * #E / 4` when `n = 3`), then the global cross-degree infimum over all `m + 2 ≥ 2` equals
  `1 / n` times the equal-degree `movedNorm (Fin n)` infimum.
* **Arbitrary-vertex-type cluster replication and multiples of four**
  (`Equiv.ciInf_sum_filter_lt_distErr_prod`,
  `Equiv.ciInf₂_sum_filter_lt_distErr_prod_eq_card_sq_mul_ciInf_of_le_of_forall_le`,
  `Equiv.ciInf₂_sum_filter_lt_distErr_fin_four_prod_of_eq_setOf_isSwap`, and
  `TauCeti.exists_equiv_fin_four_prod_ciInf₂_sum_distErr_eq_card_sq_div_eight`): pulling the
  cluster replication of a skew-symmetric degree-`n` assignment on `U` back along any bijection
  `e : V ≃ U × ι` (requiring neither order preservation of `e` nor any order on `ι`) adds the
  within-cluster mismatch correction to `Fintype.card ι ^ 2` times the base infimum, and for
  `2 ≤ n` multiplies the global cross-degree infimum by `Fintype.card ι ^ 2` whenever the base
  labels attain their cross-degree infimum at degree `n`, giving exact infimum
  `Fintype.card V ^ 2 / 8` for skew-symmetric replicated `Fin 4` three-transposition seeds whenever
  `4 ∣ Fintype.card V`.
* **Staircase cross-degree comparison at `Fintype.card V = q * (2 * t + 1)`**
  (`TauCeti.mul_two_mul_add_one_choose_two_div_four_sub`,
  `TauCeti.sq_mul_mul_add_one_div_three_lt_choose_two_div_four`,
  `TauCeti.sq_mul_mul_add_one_div_three_le_choose_two_div_four`,
  `TauCeti.sq_mul_mul_add_one_div_three_lt_ciInf_sum_distErr_three_of_ne`,
  `TauCeti.ciInf₂_sum_distErr_three_eq_ciInf_sum_movedNorm_div_three_of_card_eq`, and
  `TauCeti.ciInf₂_sum_distErr_three_eq_sq_mul_mul_add_one_div_three_of_card_eq`): the slack between
  the complete-graph `1 / 4` baseline `((q * (2 * t + 1)).choose 2 : ℝ) / 4` and the degree-`3`
  staircase cross-degree gauge cost `D₃ = q ^ 2 * t * (t + 1) / 3` equals
  `q * (q * (4 * t ^ 2 + 4 * t + 3) - (6 * t + 3)) / 24`, which is nonnegative for all `q, t : ℕ`
  and strictly positive whenever `1 ≤ q` and `1 ≤ t`. Hence every degree-`3` assignment on `V` of
  `movedNorm (Fin 3)` gauge-cost infimum at most `q ^ 2 * t * (t + 1)` attains its global
  cross-degree infimum at degree `3`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Section 3.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, Proposition 10.
-/

public section

open Finset

namespace Finset

open Equiv Equiv.Perm TauCeti

variable {V : Type*} {n : ℕ}

/-! ### Unequal-degree threshold exactness -/

/-- Whenever the equal-degree `distErr` gauge-cost infimum on `E` is at most `#E / (n + 1)`, it is a
lower bound for the degree-`m` gauge-cost infimum in every degree `m : ℕ`. -/
theorem ciInf_sum_distErr_mul_inv_le_of_le_card_div_add_one (E : Finset (V × V))
    (α : V → V → Perm (Fin n))
    (hle : (⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤
      (#E : ℝ) / (n + 1))
    (m : ℕ) :
    (⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤
      ⨅ β : V → Perm (Fin m), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  rcases eq_or_ne m n with rfl | hmn
  · exact le_rfl
  · refine le_ciInf fun β => hle.trans ?_
    exact E.card_div_add_one_le_sum_distErr_of_ne (fun e => α e.1 e.2)
      (fun e => β e.1 * (β e.2)⁻¹) hmn.symm

/-- When `2 ≤ n` and the equal-degree `distErr` gauge-cost infimum on `E` is at most `#E / (n + 1)`,
the global cross-degree infimum over all gauge degrees `m + 2 ≥ 2` equals the equal-degree infimum.
-/
theorem ciInf₂_sum_distErr_mul_inv_eq_ciInf_of_le_card_div_add_one (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (hn : 2 ≤ n)
    (hle : (⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤
      (#E : ℝ) / (n + 1)) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      ⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) :=
  le_antisymm (E.ciInf₂_sum_distErr_mul_inv_le_ciInf_of_le α hn)
    (le_ciInf fun m => E.ciInf_sum_distErr_mul_inv_le_of_le_card_div_add_one α hle (m + 2))

/-- When `2 ≤ n` and the equal-degree `movedNorm (Fin n)` gauge-cost infimum on `E` is at most
`n * #E / (n + 1)`, the global cross-degree infimum over all `m + 2 ≥ 2` equals `1 / n` times the
`movedNorm (Fin n)` infimum. -/
theorem ciInf₂_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div_of_le (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (hn : 2 ≤ n)
    (hle : (⨅ β : V → Perm (Fin n),
        ∑ e ∈ E, movedNorm (Fin n) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) ≤
      (n : ℝ) * #E / (n + 1)) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      (⨅ β : V → Perm (Fin n),
        ∑ e ∈ E, movedNorm (Fin n) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) / n := by
  have : NeZero n := ⟨by omega⟩
  have hn_pos : (0 : ℝ) < n := by positivity
  have hle' : (⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤
      (#E : ℝ) / (n + 1) := by
    rw [E.ciInf_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div α, div_le_iff₀ hn_pos]
    exact hle.trans_eq (by ring)
  rw [E.ciInf₂_sum_distErr_mul_inv_eq_ciInf_of_le_card_div_add_one α hn hle',
    E.ciInf_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div α]

end Finset

/-! ### Arbitrary-vertex-type cluster replication and multiples of four -/

namespace Equiv

open Equiv.Perm TauCeti

/-- Replicating a skew-symmetric assignment along `U ×ₗ ι` with identity labels inside each
cluster preserves skew-symmetry. -/
private theorem if_ofLex_fst_eq_inv {U ι : Type*} [DecidableEq U] {n : ℕ}
    (α : U → U → Perm (Fin n)) (hα : ∀ u v : U, u ≠ v → α v u = (α u v)⁻¹)
    (x y : U ×ₗ ι) (_ : x ≠ y) :
    (if (ofLex y).1 = (ofLex x).1 then 1 else α (ofLex y).1 (ofLex x).1) =
      (if (ofLex x).1 = (ofLex y).1 then 1 else α (ofLex x).1 (ofLex y).1)⁻¹ := by
  by_cases h1 : (ofLex x).1 = (ofLex y).1
  · simp [h1]
  · simp [h1, Ne.symm h1, hα (ofLex x).1 (ofLex y).1 h1]

/-- Pulling the cluster replication of a skew-symmetric assignment on `U` (with identity labels
inside each cluster `{u} × ι`) back along an arbitrary bijection `e : V ≃ U × ι`—requiring neither
order preservation of `e` nor any linear order on `ι`—gives exact degree-`m` cross-degree
gauge-cost infimum equal to the within-cluster correction
`(Fintype.card U * (Fintype.card ι).choose 2) * (1 - min n m / max n m)` plus `Fintype.card ι ^ 2`
times the base degree-`m` infimum on `U`. -/
theorem ciInf_sum_filter_lt_distErr_prod {V U ι : Type*} [Fintype V] [LinearOrder V]
    [Fintype U] [LinearOrder U] [Fintype ι] {n : ℕ} (e : V ≃ U × ι) (α : U → U → Perm (Fin n))
    (hα : ∀ u v : U, u ≠ v → α v u = (α u v)⁻¹) (m : ℕ) :
    (⨅ β : V → Perm (Fin m),
        ∑ p : V × V with p.1 < p.2,
          distErr (if (e p.1).1 = (e p.2).1 then 1 else α (e p.1).1 (e p.2).1)
            (β p.1 * (β p.2)⁻¹)) =
      (Fintype.card U * (Fintype.card ι).choose 2 : ℕ) * (1 - (min n m : ℝ) / max n m) +
        (Fintype.card ι : ℝ) ^ 2 *
          ⨅ β₀ : U → Perm (Fin m),
            ∑ p : U × U with p.1 < p.2, distErr (α p.1 p.2) (β₀ p.1 * (β₀ p.2)⁻¹) := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hrel := (e.trans toLex).ciInf_sum_filter_lt_distErr_mul_inv
    (fun x y : U ×ₗ ι => if (ofLex x).1 = (ofLex y).1 then 1 else α (ofLex x).1 (ofLex y).1)
    (if_ofLex_fst_eq_inv α hα) m
  dsimp only [trans_apply, ofLex_toLex] at hrel
  exact hrel.trans (ciInf_sum_distErr_lex (V := U) (ι := ι) α m)

/-- Whenever a skew-symmetric degree-`n` assignment (`2 ≤ n`) on `U` attains its global cross-degree
infimum over `m + 2 ≥ 2` at its own degree `n`, pulling its cluster replication on `U × ι` back
along any bijection `e : V ≃ U × ι` multiplies the global cross-degree infimum by
`Fintype.card ι ^ 2`. -/
theorem ciInf₂_sum_filter_lt_distErr_prod_eq_card_sq_mul_ciInf_of_le_of_forall_le
    {V U ι : Type*} [Fintype V] [LinearOrder V] [Fintype U] [LinearOrder U] [Fintype ι] {n : ℕ}
    (e : V ≃ U × ι) (α : U → U → Perm (Fin n))
    (hα : ∀ u v : U, u ≠ v → α v u = (α u v)⁻¹) (hn : 2 ≤ n)
    (hmin : ∀ m : ℕ,
      (⨅ β₀ : U → Perm (Fin n),
          ∑ p : U × U with p.1 < p.2, distErr (α p.1 p.2) (β₀ p.1 * (β₀ p.2)⁻¹)) ≤
        ⨅ β₀ : U → Perm (Fin (m + 2)),
          ∑ p : U × U with p.1 < p.2, distErr (α p.1 p.2) (β₀ p.1 * (β₀ p.2)⁻¹)) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ p : V × V with p.1 < p.2,
          distErr (if (e p.1).1 = (e p.2).1 then 1 else α (e p.1).1 (e p.2).1)
            (β p.1 * (β p.2)⁻¹)) =
      (Fintype.card ι : ℝ) ^ 2 *
        ⨅ β₀ : U → Perm (Fin n),
          ∑ p : U × U with p.1 < p.2, distErr (α p.1 p.2) (β₀ p.1 * (β₀ p.2)⁻¹) := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hrel := (e.trans toLex).ciInf₂_sum_filter_lt_distErr_mul_inv
    (fun x y : U ×ₗ ι => if (ofLex x).1 = (ofLex y).1 then 1 else α (ofLex x).1 (ofLex y).1)
    (if_ofLex_fst_eq_inv α hα)
  dsimp only [trans_apply, ofLex_toLex] at hrel
  exact hrel.trans
    (ciInf₂_sum_distErr_lex_eq_card_sq_mul_ciInf_of_le_of_forall_le (V := U) (ι := ι) α hn hmin)

/-- Pulling the cluster replication of a skew-symmetric three-transposition seed on `Fin 4` back
along an arbitrary bijection `e : V ≃ Fin 4 × ι` (requiring neither order preservation of `e` nor
any `Fintype` or `LinearOrder` structure on `ι`) yields exact cross-degree gauge-cost infimum
`Fintype.card V ^ 2 / 8` across all gauge degrees `m + 2 ≥ 2`. -/
theorem ciInf₂_sum_filter_lt_distErr_fin_four_prod_of_eq_setOf_isSwap
    {V ι : Type*} [Fintype V] [LinearOrder V] (e : V ≃ Fin 4 × ι)
    (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (hα : ∀ u v : Fin 4, u ≠ v → α v u = (α u v)⁻¹)
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ p : V × V with p.1 < p.2,
          distErr (if (e p.1).1 = (e p.2).1 then 1 else α (e p.1).1 (e p.2).1)
            (β p.1 * (β p.2)⁻¹)) =
      (Fintype.card V : ℝ) ^ 2 / 8 := by
  have : Finite (Fin 4 × ι) := Finite.of_equiv V e
  have : Finite ι :=
    Finite.of_injective (fun i : ι => ((0 : Fin 4), i)) fun _ _ h => (Prod.mk.inj h).2
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hrel := (e.trans toLex).ciInf₂_sum_filter_lt_distErr_mul_inv
    (fun x y : Fin 4 ×ₗ ι => if (ofLex x).1 = (ofLex y).1 then 1 else α (ofLex x).1 (ofLex y).1)
    (if_ofLex_fst_eq_inv α hα)
  dsimp only [trans_apply, ofLex_toLex] at hrel
  have hcard : Fintype.card V = 4 * Fintype.card ι := by
    simpa [Fintype.card_prod] using Fintype.card_congr e
  refine hrel.trans ?_
  rw [ciInf₂_sum_distErr_lex_fin_four_of_eq_setOf_isSwap α h0 hswaps, hcard,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

end Equiv

namespace TauCeti

open Equiv Equiv.Perm

/-- When `4 ∣ Fintype.card V`, any skew-symmetric three-transposition seed on `Fin 4` admits a
replicated pullback along a bijection `e : V ≃ Fin 4 × Fin (Fintype.card V / 4)` with global
cross-degree gauge-cost infimum `Fintype.card V ^ 2 / 8`. -/
theorem exists_equiv_fin_four_prod_ciInf₂_sum_distErr_eq_card_sq_div_eight
    {V : Type*} [Fintype V] [LinearOrder V] (h4 : 4 ∣ Fintype.card V)
    (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (hα : ∀ u v : Fin 4, u ≠ v → α v u = (α u v)⁻¹)
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    ∃ e : V ≃ Fin 4 × Fin (Fintype.card V / 4),
      (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
          ∑ p : V × V with p.1 < p.2,
            distErr (if (e p.1).1 = (e p.2).1 then 1 else α (e p.1).1 (e p.2).1)
              (β p.1 * (β p.2)⁻¹)) =
        (Fintype.card V : ℝ) ^ 2 / 8 := by
  have hcard : Fintype.card V = Fintype.card (Fin 4 × Fin (Fintype.card V / 4)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  exact ⟨Fintype.equivOfCardEq hcard,
    (Fintype.equivOfCardEq hcard).ciInf₂_sum_filter_lt_distErr_fin_four_prod_of_eq_setOf_isSwap
      α hα h0 hswaps⟩

/-! ### Staircase cross-degree comparison at `q * (2 * t + 1)` -/

/-- For `1 ≤ q` and `1 ≤ t`, the staircase polynomial inequality
`6 * t + 3 + 2 * q ≤ q * (4 * t ^ 2 + 4 * t + 3)` holds in `ℕ`. -/
private theorem six_mul_add_three_add_two_mul_le {q t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) :
    6 * t + 3 + 2 * q ≤ q * (4 * t ^ 2 + 4 * t + 3) := by
  rcases Nat.exists_eq_add_of_le' hq with ⟨q', rfl⟩
  rcases Nat.exists_eq_add_of_le' ht with ⟨t', rfl⟩
  nlinarith

/-- Exact algebraic identity for the slack between the complete-graph `1 / 4` unequal-degree
baseline on `q * (2 * t + 1)` vertices and the degree-`3` staircase cross-degree gauge cost
`q ^ 2 * t * (t + 1) / 3`. -/
theorem mul_two_mul_add_one_choose_two_div_four_sub (q t : ℕ) :
    ((q * (2 * t + 1)).choose 2 : ℝ) / 4 - (q : ℝ) ^ 2 * t * (t + 1) / 3 =
      (q : ℝ) * ((q : ℝ) * (4 * (t : ℝ) ^ 2 + 4 * t + 3) - (6 * t + 3)) / 24 := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

/-- When `1 ≤ q` and `1 ≤ t`, the complete-graph `1 / 4` baseline on `q * (2 * t + 1)` vertices
strictly exceeds the degree-`3` staircase cross-degree gauge cost `q ^ 2 * t * (t + 1) / 3`. -/
theorem sq_mul_mul_add_one_div_three_lt_choose_two_div_four {q t : ℕ}
    (hq : 1 ≤ q) (ht : 1 ≤ t) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 < ((q * (2 * t + 1)).choose 2 : ℝ) / 4 := by
  have hpoly : ((6 * t + 3 + 2 * q : ℕ) : ℝ) ≤ ((q * (4 * t ^ 2 + 4 * t + 3) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (six_mul_add_three_add_two_mul_le hq ht)
  push_cast at hpoly
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsub := mul_two_mul_add_one_choose_two_div_four_sub q t
  nlinarith

/-- For all `q, t : ℕ` (including `q = 0` and `t = 0`), the degree-`3` staircase cross-degree gauge
cost `q ^ 2 * t * (t + 1) / 3` is at most the `1 / 4` complete-graph baseline
`((q * (2 * t + 1)).choose 2 : ℝ) / 4`. -/
theorem sq_mul_mul_add_one_div_three_le_choose_two_div_four (q t : ℕ) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 ≤ ((q * (2 * t + 1)).choose 2 : ℝ) / 4 := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rcases eq_or_ne t 0 with rfl | ht0
  · simp only [Nat.cast_zero, mul_zero, zero_add, mul_one, zero_div]
    positivity
  exact (sq_mul_mul_add_one_div_three_lt_choose_two_div_four
    (Nat.pos_of_ne_zero hq0) (Nat.pos_of_ne_zero ht0)).le

section StaircaseGraph

variable {V : Type*} [Fintype V] [LinearOrder V] {q t m : ℕ}

/-- On `Fintype.card V = q * (2 * t + 1)` vertices with `1 ≤ q` and `1 ≤ t`, every unequal-degree
(`m ≠ 3`) vertex gauge `β : V → Perm (Fin m)` against any degree-`3` assignment has complete-graph
cross-degree pair cost strictly greater than `q ^ 2 * t * (t + 1) / 3`. -/
theorem sq_mul_mul_add_one_div_three_lt_sum_distErr_three_of_ne
    (hcard : Fintype.card V = q * (2 * t + 1)) (hq : 1 ≤ q) (ht : 1 ≤ t)
    (α : V → V → Perm (Fin 3)) (β : V → Perm (Fin m)) (hm : m ≠ 3) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 <
      ∑ e : V × V with e.1 < e.2, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  have hlt := sq_mul_mul_add_one_div_three_lt_choose_two_div_four hq ht
  have hbase := (univ.filter fun p : V × V => p.1 < p.2).card_div_four_le_sum_distErr_three_of_ne
    (fun e => α e.1 e.2) (fun e => β e.1 * (β e.2)⁻¹) hm
  rw [Fintype.card_product_filter_lt, hcard] at hbase
  exact hlt.trans_le hbase

/-- On `Fintype.card V = q * (2 * t + 1)` vertices with `1 ≤ q` and `1 ≤ t`, the degree-`m`
(`m ≠ 3`) cross-degree gauge-cost infimum of any degree-`3` assignment strictly exceeds
`q ^ 2 * t * (t + 1) / 3`. -/
theorem sq_mul_mul_add_one_div_three_lt_ciInf_sum_distErr_three_of_ne
    (hcard : Fintype.card V = q * (2 * t + 1)) (hq : 1 ≤ q) (ht : 1 ≤ t)
    (α : V → V → Perm (Fin 3)) (hm : m ≠ 3) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 <
      ⨅ β : V → Perm (Fin m),
        ∑ e : V × V with e.1 < e.2, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  obtain ⟨β₀, hβ₀⟩ :=
    (univ.filter fun p : V × V => p.1 < p.2).exists_eq_ciInf_sum_distErr_mul_inv α m
  rw [← hβ₀]
  exact sq_mul_mul_add_one_div_three_lt_sum_distErr_three_of_ne hcard hq ht α β₀ hm

/-- For every `q, t : ℕ`, if `Fintype.card V = q * (2 * t + 1)` and `α : V → V → Perm (Fin 3)` has
`movedNorm (Fin 3)` complete-graph gauge-cost infimum at most `q ^ 2 * t * (t + 1)`, then its global
cross-degree gauge-cost infimum over all `m + 2 ≥ 2` equals `1 / 3` times its `movedNorm (Fin 3)`
infimum. -/
theorem ciInf₂_sum_distErr_three_eq_ciInf_sum_movedNorm_div_three_of_card_eq
    (hcard : Fintype.card V = q * (2 * t + 1)) (α : V → V → Perm (Fin 3))
    (hle : (⨅ β : V → Perm (Fin 3),
        ∑ e : V × V with e.1 < e.2, movedNorm (Fin 3) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) ≤
      (q : ℝ) ^ 2 * t * (t + 1)) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e : V × V with e.1 < e.2, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      (⨅ β : V → Perm (Fin 3),
        ∑ e : V × V with e.1 < e.2, movedNorm (Fin 3) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) / 3 := by
  have h := (univ.filter fun p : V × V => p.1 < p.2
    ).ciInf₂_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div_of_le α (by decide) ?_
  · simpa only [Nat.cast_ofNat] using h
  · rw [Fintype.card_product_filter_lt, hcard]
    have hbase := sq_mul_mul_add_one_div_three_le_choose_two_div_four q t
    rw [Nat.cast_ofNat]
    linarith

/-- Exact cross-degree gauge-cost evaluation `q ^ 2 * t * (t + 1) / 3` for any degree-`3` assignment
on `Fintype.card V = q * (2 * t + 1)` vertices whose `movedNorm (Fin 3)` gauge-cost infimum equals
`q ^ 2 * t * (t + 1)`. -/
theorem ciInf₂_sum_distErr_three_eq_sq_mul_mul_add_one_div_three_of_card_eq
    (hcard : Fintype.card V = q * (2 * t + 1)) (α : V → V → Perm (Fin 3))
    (heq : (⨅ β : V → Perm (Fin 3),
        ∑ e : V × V with e.1 < e.2, movedNorm (Fin 3) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) =
      (q : ℝ) ^ 2 * t * (t + 1)) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e : V × V with e.1 < e.2, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      (q : ℝ) ^ 2 * t * (t + 1) / 3 := by
  rw [ciInf₂_sum_distErr_three_eq_ciInf_sum_movedNorm_div_three_of_card_eq hcard α heq.le, heq]

end StaircaseGraph

end TauCeti

end
