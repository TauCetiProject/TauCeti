/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Invariance
public import TauCeti.Combinatorics.CoboundaryExpansion.Replication
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.CoboundaryExpansion.StarBound

/-!
# Unequal-degree thresholds, arbitrary-vertex replication, and staircase cross-degree bounds

Comparing a degree-`n` permutation cochain against a vertex gauge of unequal degree `m ≠ n` incurs
at least `1 / (n + 1)` per edge (`1 / 4` when `n = 3`, with sharper bounds `1 / 3` at `m = 2` and
`1 - 3 / m` for `5 ≤ m`). Whenever the equal-degree gauge-cost infimum lies at or below this
unequal-degree baseline, no gauge in a different symmetric group can beat the cochain's own degree.
This file develops that threshold principle and applies it—together with relabelling invariance—to
both `Finset`/`Equiv` pair sums and `TauCeti.Cochain` / `TauCeti.h1Err`:

* **Unequal-degree threshold exactness**
  (`Finset.ciInf_sum_distErr_mul_inv_le_of_le_card_div_add_one`,
  `Finset.ciInf₂_sum_distErr_mul_inv_eq_ciInf_of_le_card_div_add_one`,
  `Finset.ciInf₂_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div_of_le`, and
  `TauCeti.Cochain.gaugeDistErr_eq_gaugeDist_div_of_le`): on any two-complex `X`, if the
  equal-degree `movedNorm (Fin n)` gauge distance (`2 ≤ n`) is at most `n * #X.edges / (n + 1)`
  (`3 * #X.edges / 4` when `n = 3`), then `α.gaugeDistErr = α.gaugeDist (movedNorm (Fin n)) / n`.
* **Cross-degree star bound on the complete complex** (`TauCeti.Cochain.card_mul_gaugeDistErr_le`,
  `TauCeti.Cochain.card_div_three_le_defect_div_gaugeDistErr`,
  `TauCeti.card_div_three_le_h1Err_of_exists`, and `TauCeti.card_div_three_le_h1Err`): using the
  cochain's own degree `n ≥ 2` and the star bound in `movedNorm (Fin n)`, every degree-`n` cochain
  on `complete V` satisfies `card V * α.gaugeDistErr ≤ 3 * (α.defect (movedNorm (Fin n)) / n)`,
  so `(Fintype.card V : ℝ) / 3 ≤ h1Err (complete V)` whenever `3 ≤ Fintype.card V`.
* **Arbitrary-vertex-type cluster replication and multiples of four**
  (`Equiv.ciInf_sum_filter_lt_distErr_prod`,
  `Equiv.ciInf₂_sum_filter_lt_distErr_prod_eq_card_sq_mul_ciInf_of_le_of_forall_le`,
  `Equiv.ciInf₂_sum_filter_lt_distErr_fin_four_prod_of_eq_setOf_isSwap`,
  `TauCeti.exists_equiv_fin_four_prod_ciInf₂_sum_distErr_eq_card_sq_div_eight`,
  `TauCeti.Cochain.gaugeDistErr_replicate_of_forall_le`, and
  `TauCeti.Cochain.gaugeDistErr_fin_four_of_eq_setOf_isSwap`): pulling the cluster replication of a
  skew-symmetric degree-`n` assignment on `U` back along any bijection `e : V ≃ U × ι` (requiring
  neither order preservation of `e` nor any order on `ι`) adds
  `(Fintype.card U * (Fintype.card ι).choose 2) * (1 - min n m / max n m)` to `Fintype.card ι ^ 2`
  times the base infimum, and for `2 ≤ n` multiplies the global cross-degree infimum by
  `Fintype.card ι ^ 2` whenever the base labels attain their cross-degree infimum at degree `n`,
  giving exact infimum `Fintype.card V ^ 2 / 8` for skew-symmetric replicated `Fin 4`
  three-transposition seeds whenever `4 ∣ Fintype.card V`.
* **Staircase threshold comparison at `Fintype.card V = q * (2 * t + 1)`**
  (`TauCeti.mul_two_mul_add_one_choose_two_div_four_sub`,
  `TauCeti.sq_mul_mul_add_one_div_three_lt_choose_two_div_four`,
  `TauCeti.sq_mul_mul_add_one_div_three_le_choose_two_div_four`,
  `TauCeti.sq_mul_mul_add_one_div_three_lt_ciInf_sum_distErr_three_of_ne`,
  `TauCeti.ciInf₂_sum_distErr_three_eq_ciInf_sum_movedNorm_div_three_of_card_eq`,
  `TauCeti.Cochain.sq_mul_mul_add_one_div_three_lt_ciInf_costErr_three_of_ne`, and
  `TauCeti.Cochain.gaugeDistErr_eq_gaugeDist_div_three_of_card_eq`): the slack between the
  complete-graph `1 / 4` baseline `((q * (2 * t + 1)).choose 2 : ℝ) / 4` and the explicit threshold
  `q ^ 2 * t * (t + 1) / 3` equals `q * (q * (4 * t ^ 2 + 4 * t + 3) - (6 * t + 3)) / 24`, which is
  nonnegative for all `q, t : ℕ` and strictly positive whenever `1 ≤ q` and `1 ≤ t`. Hence every
  degree-`3` cochain on `complete V` whose `movedNorm (Fin 3)` gauge distance is at most
  `q ^ 2 * t * (t + 1)` has `α.gaugeDistErr = α.gaugeDist (movedNorm (Fin 3)) / 3` (on Kozlov's
  staircase graph witness in `Sym3/Staircase.lean`,
  `h1_complete_movedNorm_fin_three_le_of_card_eq_mul` already bounds
  `h1 (complete V) (movedNorm (Fin 3))` above by `card V / 3`).

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

/-- Transporting the fixed-degree replicated cross-degree infimum on `V` along `e.trans toLex`
to the lexicographic product `U ×ₗ ι`. -/
private theorem ciInf_sum_filter_lt_distErr_prod_eq_lex
    {V U ι : Type*} [Fintype V] [LinearOrder V] [Fintype U] [LinearOrder U]
    [Fintype ι] [LinearOrder ι] {n : ℕ} (e : V ≃ U × ι) (α : U → U → Perm (Fin n))
    (hα : ∀ u v : U, u ≠ v → α v u = (α u v)⁻¹) (m : ℕ) :
    (⨅ β : V → Perm (Fin m),
        ∑ p : V × V with p.1 < p.2,
          distErr (if (e p.1).1 = (e p.2).1 then 1 else α (e p.1).1 (e p.2).1)
            (β p.1 * (β p.2)⁻¹)) =
      ⨅ β : (U ×ₗ ι) → Perm (Fin m),
        ∑ p : (U ×ₗ ι) × (U ×ₗ ι) with p.1 < p.2,
          distErr (if (ofLex p.1).1 = (ofLex p.2).1 then 1 else α (ofLex p.1).1 (ofLex p.2).1)
            (β p.1 * (β p.2)⁻¹) := by
  let γ₀ : Cochain (TwoComplex.complete (U ×ₗ ι)) (Perm (Fin n)) :=
    Cochain.ofFn (TwoComplex.complete (U ×ₗ ι))
      (fun x y => if (ofLex x).1 = (ofLex y).1 then 1 else α (ofLex x).1 (ofLex y).1)
      fun x y _ => by
        by_cases h1 : (ofLex x).1 = (ofLex y).1
        · simp [h1]
        · simp [h1, Ne.symm h1, hα _ _ h1]
  have hrel := γ₀.ciInf_costErr_relabelComplete (e.trans toLex).symm m
  have hL (β : V → Perm (Fin m)) :
      (γ₀.relabelComplete (e.trans toLex).symm).costErr β =
        ∑ p : V × V with p.1 < p.2,
          distErr (if (e p.1).1 = (e p.2).1 then 1 else α (e p.1).1 (e p.2).1)
            (β p.1 * (β p.2)⁻¹) := by
    rw [Cochain.costErr_complete]
    refine sum_congr rfl fun p hp => ?_
    have hne : toLex (e p.1) ≠ toLex (e p.2) :=
      toLex.injective.ne (e.injective.ne (mem_filter.mp hp).2.ne)
    rw [Cochain.relabelComplete_apply, symm_symm]
    simp only [trans_apply]
    dsimp only [γ₀]
    rw [Cochain.ofFn_apply_of_adj _ ((TwoComplex.adj_complete _ _).mpr hne)]
    simp only [ofLex_toLex]
    by_cases h : (e p.1).1 = (e p.2).1 <;> simp [h]
  have hR (β : (U ×ₗ ι) → Perm (Fin m)) :
      γ₀.costErr β =
        ∑ p : (U ×ₗ ι) × (U ×ₗ ι) with p.1 < p.2,
          distErr (if (ofLex p.1).1 = (ofLex p.2).1 then 1 else α (ofLex p.1).1 (ofLex p.2).1)
            (β p.1 * (β p.2)⁻¹) := by
    rw [Cochain.costErr_complete]
    refine sum_congr rfl fun p hp => ?_
    dsimp only [γ₀]
    rw [Cochain.ofFn_apply_of_adj _ ((TwoComplex.adj_complete _ _).mpr (mem_filter.mp hp).2.ne)]
  simp only [hL, hR] at hrel
  exact hrel

/-- Transporting the global cross-degree infimum over `m + 2 ≥ 2` on `V` along `e.trans toLex`
to the lexicographic product `U ×ₗ ι`. -/
private theorem ciInf₂_sum_filter_lt_distErr_prod_eq_lex
    {V U ι : Type*} [Fintype V] [LinearOrder V] [Fintype U] [LinearOrder U]
    [Fintype ι] [LinearOrder ι] {n : ℕ} (e : V ≃ U × ι) (α : U → U → Perm (Fin n))
    (hα : ∀ u v : U, u ≠ v → α v u = (α u v)⁻¹) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ p : V × V with p.1 < p.2,
          distErr (if (e p.1).1 = (e p.2).1 then 1 else α (e p.1).1 (e p.2).1)
            (β p.1 * (β p.2)⁻¹)) =
      ⨅ (m : ℕ) (β : (U ×ₗ ι) → Perm (Fin (m + 2))),
        ∑ p : (U ×ₗ ι) × (U ×ₗ ι) with p.1 < p.2,
          distErr (if (ofLex p.1).1 = (ofLex p.2).1 then 1 else α (ofLex p.1).1 (ofLex p.2).1)
            (β p.1 * (β p.2)⁻¹) :=
  iInf_congr fun m => ciInf_sum_filter_lt_distErr_prod_eq_lex e α hα (m + 2)

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
  exact (ciInf_sum_filter_lt_distErr_prod_eq_lex e α hα m).trans
    (ciInf_sum_distErr_lex (V := U) (ι := ι) α m)

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
  exact (ciInf₂_sum_filter_lt_distErr_prod_eq_lex e α hα).trans
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
  have hcard : Fintype.card V = 4 * Fintype.card ι := by
    simpa [Fintype.card_prod] using Fintype.card_congr e
  refine (ciInf₂_sum_filter_lt_distErr_prod_eq_lex e α hα).trans ?_
  rw [ciInf₂_sum_distErr_lex_fin_four_of_eq_setOf_isSwap α h0 hswaps, hcard,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

end Equiv

namespace TauCeti

open Equiv Equiv.Perm TwoComplex

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
baseline on `q * (2 * t + 1)` vertices and the explicit threshold `q ^ 2 * t * (t + 1) / 3`. -/
theorem mul_two_mul_add_one_choose_two_div_four_sub (q t : ℕ) :
    ((q * (2 * t + 1)).choose 2 : ℝ) / 4 - (q : ℝ) ^ 2 * t * (t + 1) / 3 =
      (q : ℝ) * ((q : ℝ) * (4 * (t : ℝ) ^ 2 + 4 * t + 3) - (6 * t + 3)) / 24 := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

/-- When `1 ≤ q` and `1 ≤ t`, the complete-graph `1 / 4` baseline on `q * (2 * t + 1)` vertices
strictly exceeds the explicit threshold `q ^ 2 * t * (t + 1) / 3`. -/
theorem sq_mul_mul_add_one_div_three_lt_choose_two_div_four {q t : ℕ}
    (hq : 1 ≤ q) (ht : 1 ≤ t) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 < ((q * (2 * t + 1)).choose 2 : ℝ) / 4 := by
  have hpoly : ((6 * t + 3 + 2 * q : ℕ) : ℝ) ≤ ((q * (4 * t ^ 2 + 4 * t + 3) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (six_mul_add_three_add_two_mul_le hq ht)
  push_cast at hpoly
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsub := mul_two_mul_add_one_choose_two_div_four_sub q t
  nlinarith

/-- For all `q, t : ℕ` (including `q = 0` and `t = 0`), the explicit threshold
`q ^ 2 * t * (t + 1) / 3` is at most the `1 / 4` complete-graph baseline
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

end StaircaseGraph

/-! ### Cochain thresholds, cross-degree star bound, replication, and staircase exactness -/

namespace Cochain

section CochainThreshold

variable {V : Type*} [Fintype V] [LinearOrder V] {X : TwoComplex V} {n m : ℕ}

/-- Whenever the equal-degree `costErr` infimum on `X` is at most `#X.edges / (n + 1)`, it is a
lower bound for the degree-`m` `costErr` infimum in every degree `m : ℕ`. -/
theorem ciInf_costErr_le_of_le_card_div_add_one (α : Cochain X (Perm (Fin n)))
    (hle : (⨅ β : V → Perm (Fin n), α.costErr β) ≤ (#X.edges : ℝ) / (n + 1)) (m : ℕ) :
    (⨅ β : V → Perm (Fin n), α.costErr β) ≤ ⨅ β : V → Perm (Fin m), α.costErr β := by
  set E : Finset (V × V) :=
    univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges)
  have hcard : #E = X.edges.card := by
    refine card_bij (fun p _ => ({p.1, p.2} : Finset V)) (fun p hp => (mem_filter.mp hp).2.2)
      ?_ ?_
    · rintro ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ hpair
      have hlt₁ : u₁ < v₁ := (mem_filter.mp hp₁).2.1
      have hlt₂ : u₂ < v₂ := (mem_filter.mp hp₂).2.1
      rw [← coe_inj, coe_pair, coe_pair, Set.pair_eq_pair_iff] at hpair
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact (lt_asymm hlt₁ hlt₂).elim
    · intro e he
      obtain ⟨u, v, hlt, hset⟩ := X.exists_increasing_of_mem_edges he
      exact ⟨(u, v), mem_filter.mpr ⟨mem_univ _, hlt, hset ▸ he⟩, hset⟩
  have hle' : (⨅ β : V → Perm (Fin n),
      ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤ (#E : ℝ) / (n + 1) := by
    simpa only [E, hcard, costErr_def] using hle
  simpa only [E, costErr_def] using E.ciInf_sum_distErr_mul_inv_le_of_le_card_div_add_one α hle' m

/-- When `2 ≤ n` and the equal-degree `costErr` infimum on `X` is at most `#X.edges / (n + 1)`,
`α.gaugeDistErr` equals the equal-degree `costErr` infimum. -/
theorem gaugeDistErr_eq_ciInf_costErr_of_le (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n)
    (hle : (⨅ β : V → Perm (Fin n), α.costErr β) ≤ (#X.edges : ℝ) / (n + 1)) :
    α.gaugeDistErr = ⨅ β : V → Perm (Fin n), α.costErr β := by
  refine le_antisymm (α.gaugeDistErr_le_ciInf_costErr hn) ?_
  rw [gaugeDistErr_def]
  exact le_ciInf fun m => α.ciInf_costErr_le_of_le_card_div_add_one hle (m + 2)

/-- When `2 ≤ n` and `α.gaugeDist (movedNorm (Fin n)) ≤ n * #X.edges / (n + 1)`,
`α.gaugeDistErr` equals `α.gaugeDist (movedNorm (Fin n)) / n`. -/
theorem gaugeDistErr_eq_gaugeDist_div_of_le (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n)
    (hle : α.gaugeDist (movedNorm (Fin n)) ≤ (n : ℝ) * #X.edges / (n + 1)) :
    α.gaugeDistErr = α.gaugeDist (movedNorm (Fin n)) / n := by
  have : NeZero n := ⟨by omega⟩
  have hn_pos : (0 : ℝ) < n := by positivity
  have hle' : (⨅ β : V → Perm (Fin n), α.costErr β) ≤ (#X.edges : ℝ) / (n + 1) := by
    rw [α.ciInf_costErr_eq_gaugeDist_div, div_le_iff₀ hn_pos]
    exact hle.trans_eq (by ring)
  rw [α.gaugeDistErr_eq_ciInf_costErr_of_le hn hle', α.ciInf_costErr_eq_gaugeDist_div]

end CochainThreshold

section StarAndReplication

variable {V ι : Type*} [Fintype V] [LinearOrder V] {n m : ℕ}

/-- Cross-degree star bound in counting form: for `2 ≤ n` and any degree-`n` cochain `α` on
`complete V`, `Fintype.card V * α.gaugeDistErr ≤ 3 * (α.defect (movedNorm (Fin n)) / n)`. -/
theorem card_mul_gaugeDistErr_le (α : Cochain (complete V) (Perm (Fin n))) (hn : 2 ≤ n) :
    (Fintype.card V : ℝ) * α.gaugeDistErr ≤ 3 * (α.defect (movedNorm (Fin n)) / n) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hgd : (Fintype.card V : ℝ) * α.gaugeDistErr ≤
      (Fintype.card V : ℝ) * (α.gaugeDist (movedNorm (Fin n)) / n) :=
    mul_le_mul_of_nonneg_left (α.gaugeDistErr_le_gaugeDist_div hn) (Nat.cast_nonneg _)
  have hstar := div_le_div_of_nonneg_right
    (TauCeti.card_mul_gaugeDist_le (movedNorm (Fin n)) isConjInvariant_movedNorm α) hn_pos.le
  calc (Fintype.card V : ℝ) * α.gaugeDistErr
      ≤ (Fintype.card V : ℝ) * (α.gaugeDist (movedNorm (Fin n)) / n) := hgd
    _ = ((Fintype.card V : ℝ) * α.gaugeDist (movedNorm (Fin n))) / n := by ring
    _ ≤ (3 * α.defect (movedNorm (Fin n))) / n := hstar
    _ = 3 * (α.defect (movedNorm (Fin n)) / n) := by ring

/-- Pointwise cross-degree star bound for a degree-`n` cochain (`2 ≤ n`) at positive
`gaugeDistErr`. -/
theorem card_div_three_le_defect_div_gaugeDistErr {α : Cochain (complete V) (Perm (Fin n))}
    (hn : 2 ≤ n) (hα : 0 < α.gaugeDistErr) :
    (Fintype.card V : ℝ) / 3 ≤ α.defect (movedNorm (Fin n)) / n / α.gaugeDistErr := by
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hα, mul_comm _ (3 : ℝ)]
  exact α.card_mul_gaugeDistErr_le hn

/-- Degree-`m` cross-degree cost infimum of `α.replicate ι` on `complete (V ×ₗ ι)`. -/
theorem ciInf_costErr_replicate [Fintype ι] [LinearOrder ι]
    (α : Cochain (complete V) (Perm (Fin n))) (m : ℕ) :
    (⨅ β : (V ×ₗ ι) → Perm (Fin m), (α.replicate ι).costErr β) =
      (Fintype.card V * (Fintype.card ι).choose 2 : ℕ) * (1 - (min n m : ℝ) / max n m) +
        (Fintype.card ι : ℝ) ^ 2 * ⨅ β₀ : V → Perm (Fin m), α.costErr β₀ := by
  have hL (β : (V ×ₗ ι) → Perm (Fin m)) :
      (α.replicate ι).costErr β =
        ∑ p ∈ ({q : (V ×ₗ ι) × (V ×ₗ ι) | q.1 < q.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι))),
          distErr (if (ofLex p.1).1 = (ofLex p.2).1 then 1 else α (ofLex p.1).1 (ofLex p.2).1)
            (β p.1 * (β p.2)⁻¹) := by
    rw [costErr_complete]
    refine sum_congr rfl fun p _ => ?_
    rw [replicate_apply]
    by_cases h : (ofLex p.1).1 = (ofLex p.2).1 <;> simp [h]
  simp_rw [hL, costErr_complete]
  exact ciInf_sum_distErr_lex (V := V) (ι := ι) α m

/-- Replication multiplies the degree-`m` `costErr` infimum by at least `Fintype.card ι ^ 2`. -/
theorem card_sq_mul_ciInf_costErr_le_replicate [Fintype ι] [LinearOrder ι]
    (α : Cochain (complete V) (Perm (Fin n))) (m : ℕ) :
    (Fintype.card ι : ℝ) ^ 2 * (⨅ β₀ : V → Perm (Fin m), α.costErr β₀) ≤
      ⨅ β : (V ×ₗ ι) → Perm (Fin m), (α.replicate ι).costErr β := by
  rw [α.ciInf_costErr_replicate m, ← distErr_one_one]
  exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (distErr_nonneg 1 1))

/-- In equal nonzero degree `n`, balanced replication multiplies the `costErr` infimum by
`Fintype.card ι ^ 2`. -/
theorem ciInf_costErr_replicate_eq [Fintype ι] [LinearOrder ι] [NeZero n]
    (α : Cochain (complete V) (Perm (Fin n))) :
    (⨅ β : (V ×ₗ ι) → Perm (Fin n), (α.replicate ι).costErr β) =
      (Fintype.card ι : ℝ) ^ 2 * ⨅ β₀ : V → Perm (Fin n), α.costErr β₀ := by
  rw [α.ciInf_costErr_replicate n, ← distErr_one_one, distErr_self, mul_zero, zero_add]

/-- Whenever a degree-`n` cochain (`2 ≤ n`) on `complete V` attains its `gaugeDistErr` at its own
degree `n`, its replication `α.replicate ι` also attains `gaugeDistErr` at degree `n`, with value
multiplied by `Fintype.card ι ^ 2`. -/
theorem gaugeDistErr_replicate_of_forall_le [Fintype ι] [LinearOrder ι]
    (α : Cochain (complete V) (Perm (Fin n))) (hn : 2 ≤ n)
    (hmin : ∀ m : ℕ,
      (⨅ β₀ : V → Perm (Fin n), α.costErr β₀) ≤ ⨅ β₀ : V → Perm (Fin (m + 2)), α.costErr β₀) :
    (α.replicate ι).gaugeDistErr = (Fintype.card ι : ℝ) ^ 2 * α.gaugeDistErr := by
  have : NeZero n := ⟨by omega⟩
  have hα : α.gaugeDistErr = ⨅ β₀ : V → Perm (Fin n), α.costErr β₀ := by
    refine le_antisymm (α.gaugeDistErr_le_ciInf_costErr hn) ?_
    rw [gaugeDistErr_def]
    exact le_ciInf hmin
  rw [hα]
  refine le_antisymm ?_ ?_
  · exact ((α.replicate ι).gaugeDistErr_le_ciInf_costErr hn).trans_eq α.ciInf_costErr_replicate_eq
  · rw [gaugeDistErr_def]
    refine le_ciInf fun m => ?_
    exact (mul_le_mul_of_nonneg_left (hmin m) (sq_nonneg _)).trans
      (α.card_sq_mul_ciInf_costErr_le_replicate (m + 2))

/-- Exact degree-`m` `costErr` infimum for a three-transposition cochain on `complete (Fin 4)`. -/
theorem ciInf_costErr_fin_four_of_eq_setOf_isSwap
    (α : Cochain (complete (Fin 4)) (Perm (Fin 3)))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) (m : ℕ) :
    (⨅ β : Fin 4 → Perm (Fin m), α.costErr β) = 6 - ((4 * min 3 m : ℕ) : ℝ) / max 3 m := by
  simp_rw [costErr_complete]
  exact TauCeti.ciInf_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps m

/-- A three-transposition cochain on `complete (Fin 4)` has cross-degree gauge distance `2`. -/
theorem gaugeDistErr_fin_four_of_eq_setOf_isSwap
    (α : Cochain (complete (Fin 4)) (Perm (Fin 3)))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    α.gaugeDistErr = 2 := by
  simp_rw [gaugeDistErr_def, costErr_complete]
  exact TauCeti.ciInf₂_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps

end StarAndReplication

section CochainStaircase

variable {V : Type*} [Fintype V] [LinearOrder V] {q t m : ℕ}

/-- On `Fintype.card V = q * (2 * t + 1)` vertices with `1 ≤ q` and `1 ≤ t`, the degree-`m`
(`m ≠ 3`) `costErr` infimum of any degree-`3` cochain on `complete V` strictly exceeds
`q ^ 2 * t * (t + 1) / 3`. -/
theorem sq_mul_mul_add_one_div_three_lt_ciInf_costErr_three_of_ne
    (hcard : Fintype.card V = q * (2 * t + 1)) (hq : 1 ≤ q) (ht : 1 ≤ t)
    (α : Cochain (complete V) (Perm (Fin 3))) (hm : m ≠ 3) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 < ⨅ β : V → Perm (Fin m), α.costErr β := by
  simp_rw [costErr_complete]
  exact sq_mul_mul_add_one_div_three_lt_ciInf_sum_distErr_three_of_ne hcard hq ht α hm

/-- For every `q, t : ℕ`, if `Fintype.card V = q * (2 * t + 1)` and `α` is a degree-`3` cochain on
`complete V` with `α.gaugeDist (movedNorm (Fin 3)) ≤ q ^ 2 * t * (t + 1)`, then
`α.gaugeDistErr = α.gaugeDist (movedNorm (Fin 3)) / 3`. -/
theorem gaugeDistErr_eq_gaugeDist_div_three_of_card_eq
    (hcard : Fintype.card V = q * (2 * t + 1)) (α : Cochain (complete V) (Perm (Fin 3)))
    (hle : α.gaugeDist (movedNorm (Fin 3)) ≤ (q : ℝ) ^ 2 * t * (t + 1)) :
    α.gaugeDistErr = α.gaugeDist (movedNorm (Fin 3)) / 3 := by
  have h := α.gaugeDistErr_eq_gaugeDist_div_of_le (by decide) ?_
  · simpa only [Nat.cast_ofNat] using h
  · rw [card_edges_complete, hcard]
    have hbase := sq_mul_mul_add_one_div_three_le_choose_two_div_four q t
    rw [Nat.cast_ofNat]
    linarith

end CochainStaircase

end Cochain

section CrossDegreeStarBound

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The star bound as a lower bound on `h1Err (complete V)`, whenever some cochain of degree at
least `2` has strictly positive cross-degree gauge distance. -/
theorem card_div_three_le_h1Err_of_exists
    (hne : ∃ (n : ℕ) (α : Cochain (complete V) (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) :
    (Fintype.card V : ℝ) / 3 ≤ h1Err (complete V) :=
  le_h1Err_of_forall hne fun _ _ hα =>
    Cochain.card_div_three_le_defect_div_gaugeDistErr (by omega) hα

/-- Unconditional cross-degree star bound: when `3 ≤ Fintype.card V`,
`(Fintype.card V : ℝ) / 3 ≤ h1Err (complete V)`. -/
theorem card_div_three_le_h1Err (hV : 3 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) / 3 ≤ h1Err (complete V) :=
  let ⟨α, hα⟩ := exists_gaugeDistErr_pos_complete hV (n := 2) (by decide)
  card_div_three_le_h1Err_of_exists ⟨0, α, hα⟩

end CrossDegreeStarBound

end TauCeti

end
