/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Cochain
public import TauCeti.Combinatorics.CoboundaryExpansion.Replication

/-!
# Cross-degree replication and `Fin 4` seed evaluations

This file develops balanced cluster replication and `Fin 4` three-transposition evaluations for
cross-degree cochain distances (`TauCeti.Cochain`) and arbitrary-vertex-type pullbacks (`Equiv`):

* **Cochain cluster replication and `Fin 4` seeds** (`TauCeti.Cochain.costErr_replicate`,
  `TauCeti.Cochain.ciInf_costErr_replicate`,
  `TauCeti.Cochain.card_sq_mul_ciInf_costErr_le_replicate`,
  `TauCeti.Cochain.ciInf_costErr_replicate_eq`,
  `TauCeti.Cochain.gaugeDistErr_replicate_of_forall_le`,
  `TauCeti.Cochain.ciInf_costErr_fin_four_of_eq_setOf_isSwap`, and
  `TauCeti.Cochain.gaugeDistErr_fin_four_of_eq_setOf_isSwap`): replicating a cochain along `V ×ₗ ι`
  adds `(Fintype.card V * (Fintype.card ι).choose 2) * (1 - min n m / max n m)` to
  `Fintype.card ι ^ 2` times the base degree-`m` infimum, multiplies `gaugeDistErr` by
  `Fintype.card ι ^ 2` whenever `gaugeDistErr` is attained at degree `n ≥ 2`, and gives exact
  `gaugeDistErr = 2` for three-transposition cochains on `complete (Fin 4)`.
* **Arbitrary-vertex-type pullbacks and multiples of four**
  (`Equiv.ciInf_sum_filter_lt_distErr_prod`,
  `Equiv.ciInf₂_sum_filter_lt_distErr_prod_eq_card_sq_mul_ciInf_of_le_of_forall_le`,
  `Equiv.ciInf₂_sum_filter_lt_distErr_fin_four_prod_of_eq_setOf_isSwap`, and
  `TauCeti.exists_equiv_fin_four_prod_ciInf₂_sum_distErr_eq_card_sq_div_eight`): pulling the
  cluster replication of a skew-symmetric assignment on `U` back along an arbitrary bijection
  `e : V ≃ U × ι` (requiring neither order preservation of `e` nor any order on `ι`) satisfies the
  same replication formulas and yields exact cross-degree infimum `Fintype.card V ^ 2 / 8` whenever
  `4 ∣ Fintype.card V`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Section 3.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, Lemma 6 and Proposition 10.
-/

public section

open Finset

namespace TauCeti

open Equiv Equiv.Perm TwoComplex

namespace Cochain

section CochainReplication

variable {V ι : Type*} [Fintype V] [Fintype ι] [LinearOrder V] [LinearOrder ι] {n m : ℕ}

/-- Fixed-gauge `costErr` formula for the balanced replication `α.replicate ι` on
`complete (V ×ₗ ι)` under linear orders on `V` and `ι`. -/
theorem costErr_replicate
    (α : Cochain (complete V) (Perm (Fin n))) (β : (V ×ₗ ι) → Perm (Fin m)) :
    (α.replicate ι).costErr β =
      ∑ p : (V ×ₗ ι) × (V ×ₗ ι) with p.1 < p.2,
        distErr (if (ofLex p.1).1 = (ofLex p.2).1 then 1 else α (ofLex p.1).1 (ofLex p.2).1)
          (β p.1 * (β p.2)⁻¹) := by
  rw [costErr_complete]
  refine sum_congr rfl fun p _ => ?_
  rw [replicate_apply]
  by_cases h : (ofLex p.1).1 = (ofLex p.2).1 <;> simp [h]

/-- Degree-`m` cross-degree cost infimum of `α.replicate ι` on `complete (V ×ₗ ι)`. -/
theorem ciInf_costErr_replicate
    (α : Cochain (complete V) (Perm (Fin n))) (m : ℕ) :
    (⨅ β : (V ×ₗ ι) → Perm (Fin m), (α.replicate ι).costErr β) =
      (Fintype.card V * (Fintype.card ι).choose 2 : ℕ) * (1 - (min n m : ℝ) / max n m) +
        (Fintype.card ι : ℝ) ^ 2 * ⨅ β₀ : V → Perm (Fin m), α.costErr β₀ := by
  simp_rw [costErr_replicate, costErr_complete]
  exact ciInf_sum_distErr_lex (V := V) (ι := ι) α m

/-- Replication multiplies the degree-`m` `costErr` infimum by at least `Fintype.card ι ^ 2`. -/
theorem card_sq_mul_ciInf_costErr_le_replicate
    (α : Cochain (complete V) (Perm (Fin n))) (m : ℕ) :
    (Fintype.card ι : ℝ) ^ 2 * (⨅ β₀ : V → Perm (Fin m), α.costErr β₀) ≤
      ⨅ β : (V ×ₗ ι) → Perm (Fin m), (α.replicate ι).costErr β := by
  have hnonneg : 0 ≤ 1 - (min n m : ℝ) / max n m := by
    rw [sub_nonneg]
    exact div_le_one_of_le₀
      (by exact_mod_cast (min_le_left n m).trans (le_max_left n m)) (Nat.cast_nonneg _)
  rw [α.ciInf_costErr_replicate m]
  exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hnonneg)

/-- In equal nonzero degree `n`, balanced replication multiplies the `costErr` infimum by
`Fintype.card ι ^ 2`. -/
theorem ciInf_costErr_replicate_eq [NeZero n]
    (α : Cochain (complete V) (Perm (Fin n))) :
    (⨅ β : (V ×ₗ ι) → Perm (Fin n), (α.replicate ι).costErr β) =
      (Fintype.card ι : ℝ) ^ 2 * ⨅ β₀ : V → Perm (Fin n), α.costErr β₀ := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [α.ciInf_costErr_replicate n, min_self, max_self, div_self hn, sub_self, mul_zero, zero_add]

/-- Whenever a degree-`n` cochain (`2 ≤ n`) on `complete V` attains its `gaugeDistErr` at its own
degree `n`, its replication `α.replicate ι` also attains `gaugeDistErr` at degree `n`, with value
multiplied by `Fintype.card ι ^ 2`. -/
theorem gaugeDistErr_replicate_of_forall_le
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

/-- Degree-`m` (`m ≥ 2`) `costErr` infimum lower bound `2` for a three-transposition cochain on
`complete (Fin 4)`. -/
theorem two_le_ciInf_costErr_fin_four_of_eq_setOf_isSwap
    (α : Cochain (complete (Fin 4)) (Perm (Fin 3)))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap})
    (m : ℕ) :
    2 ≤ ⨅ β : Fin 4 → Perm (Fin (m + 2)), α.costErr β := by
  simp_rw [costErr_complete]
  exact le_ciInf (two_le_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps)

/-- A three-transposition cochain on `complete (Fin 4)` has cross-degree gauge distance `2`. -/
theorem gaugeDistErr_fin_four_of_eq_setOf_isSwap
    (α : Cochain (complete (Fin 4)) (Perm (Fin 3)))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    α.gaugeDistErr = 2 := by
  simp_rw [gaugeDistErr_def, costErr_complete]
  exact TauCeti.ciInf₂_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps

end CochainReplication

end Cochain

end TauCeti

/-! ### Arbitrary-vertex-type pullback replication and multiples of four -/

namespace Equiv

open Equiv.Perm TauCeti

private theorem costErr_relabelComplete_replicate
    {V U ι : Type*} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype ι]
    {n m : ℕ} (e : V ≃ U × ι) (α : U → U → Perm (Fin n))
    (hα : ∀ u v : U, u ≠ v → α v u = (α u v)⁻¹) (β : V → Perm (Fin m)) :
    (((Cochain.ofFn (TwoComplex.complete U) α fun u v huv =>
        hα u v ((TwoComplex.adj_complete u v).mp huv)).replicate ι).relabelComplete
        (e.trans toLex).symm).costErr β =
      ∑ p : V × V with p.1 < p.2,
        distErr (if (e p.1).1 = (e p.2).1 then 1 else α (e p.1).1 (e p.2).1)
          (β p.1 * (β p.2)⁻¹) := by
  rw [Cochain.costErr_complete]
  refine sum_congr rfl fun p _ => ?_
  rw [Cochain.relabelComplete_apply, symm_symm, trans_apply, trans_apply, Cochain.replicate_apply,
    ofLex_toLex, ofLex_toLex]
  by_cases h : (e p.1).1 = (e p.2).1
  · simp [h]
  · simp [h, TwoComplex.adj_complete]

private theorem costErr_ofFn_complete
    {U : Type*} [Fintype U] [LinearOrder U] {n m : ℕ}
    (α : U → U → Perm (Fin n)) (hα : ∀ u v : U, u ≠ v → α v u = (α u v)⁻¹)
    (β : U → Perm (Fin m)) :
    (Cochain.ofFn (TwoComplex.complete U) α fun u v huv =>
        hα u v ((TwoComplex.adj_complete u v).mp huv)).costErr β =
      ∑ p : U × U with p.1 < p.2, distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) := by
  rw [Cochain.costErr_complete]
  refine sum_congr rfl fun p hp => ?_
  simp [TwoComplex.adj_complete, (mem_filter.mp hp).2.ne]

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
  let _ : LinearOrder ι :=
    LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let base : Cochain (TwoComplex.complete U) (Perm (Fin n)) :=
    Cochain.ofFn (TwoComplex.complete U) α fun u v huv =>
      hα u v ((TwoComplex.adj_complete u v).mp huv)
  simp_rw [← costErr_relabelComplete_replicate e α hα, ← costErr_ofFn_complete α hα]
  rw [(base.replicate ι).ciInf_costErr_relabelComplete (e.trans toLex).symm m]
  exact base.ciInf_costErr_replicate m

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
  let _ : LinearOrder ι :=
    LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let base : Cochain (TwoComplex.complete U) (Perm (Fin n)) :=
    Cochain.ofFn (TwoComplex.complete U) α fun u v huv =>
      hα u v ((TwoComplex.adj_complete u v).mp huv)
  simp_rw [← costErr_relabelComplete_replicate e α hα, ← costErr_ofFn_complete α hα]
  have hmin' : ∀ m : ℕ,
      (⨅ β₀ : U → Perm (Fin n), base.costErr β₀) ≤
        ⨅ β₀ : U → Perm (Fin (m + 2)), base.costErr β₀ := by
    simpa only [← costErr_ofFn_complete α hα] using hmin
  have hbase_gd : base.gaugeDistErr = ⨅ β₀ : U → Perm (Fin n), base.costErr β₀ :=
    le_antisymm (base.gaugeDistErr_le_ciInf_costErr hn)
      (by rw [Cochain.gaugeDistErr_def]; exact le_ciInf hmin')
  rw [← Cochain.gaugeDistErr_def ((base.replicate ι).relabelComplete (e.trans toLex).symm),
    Cochain.gaugeDistErr_relabelComplete,
    base.gaugeDistErr_replicate_of_forall_le hn hmin', hbase_gd]

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
  let _ : LinearOrder ι :=
    LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let base : Cochain (TwoComplex.complete (Fin 4)) (Perm (Fin 3)) :=
    Cochain.ofFn (TwoComplex.complete (Fin 4)) α fun u v huv =>
      hα u v ((TwoComplex.adj_complete u v).mp huv)
  have h0' : ∀ v : Fin 4, 0 < v → base 0 v = 1 := by
    intro v hv
    rw [Cochain.ofFn_apply_of_adj _ ((TwoComplex.adj_complete 0 v).mpr hv.ne), h0 v hv]
  have h12 : base 1 2 = α 1 2 :=
    Cochain.ofFn_apply_of_adj _ ((TwoComplex.adj_complete 1 2).mpr (by decide))
  have h13 : base 1 3 = α 1 3 :=
    Cochain.ofFn_apply_of_adj _ ((TwoComplex.adj_complete 1 3).mpr (by decide))
  have h23 : base 2 3 = α 2 3 :=
    Cochain.ofFn_apply_of_adj _ ((TwoComplex.adj_complete 2 3).mpr (by decide))
  have hswaps' : ({base 1 2, base 1 3, base 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap} := by
    rw [h12, h13, h23]
    exact hswaps
  have hmin : ∀ m : ℕ,
      (⨅ β₀ : Fin 4 → Perm (Fin 3), base.costErr β₀) ≤
        ⨅ β₀ : Fin 4 → Perm (Fin (m + 2)), base.costErr β₀ := by
    intro m
    refine le_trans ?_ (Cochain.two_le_ciInf_costErr_fin_four_of_eq_setOf_isSwap base h0' hswaps' m)
    rw [Cochain.ciInf_costErr_fin_four_of_eq_setOf_isSwap base h0' hswaps' 3]
    norm_num
  have hcard : Fintype.card V = 4 * Fintype.card ι := by
    simpa [Fintype.card_prod] using Fintype.card_congr e
  simp_rw [← costErr_relabelComplete_replicate e α hα]
  rw [← Cochain.gaugeDistErr_def ((base.replicate ι).relabelComplete (e.trans toLex).symm),
    Cochain.gaugeDistErr_relabelComplete,
    base.gaugeDistErr_replicate_of_forall_le (by decide) hmin,
    Cochain.gaugeDistErr_fin_four_of_eq_setOf_isSwap base h0' hswaps',
    hcard, Nat.cast_mul, Nat.cast_ofNat]
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

end TauCeti

end
