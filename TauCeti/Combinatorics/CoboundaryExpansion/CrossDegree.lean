/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Order.Prod.Lex.Basic
public import TauCeti.GroupTheory.Perm.DistErr.Invariance
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Optimization.Replication
import TauCeti.GroupTheory.Perm.Fin
import TauCeti.GroupTheory.Perm.FinThree.Basic

/-!
# Cross-degree pair costs, degree-3 baselines, fiber bounds, and lexicographic replication

Given directed edges carrying permutations in `Equiv.Perm (Fin n)` and a vertex gauge taking values
in `Equiv.Perm (Fin m)` of possibly different degree, the cross-degree pair cost sums
`Equiv.Perm.distErr (α u v) (β u * (β v)⁻¹)` across edges `(u, v)`. This file establishes the
combinatorial bounds and exact evaluations for these sums and their infima across gauge degrees:

* **Degree-`3` mismatch baselines** (`Equiv.Perm.one_div_three_le_distErr_three_two`,
  `Equiv.Perm.one_div_four_le_distErr_three_of_four_le`,
  `Equiv.Perm.two_div_five_le_distErr_three_of_five_le`,
  `Equiv.Perm.one_div_four_le_distErr_three_of_ne`, and
  `Finset.card_div_four_le_sum_distErr_three_of_ne`): explicit lower bounds comparing permutations
  in `Equiv.Perm (Fin 3)` against permutations of degree `2`, `m ≥ 4`, `m ≥ 5`, or any `m ≠ 3`.
* **Cross-degree gauge invariance for `n ≤ m`** (`Finset.ciInf_sum_distErr_inv_mul_mul_of_le`):
  transforming `α` by two-sided vertex-gauge multiplication `(γ u)⁻¹ * α u v * γ v` in degree `n`
  leaves the degree-`m` gauge-cost infimum unchanged whenever `n ≤ m`.
* **Fiber decomposition and 4-vertex reduction**
  (`Finset.sum_agreeCount_mul_inv_le_of_forall_option`,
  `Finset.sum_agreeCount_mul_inv_le_four_mul_min_of_card_eq_four_of_forall_le_four`, and
  `Finset.card_sub_four_mul_min_div_le_sum_distErr_mul_inv_of_card_eq_four_of_forall_le_four`):
  indexing agreements on `β u * (β v)⁻¹` by `y : Fin m` decomposes the total agreement count across
  `m` partial vertex colourings `V → Option (Fin n)` of total domain size
  `Fintype.card V * min n m`. On four linearly ordered vertices, partial colourings of domain size
  `#S ≤ 3` satisfy at most `(#S).choose 2 ≤ #S` edges automatically, reducing the `4 * min n m`
  agreement upper bound (and the `#E - 4 * min n m / max n m` pair-cost lower bound) for every `m`
  to checking `≤ 4` compatible edges on total functions `V → Fin n`.
* **Exact three-transposition optimization on `Fin 4`**
  (`TauCeti.ciInf_sum_distErr_fin_four_of_eq_setOf_isSwap` and
  `TauCeti.ciInf₂_sum_distErr_fin_four_of_eq_setOf_isSwap`): when `α 0 v = 1` for `0 < v` and
  `{α 1 2, α 1 3, α 2 3}` consists of the three transpositions of `Perm (Fin 3)`, the constant gauge
  `1` is globally optimal in every degree `m : ℕ`, giving exact infimum
  `6 - 4 * min 3 m / max 3 m` (`14 / 3` at `m = 1`, `10 / 3` at `m = 2`, `2` at `m = 3`, `3` at
  `m = 4`, at least `18 / 5` for `m ≥ 5`, and global cross-degree infimum `2` over `m + 2 ≥ 2`).
* **Lexicographic cluster replication** (`TauCeti.ciInf_sum_distErr_lex`,
  `TauCeti.card_sq_mul_ciInf_le_ciInf_sum_distErr_lex`,
  `TauCeti.ciInf_sum_distErr_lex_eq_card_sq_mul_ciInf`,
  `TauCeti.ciInf₂_sum_distErr_lex_eq_card_sq_mul_ciInf_of_le_of_forall_le`, and
  `TauCeti.ciInf₂_sum_distErr_lex_fin_four_of_eq_setOf_isSwap`): replicating vertices along `V ×ₗ ι`
  with identity labels inside clusters adds `(Fintype.card V * (Fintype.card ι).choose 2) *
  (1 - min n m / max n m)` to `Fintype.card ι ^ 2` times the base degree-`m` infimum. In
  particular, replication multiplies the degree-`m` infimum by at least `Fintype.card ι ^ 2` for
  every `m`, with equality in equal nonzero degree `m = n`, and multiplies the global infimum over
  all gauge degrees `m + 2 ≥ 2` by `Fintype.card ι ^ 2` when the base labels have degree `n ≥ 2`
  and attain that infimum at degree `n`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Section 3.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, Lemma 6 and Proposition 10.
-/

public section

open Finset

namespace Equiv.Perm

variable {m : ℕ}

/-! ### Degree-`3` mismatch baselines -/

/-- Any permutation of degree `3` and any permutation of degree `2` have distance with errors at
least `1 / 3`. -/
theorem one_div_three_le_distErr_three_two (σ : Perm (Fin 3)) (τ : Perm (Fin 2)) :
    (1 : ℝ) / 3 ≤ distErr σ τ := by
  have h := one_sub_div_le_distErr_of_ge σ τ (by decide)
  norm_num at h ⊢
  exact h

/-- Any permutation of degree `2` and any permutation of degree `3` have distance with errors at
least `1 / 3`. -/
theorem one_div_three_le_distErr_two_three (σ : Perm (Fin 2)) (τ : Perm (Fin 3)) :
    (1 : ℝ) / 3 ≤ distErr σ τ :=
  (one_div_three_le_distErr_three_two τ σ).trans_eq (distErr_comm τ σ)

/-- Comparing a permutation of degree `3` with one of degree `m ≥ 4` gives distance with errors at
least `1 / 4`. -/
theorem one_div_four_le_distErr_three_of_four_le (σ : Perm (Fin 3)) (τ : Perm (Fin m))
    (hm : 4 ≤ m) : (1 : ℝ) / 4 ≤ distErr σ τ := by
  have h := one_sub_div_le_distErr_of_le_of_le σ τ (by decide : 3 ≤ 4) hm
  norm_num at h ⊢
  exact h

/-- Comparing a permutation of degree `3` with one of degree `m ≥ 5` gives distance with errors at
least `2 / 5`. -/
theorem two_div_five_le_distErr_three_of_five_le (σ : Perm (Fin 3)) (τ : Perm (Fin m))
    (hm : 5 ≤ m) : (2 : ℝ) / 5 ≤ distErr σ τ := by
  have h := one_sub_div_le_distErr_of_le_of_le σ τ (by decide : 3 ≤ 5) hm
  norm_num at h ⊢
  exact h

/-- Comparing a permutation of degree `3` with one of any unequal degree `m ≠ 3` gives distance
with errors at least `1 / 4`. -/
theorem one_div_four_le_distErr_three_of_ne (σ : Perm (Fin 3)) (τ : Perm (Fin m)) (hne : m ≠ 3) :
    (1 : ℝ) / 4 ≤ distErr σ τ := by
  have h := one_div_add_one_le_distErr_of_ne σ τ hne.symm
  norm_num at h ⊢
  exact h

end Equiv.Perm

namespace Finset

open Equiv Equiv.Perm

variable {ι V : Type*} {n m : ℕ}

/-! ### Edge-sum baseline, cross-degree gauge invariance, and fiber counting -/

/-- Comparing permutations of degree `3` against permutations of any unequal degree `m ≠ 3` over a
finite set `s` has total distance with errors at least `#s / 4`. -/
theorem card_div_four_le_sum_distErr_three_of_ne (s : Finset ι) (f : ι → Perm (Fin 3))
    (g : ι → Perm (Fin m)) (hne : m ≠ 3) :
    (#s : ℝ) / 4 ≤ ∑ x ∈ s, distErr (f x) (g x) := by
  have h := s.card_div_add_one_le_sum_distErr_of_ne f g hne.symm
  norm_num at h
  exact h

/-- When `n ≤ m`, transforming `α` by a degree-`n` vertex gauge `γ : V → Perm (Fin n)` via
two-sided multiplication `(γ u)⁻¹ * α u v * γ v` preserves the infimum of the degree-`m`
cross-degree pair cost over `E`. -/
theorem ciInf_sum_distErr_inv_mul_mul_of_le (E : Finset (V × V)) (α : V → V → Perm (Fin n))
    (γ : V → Perm (Fin n)) (hnm : n ≤ m) :
    (⨅ β : V → Perm (Fin m),
        ∑ e ∈ E, distErr ((γ e.1)⁻¹ * α e.1 e.2 * γ e.2) (β e.1 * (β e.2)⁻¹)) =
      ⨅ β : V → Perm (Fin m), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) :=
  (Equiv.mulLeft (fun v => (γ v).viaEmbedding (Fin.castLEEmb hnm))).iInf_congr fun β =>
    sum_congr rfl fun e _ =>
      (distErr_inv_mul_mul_mul_inv (α e.1 e.2) (γ e.1) (γ e.2) (β e.1) (β e.2) hnm).symm

/-- Indexing agreements by fibers `y : Fin m` bounds
`∑ e ∈ E, agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹)` by `c * (Fintype.card V * min n m)` whenever
every partial colouring `φ : V → Option (Fin n)` satisfies at most `c` times its domain size in
edges of `E`. -/
theorem sum_agreeCount_mul_inv_le_of_forall_option [Fintype V] (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (β : V → Perm (Fin m)) {c : ℕ}
    (hφ : ∀ φ : V → Option (Fin n),
      #{e ∈ E | ∃ i, φ e.2 = some i ∧ φ e.1 = some (α e.1 e.2 i)} ≤
        c * #{v : V | (φ v).isSome}) :
    (∑ e ∈ E, agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤ c * (Fintype.card V * min n m) := by
  let φ (y : Fin m) (v : V) : Option (Fin n) :=
    if h : (β v y : ℕ) < n then some ⟨β v y, h⟩ else none
  have hiff (e : V × V) (y : Fin m) :
      (∃ i : Fin n, (β e.2 y : ℕ) = i ∧ (β e.1 y : ℕ) = α e.1 e.2 i) ↔
        ∃ i : Fin n, φ y e.2 = some i ∧ φ y e.1 = some (α e.1 e.2 i) := by
    constructor
    · rintro ⟨i, h₂, h₁⟩
      have lt₂ : (β e.2 y : ℕ) < n := h₂ ▸ i.isLt
      have lt₁ : (β e.1 y : ℕ) < n := h₁ ▸ (α e.1 e.2 i).isLt
      refine ⟨i, ?_, ?_⟩
      · dsimp only [φ]
        split_ifs
        exact congrArg some (Fin.ext h₂)
      · dsimp only [φ]
        split_ifs
        exact congrArg some (Fin.ext h₁)
    · rintro ⟨i, h₂, h₁⟩
      dsimp only [φ] at h₂ h₁
      split_ifs at h₂ with lt₂
      split_ifs at h₁ with lt₁
      rw [Option.some.injEq] at h₂ h₁
      exact ⟨i, congrArg Fin.val h₂, congrArg Fin.val h₁⟩
  have hswap : (∑ e ∈ E, agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      ∑ y : Fin m, #{e ∈ E | ∃ i, φ y e.2 = some i ∧ φ y e.1 = some (α e.1 e.2 i)} := by
    simp_rw [agreeCount_mul_inv_eq_card_filter]
    have hcongr (e : V × V) :
        #{y : Fin m | ∃ i : Fin n, (β e.2 y : ℕ) = i ∧ (β e.1 y : ℕ) = α e.1 e.2 i} =
          #{y : Fin m | ∃ i : Fin n, φ y e.2 = some i ∧ φ y e.1 = some (α e.1 e.2 i)} :=
      congrArg card (filter_congr fun y _ => hiff e y)
    simp_rw [hcongr, card_filter]
    exact sum_comm
  have hdom : (∑ y : Fin m, #{v : V | (φ y v).isSome}) = Fintype.card V * min n m := by
    have hsome (y : Fin m) : #{v : V | (φ y v).isSome} = #{v : V | (β v y : ℕ) < n} :=
      congrArg card (filter_congr fun v _ => by dsimp only [φ]; split_ifs with h <;> simp [h])
    simp_rw [hsome, card_filter]
    rw [sum_comm]
    simp_rw [← card_filter, card_filter_val_lt]
    rw [sum_const, card_univ, smul_eq_mul, min_comm]
  rw [hswap, ← hdom, mul_sum]
  exact sum_le_sum fun y _ => hφ (φ y)

/-- Distance-with-errors consequence of `Finset.sum_agreeCount_mul_inv_le_of_forall_option`. -/
theorem card_sub_div_le_sum_distErr_mul_inv_of_forall_option [Fintype V] (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (β : V → Perm (Fin m)) {c : ℕ}
    (hφ : ∀ φ : V → Option (Fin n),
      #{e ∈ E | ∃ i, φ e.2 = some i ∧ φ e.1 = some (α e.1 e.2 i)} ≤
        c * #{v : V | (φ v).isSome}) :
    (#E : ℝ) - ((c * (Fintype.card V * min n m) : ℕ) : ℝ) / max n m ≤
      ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  rw [E.sum_distErr_eq_card_sub_div (fun e => α e.1 e.2) (fun e => β e.1 * (β e.2)⁻¹)]
  gcongr
  exact_mod_cast E.sum_agreeCount_mul_inv_le_of_forall_option α β hφ

/-- If `Fintype.card V = 4`, edges in `E` are strictly increasing, and every `f : V → Fin n`
satisfies at most `4` edges of `E`, then the total agreement count across `E` is at most
`4 * min n m`. -/
theorem sum_agreeCount_mul_inv_le_four_mul_min_of_card_eq_four_of_forall_le_four [Fintype V]
    [LinearOrder V] (E : Finset (V × V)) (α : V → V → Perm (Fin n)) (β : V → Perm (Fin m))
    (hV : Fintype.card V = 4) (hE : ∀ e ∈ E, e.1 < e.2)
    (hf : ∀ f : V → Fin n, #{e ∈ E | f e.1 = α e.1 e.2 (f e.2)} ≤ 4) :
    (∑ e ∈ E, agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤ 4 * min n m := by
  have hbound : (∑ e ∈ E, agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤
      1 * (Fintype.card V * min n m) := by
    refine E.sum_agreeCount_mul_inv_le_of_forall_option α β fun φ => ?_
    rw [one_mul]
    set S : Finset V := {v : V | (φ v).isSome}
    have hScard : #S ≤ 4 := (card_filter_le _ _).trans (by simp [hV])
    by_cases hS4 : #S = 4
    · have hSuniv : S = univ := eq_univ_of_card S (hS4.trans hV.symm)
      have hsome (v : V) : (φ v).isSome := by
        have hv : v ∈ S := hSuniv ▸ mem_univ v
        exact (mem_filter.mp hv).2
      let f : V → Fin n := fun v => (φ v).get (hsome v)
      have hget (v : V) : φ v = some (f v) := (Option.some_get (hsome v)).symm
      have heq : #{e ∈ E | ∃ i, φ e.2 = some i ∧ φ e.1 = some (α e.1 e.2 i)} =
          #{e ∈ E | f e.1 = α e.1 e.2 (f e.2)} := by
        refine congrArg card (filter_congr fun e _ => ?_)
        simp [hget]
      rw [hS4, heq]
      exact hf f
    · have hS3 : #S ≤ 3 := by omega
      have hsub : {e ∈ E | ∃ i, φ e.2 = some i ∧ φ e.1 = some (α e.1 e.2 i)} ⊆
          {e ∈ S ×ˢ S | e.1 < e.2} := by
        intro e he
        simp only [mem_filter] at he ⊢
        rcases he with ⟨heE, i, h₂, h₁⟩
        refine ⟨mem_product.mpr ⟨?_, ?_⟩, hE e heE⟩ <;> simp [S, h₁, h₂]
      refine (card_le_card hsub).trans ?_
      rw [card_product_filter_lt]
      interval_cases #S <;> decide
  simpa [hV] using hbound

/-- Distance-with-errors consequence of
`Finset.sum_agreeCount_mul_inv_le_four_mul_min_of_card_eq_four_of_forall_le_four`. -/
theorem card_sub_four_mul_min_div_le_sum_distErr_mul_inv_of_card_eq_four_of_forall_le_four
    [Fintype V] [LinearOrder V] (E : Finset (V × V)) (α : V → V → Perm (Fin n))
    (β : V → Perm (Fin m)) (hV : Fintype.card V = 4) (hE : ∀ e ∈ E, e.1 < e.2)
    (hf : ∀ f : V → Fin n, #{e ∈ E | f e.1 = α e.1 e.2 (f e.2)} ≤ 4) :
    (#E : ℝ) - ((4 * min n m : ℕ) : ℝ) / max n m ≤
      ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  rw [E.sum_distErr_eq_card_sub_div (fun e => α e.1 e.2) (fun e => β e.1 * (β e.2)⁻¹)]
  gcongr
  exact_mod_cast
    E.sum_agreeCount_mul_inv_le_four_mul_min_of_card_eq_four_of_forall_le_four α β hV hE hf

end Finset

namespace TauCeti

open Equiv Equiv.Perm

/-! ### Exact cross-degree optimization for the three-transposition configuration on `Fin 4` -/

/-- When the star of `0 : Fin 4` carries `1` and the opposite triangle `{1, 2, 3}` carries the three
transpositions of `Perm (Fin 3)`, no function `f : Fin 4 → Fin 3` is compatible with more than `4`
of the `6` edges `u < v`. -/
theorem card_filter_lt_eq_apply_le_four_of_eq_setOf_isSwap (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap})
    (f : Fin 4 → Fin 3) :
    #{e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)) |
      f e.1 = α e.1 e.2 (f e.2)} ≤ 4 := by
  let S : Finset (Perm (Fin 3)) := {Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2}
  have hfin : ({α 1 2, α 1 3, α 2 3} : Finset (Perm (Fin 3))) = S :=
    coe_inj.mp (by simpa [S] using hswaps.trans setOf_isSwap_perm_fin_three)
  have h12 : α 1 2 ∈ S := by rw [← hfin]; simp
  have h13 : α 1 3 ∈ S := by rw [← hfin]; simp
  have h23 : α 2 3 ∈ S := by rw [← hfin]; simp
  have hexpand : ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)) =
      {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  have h01 : α 0 1 = 1 := h0 1 (by decide)
  have h02 : α 0 2 = 1 := h0 2 (by decide)
  have h03 : α 0 3 = 1 := h0 3 (by decide)
  have key : ∀ σ₁₂ ∈ S, ∀ σ₁₃ ∈ S, ∀ σ₂₃ ∈ S,
      ({σ₁₂, σ₁₃, σ₂₃} : Finset (Perm (Fin 3))) = S →
      ∀ g : Fin 4 → Fin 3,
        #{e ∈ ({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4)) |
          g e.1 = (if e = (1, 2) then σ₁₂ else if e = (1, 3) then σ₁₃
            else if e = (2, 3) then σ₂₃ else 1) (g e.2)} ≤ 4 := by decide
  have hcongr : #{e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)) |
      f e.1 = α e.1 e.2 (f e.2)} =
    #{e ∈ ({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4)) |
      f e.1 = (if e = (1, 2) then α 1 2 else if e = (1, 3) then α 1 3
        else if e = (2, 3) then α 2 3 else 1) (f e.2)} := by
    rw [hexpand]
    refine congrArg card (filter_congr fun e he => ?_)
    rcases (by simpa using he :
      e = (0, 1) ∨ e = (0, 2) ∨ e = (0, 3) ∨ e = (1, 2) ∨ e = (1, 3) ∨ e = (2, 3)) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp [h01, h02, h03]
  rw [hcongr]
  exact key (α 1 2) h12 (α 1 3) h13 (α 2 3) h23 hfin f

private theorem sum_isSwap_agreeCount_one (m : ℕ) :
    (∑ σ ∈ ({Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2} : Finset (Perm (Fin 3))),
      agreeCount σ (1 : Perm (Fin m))) = min 3 m := by
  simp_rw [agreeCount_one_right, card_filter]
  rw [sum_comm]
  have hpt (i : Fin 3) :
      (∑ σ ∈ ({Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2} : Finset (Perm (Fin 3))),
        if (i : ℕ) < m ∧ σ i = i then 1 else 0) = if (i : ℕ) < m then 1 else 0 := by
    by_cases hi : (i : ℕ) < m
    · simp only [hi, true_and, ↓reduceIte]
      clear hi
      revert i
      decide
    · simp [hi]
  simp_rw [hpt, ← card_filter]
  exact Fin.card_filter_val_lt

/-- Against the identity permutation of degree `m`, the three-transposition configuration on `Fin 4`
has exactly `4 * min 3 m` agreements across the `6` edges `u < v`. -/
theorem sum_agreeCount_one_fin_four_of_eq_setOf_isSwap (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) (m : ℕ) :
    (∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
        agreeCount (α e.1 e.2) (1 : Perm (Fin m))) = 4 * min 3 m := by
  have hfin : ({α 1 2, α 1 3, α 2 3} : Finset (Perm (Fin 3))) =
      {Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2} :=
    coe_inj.mp (by simpa using hswaps.trans setOf_isSwap_perm_fin_three)
  have hcard3 : #({α 1 2, α 1 3, α 2 3} : Finset (Perm (Fin 3))) = 3 := by
    rw [hfin]; decide
  obtain ⟨h12_13, h12_23, h13_23⟩ := card_triple_eq_three_iff.mp hcard3
  have hpairs (w : Fin 4 × Fin 4 → ℕ) :
      (∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)), w e) =
        w (0, 1) + w (0, 2) + w (0, 3) + (w (1, 2) + (w (1, 3) + w (2, 3))) := by
    have hexpand : ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)) =
        {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
    rw [hexpand]
    repeat rw [sum_insert (by decide)]
    rw [sum_singleton]
    omega
  rw [hpairs]
  simp only [h0 1 (by decide), h0 2 (by decide), h0 3 (by decide), agreeCount_one_one]
  have hsum_swaps : agreeCount (α 1 2) (1 : Perm (Fin m)) +
      (agreeCount (α 1 3) (1 : Perm (Fin m)) + agreeCount (α 2 3) (1 : Perm (Fin m))) =
      ∑ σ ∈ ({α 1 2, α 1 3, α 2 3} : Finset (Perm (Fin 3))), agreeCount σ (1 : Perm (Fin m)) := by
    rw [sum_insert (by simp [h12_13, h12_23]), sum_pair h13_23]
  rw [hsum_swaps, hfin, sum_isSwap_agreeCount_one]
  omega

/-- Against the constant gauge `fun _ => 1` of degree `m`, the three-transposition configuration on
`Fin 4` has cross-degree pair cost `6 - 4 * min 3 m / max 3 m`. -/
theorem sum_distErr_one_fin_four_of_eq_setOf_isSwap (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) (m : ℕ) :
    (∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
        distErr (α e.1 e.2) (1 : Perm (Fin m))) =
      6 - ((4 * min 3 m : ℕ) : ℝ) / max 3 m := by
  have hcard : #({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)) = 6 := by decide
  have hsum := Finset.sum_distErr_eq_card_sub_div
    ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4))
    (fun e => α e.1 e.2) (fun _ => (1 : Perm (Fin m)))
  rw [hsum, hcard, sum_agreeCount_one_fin_four_of_eq_setOf_isSwap α h0 hswaps m]
  norm_num

/-- Exact degree-`m` cross-degree pair-cost infimum for the three-transposition configuration on
`Fin 4`: for every `m : ℕ`, the infimum over `β : Fin 4 → Perm (Fin m)` equals
`6 - 4 * min 3 m / max 3 m`. -/
theorem ciInf_sum_distErr_fin_four_of_eq_setOf_isSwap (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) (m : ℕ) :
    (⨅ β : Fin 4 → Perm (Fin m),
        ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
          distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      6 - ((4 * min 3 m : ℕ) : ℝ) / max 3 m := by
  set E : Finset (Fin 4 × Fin 4) := {p : Fin 4 × Fin 4 | p.1 < p.2}
  have hcard : #E = 6 := by decide
  have hlower (β : Fin 4 → Perm (Fin m)) :
      6 - ((4 * min 3 m : ℕ) : ℝ) / max 3 m ≤
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
    have h :=
      E.card_sub_four_mul_min_div_le_sum_distErr_mul_inv_of_card_eq_four_of_forall_le_four α β
        (by simp) (fun _ he => (mem_filter.mp he).2)
        (card_filter_lt_eq_apply_le_four_of_eq_setOf_isSwap α h0 hswaps)
    simpa [hcard] using h
  have hbdd : BddBelow (Set.range fun β : Fin 4 → Perm (Fin m) =>
      ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) :=
    ⟨0, by rintro _ ⟨β, rfl⟩; exact sum_nonneg fun _ _ => distErr_nonneg _ _⟩
  refine le_antisymm ?_ (le_ciInf hlower)
  refine (ciInf_le hbdd (fun _ => (1 : Perm (Fin m)))).trans_eq ?_
  simpa using sum_distErr_one_fin_four_of_eq_setOf_isSwap α h0 hswaps m

/-- In degree `1`, the three-transposition configuration on `Fin 4` has cross-degree pair-cost
infimum `14 / 3`. -/
theorem ciInf_sum_distErr_fin_four_one_of_eq_setOf_isSwap (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ β : Fin 4 → Perm (Fin 1),
        ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
          distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 14 / 3 := by
  rw [ciInf_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps 1]
  norm_num

/-- In degree `2`, the three-transposition configuration on `Fin 4` has cross-degree pair-cost
infimum `10 / 3`. -/
theorem ciInf_sum_distErr_fin_four_two_of_eq_setOf_isSwap (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ β : Fin 4 → Perm (Fin 2),
        ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
          distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 10 / 3 := by
  rw [ciInf_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps 2]
  norm_num

/-- In equal degree `3`, the three-transposition configuration on `Fin 4` has cross-degree pair-cost
infimum `2`. -/
theorem ciInf_sum_distErr_fin_four_three_of_eq_setOf_isSwap (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ β : Fin 4 → Perm (Fin 3),
        ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
          distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 2 := by
  rw [ciInf_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps 3]
  norm_num

/-- In degree `4`, the three-transposition configuration on `Fin 4` has cross-degree pair-cost
infimum `3`. -/
theorem ciInf_sum_distErr_fin_four_four_of_eq_setOf_isSwap (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ β : Fin 4 → Perm (Fin 4),
        ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
          distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 3 := by
  rw [ciInf_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps 4]
  norm_num

/-- In every degree `m ≥ 5`, the three-transposition configuration on `Fin 4` has cross-degree
pair-cost infimum at least `18 / 5`. -/
theorem eighteen_div_five_le_ciInf_sum_distErr_fin_four_of_eq_setOf_isSwap_of_five_le
    (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap})
    {m : ℕ} (hm : 5 ≤ m) :
    (18 : ℝ) / 5 ≤ ⨅ β : Fin 4 → Perm (Fin m),
      ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
        distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  rw [ciInf_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps m,
    Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]
  have hm' : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hdiv : ((4 * 3 : ℕ) : ℝ) / m ≤ 12 / 5 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    norm_num
    linarith
  linarith

/-- Every gauge `β : Fin 4 → Perm (Fin m)` of every degree `m : ℕ` has cross-degree pair cost at
least `2` against the three-transposition configuration on `Fin 4`. -/
theorem two_le_sum_distErr_fin_four_of_eq_setOf_isSwap (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap})
    {m : ℕ} (β : Fin 4 → Perm (Fin m)) :
    2 ≤ ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
      distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  have hbdd : BddBelow (Set.range fun β' : Fin 4 → Perm (Fin m) =>
      ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
        distErr (α e.1 e.2) (β' e.1 * (β' e.2)⁻¹)) :=
    ⟨0, by rintro _ ⟨β', rfl⟩; exact sum_nonneg fun _ _ => distErr_nonneg _ _⟩
  refine le_trans ?_ (ciInf_le hbdd β)
  rw [ciInf_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps m]
  by_cases hm : m ≤ 3
  · rw [Nat.min_eq_right hm, Nat.max_eq_left hm]
    have hm' : (m : ℝ) ≤ 3 := by exact_mod_cast hm
    have hcast : ((4 * m : ℕ) : ℝ) = 4 * (m : ℝ) := by push_cast; ring
    rw [hcast]
    linarith
  · rw [Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]
    have hm4 : 4 ≤ m := by omega
    have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm4
    have hdiv : ((4 * 3 : ℕ) : ℝ) / m ≤ 3 := by
      rw [div_le_iff₀ (by positivity)]
      norm_num
      linarith
    linarith

/-- Across all gauge degrees `m + 2 ≥ 2`, the global cross-degree pair-cost infimum of the
three-transposition configuration on `Fin 4` is `2`, attained at equal degree `3`. -/
theorem ciInf₂_sum_distErr_fin_four_of_eq_setOf_isSwap (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ (m : ℕ) (β : Fin 4 → Perm (Fin (m + 2))),
        ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
          distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 2 := by
  let f (m : ℕ) : ℝ := ⨅ β : Fin 4 → Perm (Fin (m + 2)),
    ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
      distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)
  have hf_ge (m : ℕ) : 2 ≤ f m :=
    le_ciInf (two_le_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps)
  have hbdd : BddBelow (Set.range f) := ⟨2, by rintro _ ⟨m, rfl⟩; exact hf_ge m⟩
  refine le_antisymm ?_ (le_ciInf hf_ge)
  exact (ciInf_le hbdd 1).trans_eq
    (ciInf_sum_distErr_fin_four_three_of_eq_setOf_isSwap α h0 hswaps)

/-! ### Lexicographic cluster replication of cross-degree pair costs -/

section Replication

variable {V ι : Type*} [Fintype V] [LinearOrder V] [Fintype ι] [LinearOrder ι] {n : ℕ}

/-- Exact degree-`m` cross-degree pair-cost infimum under lexicographic cluster replication along
`V ×ₗ ι` with identity labels inside clusters: the `Fintype.card V * (Fintype.card ι).choose 2`
intra-cluster edges contribute their baseline `1 - min n m / max n m`, while the inter-cluster
edges contribute `Fintype.card ι ^ 2` times the base degree-`m` infimum. -/
theorem ciInf_sum_distErr_lex (α : V → V → Perm (Fin n)) (m : ℕ) :
    (⨅ β : (V ×ₗ ι) → Perm (Fin m),
        ∑ e ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι))),
          distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
            (β e.1 * (β e.2)⁻¹)) =
      (Fintype.card V * (Fintype.card ι).choose 2 : ℕ) * (1 - (min n m : ℝ) / max n m) +
        (Fintype.card ι : ℝ) ^ 2 *
          ⨅ β₀ : V → Perm (Fin m),
            ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
              distErr (α e.1 e.2) (β₀ e.1 * (β₀ e.2)⁻¹) := by
  set EV : Finset (V × V) := {p : V × V | p.1 < p.2}
  set Q : Finset (ι × ι) := {q : ι × ι | q.1 < q.2} with hQ_def
  let b₀ : ℝ := 1 - (min n m : ℝ) / max n m
  let base : ℝ := (Fintype.card V * (Fintype.card ι).choose 2 : ℕ) * b₀
  have hQ : #Q = (Fintype.card ι).choose 2 := by
    simpa [Q, ← univ_product_univ] using card_product_filter_lt (s := (univ : Finset ι))
  -- Reindex gauges as curried families `V → ι → Perm (Fin m)` and isolate the intra-cluster
  -- excess over the baseline `b₀`.
  let ev : (V → ι → Perm (Fin m)) ≃ ((V ×ₗ ι) → Perm (Fin m)) :=
    (Equiv.curry V ι (Perm (Fin m))).symm.trans (Equiv.arrowCongr toLex (.refl _))
  have hev (β' : V → ι → Perm (Fin m)) (v : V) (a : ι) : ev β' (toLex (v, a)) = β' v a := by
    simp [ev]
  let c (β' : V → ι → Perm (Fin m)) : ℝ :=
    ∑ v : V, ∑ q ∈ Q, (distErr (1 : Perm (Fin n)) (β' v q.1 * (β' v q.2)⁻¹) - b₀)
  have hc (β' : V → ι → Perm (Fin m)) : 0 ≤ c β' :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
      sub_nonneg.mpr (one_sub_min_div_max_le_distErr _ _)
  have hc_const (β₀ : V → Perm (Fin m)) : c (fun v _ => β₀ v) = 0 := by simp [c, b₀]
  -- Split the lexicographic edge sum into intra-cluster and inter-cluster pairs.
  have hsplit (β' : V → ι → Perm (Fin m)) :
      (∑ e ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι))),
        distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
          (ev β' e.1 * (ev β' e.2)⁻¹)) =
        base + (c β' + ∑ e ∈ EV, ∑ a : ι, ∑ b : ι,
          distErr (α e.1 e.2) (β' e.1 a * (β' e.2 b)⁻¹)) := by
    rw [Fintype.sum_filter_lt_lex (V := V) (ι := ι)]
    dsimp only [ofLex_toLex]
    simp only [↓reduceIte, hev]
    have hintra : (∑ v : V, ∑ q : ι × ι with q.1 < q.2,
        distErr (1 : Perm (Fin n)) (β' v q.1 * (β' v q.2)⁻¹)) = base + c β' := by
      have hterm (v : V) : (∑ q ∈ Q, distErr (1 : Perm (Fin n)) (β' v q.1 * (β' v q.2)⁻¹)) =
          (#Q : ℝ) * b₀ +
            ∑ q ∈ Q, (distErr (1 : Perm (Fin n)) (β' v q.1 * (β' v q.2)⁻¹) - b₀) := by
        simp [sum_sub_distrib, nsmul_eq_mul]
      simp_rw [← hQ_def]
      simp only [hterm, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
        hQ, base, c, Nat.cast_mul, mul_assoc]
    rw [hintra, add_assoc]
    congr 2
    exact sum_congr rfl fun e he => by simp [ne_of_lt (mem_filter.mp he).2]
  rw [← ev.iInf_congr hsplit]
  have hbdd : BddBelow (Set.range fun β' : V → ι → Perm (Fin m) =>
      c β' + ∑ e ∈ EV, ∑ a : ι, ∑ b : ι, distErr (α e.1 e.2) (β' e.1 a * (β' e.2 b)⁻¹)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨β', rfl⟩
    exact add_nonneg (hc β')
      (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => distErr_nonneg _ _)
  rw [← add_ciInf hbdd base,
    EV.ciInf_add_sum_eq_card_sq_mul_ciInf_sum (fun _ he => ne_of_lt (mem_filter.mp he).2)
      (fun e g h => distErr (α e.1 e.2) (g * h⁻¹)) c hc hc_const]

/-- Replicating `V` along `V ×ₗ ι` with identity labels inside each cluster multiplies the
degree-`m` cross-degree pair-cost infimum by at least `Fintype.card ι ^ 2`, for every `m : ℕ`. -/
theorem card_sq_mul_ciInf_le_ciInf_sum_distErr_lex (α : V → V → Perm (Fin n)) (m : ℕ) :
    (Fintype.card ι : ℝ) ^ 2 *
        (⨅ β₀ : V → Perm (Fin m),
          ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
            distErr (α e.1 e.2) (β₀ e.1 * (β₀ e.2)⁻¹)) ≤
      ⨅ β : (V ×ₗ ι) → Perm (Fin m),
        ∑ e ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι))),
          distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
            (β e.1 * (β e.2)⁻¹) := by
  rw [ciInf_sum_distErr_lex α m, ← distErr_one_one]
  exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (distErr_nonneg 1 1))

/-- In equal nonzero degree `n`, lexicographic cluster replication multiplies the cross-degree
pair-cost infimum by `Fintype.card ι ^ 2` with equality, because cluster-constant gauges have zero
intra-cluster distance with errors. -/
theorem ciInf_sum_distErr_lex_eq_card_sq_mul_ciInf [NeZero n] (α : V → V → Perm (Fin n)) :
    (⨅ β : (V ×ₗ ι) → Perm (Fin n),
        ∑ e ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι))),
          distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
            (β e.1 * (β e.2)⁻¹)) =
      (Fintype.card ι : ℝ) ^ 2 *
        ⨅ β₀ : V → Perm (Fin n),
          ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
            distErr (α e.1 e.2) (β₀ e.1 * (β₀ e.2)⁻¹) := by
  rw [ciInf_sum_distErr_lex α n, ← distErr_one_one, distErr_self, mul_zero, zero_add]

/-- Whenever a degree-`n` edge assignment (`2 ≤ n`) on `V` attains its cross-degree pair-cost
infimum over all gauge degrees `m + 2 ≥ 2` at its own degree `n`, its lexicographic replication on
`V ×ₗ ι` also attains its cross-degree infimum at degree `n`, with value multiplied by
`Fintype.card ι ^ 2`. -/
theorem ciInf₂_sum_distErr_lex_eq_card_sq_mul_ciInf_of_le_of_forall_le (α : V → V → Perm (Fin n))
    (hn : 2 ≤ n)
    (hmin : ∀ m : ℕ,
      (⨅ β₀ : V → Perm (Fin n),
          ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
            distErr (α e.1 e.2) (β₀ e.1 * (β₀ e.2)⁻¹)) ≤
        ⨅ β₀ : V → Perm (Fin (m + 2)),
          ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
            distErr (α e.1 e.2) (β₀ e.1 * (β₀ e.2)⁻¹)) :
    (⨅ (m : ℕ) (β : (V ×ₗ ι) → Perm (Fin (m + 2))),
        ∑ e ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι))),
          distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
            (β e.1 * (β e.2)⁻¹)) =
      (Fintype.card ι : ℝ) ^ 2 *
        ⨅ β₀ : V → Perm (Fin n),
          ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
            distErr (α e.1 e.2) (β₀ e.1 * (β₀ e.2)⁻¹) := by
  rcases Nat.exists_eq_add_of_le' hn with ⟨k, rfl⟩
  let F (m : ℕ) : ℝ := ⨅ β : (V ×ₗ ι) → Perm (Fin (m + 2)),
    ∑ e ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι))),
      distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
        (β e.1 * (β e.2)⁻¹)
  have hF_nonneg (m : ℕ) : 0 ≤ F m :=
    le_ciInf fun _ => sum_nonneg fun _ _ => distErr_nonneg _ _
  have hbdd : BddBelow (Set.range F) := ⟨0, by rintro _ ⟨m, rfl⟩; exact hF_nonneg m⟩
  refine le_antisymm ?_ ?_
  · exact (ciInf_le hbdd k).trans_eq (ciInf_sum_distErr_lex_eq_card_sq_mul_ciInf α)
  · refine le_ciInf fun m => ?_
    exact (mul_le_mul_of_nonneg_left (hmin m) (sq_nonneg _)).trans
      (card_sq_mul_ciInf_le_ciInf_sum_distErr_lex α (m + 2))

end Replication

/-- Replicating the three-transposition configuration on `Fin 4` along `Fin 4 ×ₗ ι` yields exact
cross-degree pair-cost infimum `2 * Fintype.card ι ^ 2` across all gauge degrees `m + 2 ≥ 2`. -/
theorem ciInf₂_sum_distErr_lex_fin_four_of_eq_setOf_isSwap {ι : Type*} [Fintype ι] [LinearOrder ι]
    (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ (m : ℕ) (β : (Fin 4 ×ₗ ι) → Perm (Fin (m + 2))),
        ∑ e ∈ ({p : (Fin 4 ×ₗ ι) × (Fin 4 ×ₗ ι) | p.1 < p.2} :
            Finset ((Fin 4 ×ₗ ι) × (Fin 4 ×ₗ ι))),
          distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
            (β e.1 * (β e.2)⁻¹)) =
      2 * (Fintype.card ι : ℝ) ^ 2 := by
  have h := ciInf₂_sum_distErr_lex_eq_card_sq_mul_ciInf_of_le_of_forall_le (ι := ι) α (by decide)
    fun m => by
      rw [ciInf_sum_distErr_fin_four_three_of_eq_setOf_isSwap α h0 hswaps]
      exact le_ciInf (two_le_sum_distErr_fin_four_of_eq_setOf_isSwap α h0 hswaps)
  rw [h, ciInf_sum_distErr_fin_four_three_of_eq_setOf_isSwap α h0 hswaps]
  ring

end TauCeti

end
