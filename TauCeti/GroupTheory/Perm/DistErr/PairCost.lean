/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Order.Prod.Lex.Basic
public import TauCeti.GroupTheory.Perm.DistErr.Invariance
import Mathlib.Basic.Real.Pointwise
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Optimization.Replication
import TauCeti.GroupTheory.Perm.FinThree.Basic

/-!
# Cross-degree pair costs, fiber bounds, and lexicographic replication

Given directed edges carrying permutations in `Equiv.Perm (Fin n)` and a vertex gauge taking values
in `Equiv.Perm (Fin m)` of possibly different degree, the cross-degree pair cost sums
`Equiv.Perm.distErr (α u v) (β u * (β v)⁻¹)` across edges `(u, v)`. This file develops the
combinatorial tools needed to evaluate and bound these sums and their infima over all gauge degrees:

* **Fiber decomposition** (`Equiv.Perm.agreeCount_mul_inv_eq_card_filter`,
  `Finset.sum_agreeCount_mul_inv_le_of_forall_option`, and
  `Finset.card_sub_four_mul_min_div_le_sum_distErr_mul_inv`): indexing agreements on `β u * (β v)⁻¹`
  by `y : Fin m` decomposes the total agreement count across `m` partial vertex colourings
  `V → Option (Fin n)` of total domain size `Fintype.card V * min n m`. On four linearly ordered
  vertices, partial colourings of size at most `3` satisfy at most `(#S).choose 2 ≤ #S` edges
  automatically, reducing cross-degree lower bounds for every `m` to total functions `V → Fin n`.
* **Cross-degree gauge invariance for `n ≤ m`** (`Finset.ciInf_sum_distErr_conj_eq`): changing `α`
  by a degree-`n` vertex gauge `γ : V → Perm (Fin n)` leaves the degree-`m` gauge-cost infimum
  unchanged whenever `n ≤ m`.
* **Exact three-transposition optimization on `Fin 4`**
  (`TauCeti.ciInf_sum_distErr_fin_four_three_swaps` and
  `TauCeti.iInf_sum_distErr_fin_four_three_swaps`): when `α 0 v = 1` for `0 < v` and
  `{α 1 2, α 1 3, α 2 3}` consists of the three transpositions of `Perm (Fin 3)`, the constant gauge
  `1` is globally optimal in every degree `m : ℕ`, giving exact infimum
  `6 - 4 * min 3 m / max 3 m` (`14 / 3` at `m = 1`, `10 / 3` at `m = 2`, `2` at `m = 3`, `3` at
  `m = 4`, at least `18 / 5` for `m ≥ 5`, and global cross-degree infimum `2`).
* **Lexicographic cluster replication** (`TauCeti.card_sq_mul_ciInf_le_ciInf_sum_distErr_lex`,
  `TauCeti.ciInf_sum_distErr_lex_eq`, `TauCeti.iInf_sum_distErr_lex_eq`, and
  `TauCeti.iInf_sum_distErr_lex_fin_four_three_swaps`): replicating vertices along `V ×ₗ ι` with
  identity labels inside clusters multiplies cross-degree gauge-cost infima by `Fintype.card ι ^ 2`
  at every degree `m` (as a lower bound) and identically across all degrees `m ≥ 2` whenever the
  base edge labels attain their cross-degree infimum in their own degree.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Section 3.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, Lemma 6 and Proposition 10.
-/

public section

open Finset

namespace Equiv.Perm

variable {n m : ℕ}

/-- A permutation of `Fin m` maps exactly `min n m` indices into `{0, ..., n - 1}`. -/
theorem card_filter_val_lt (β : Perm (Fin m)) (n : ℕ) :
    #{y : Fin m | (β y : ℕ) < n} = min n m := by
  have hcard : #(univ : Finset (Fin (min n m))) = #{z : Fin m | (z : ℕ) < n} := by
    refine card_bij (fun (j : Fin (min n m)) _ => j.castLE (min_le_right n m))
      (fun j _ => ?_) (fun _ _ _ _ h => Fin.castLE_injective _ h) (fun z hz => ?_)
    · simp only [mem_filter, mem_univ, true_and, Fin.val_castLE]
      exact lt_of_lt_of_le j.isLt (min_le_left n m)
    · simp only [mem_filter, mem_univ, true_and] at hz
      exact ⟨⟨z, lt_min hz z.isLt⟩, mem_univ _, Fin.ext rfl⟩
  have hmin : #(univ : Finset (Fin (min n m))) = min n m := by simp
  rw [← hmin, hcard]
  exact card_equiv β fun _ => by simp

/-- Agreements between `σ : Perm (Fin n)` and a degree-`m` quotient `g * h⁻¹` correspond
bijectively to fibers `y : Fin m` at which `h y` lies below `n` and `g y` matches `σ (h y)`. -/
theorem agreeCount_mul_inv_eq_card_filter (σ : Perm (Fin n)) (g h : Perm (Fin m)) :
    agreeCount σ (g * h⁻¹) =
      #{y : Fin m | ∃ i : Fin n, (h y : ℕ) = i ∧ (g y : ℕ) = σ i} := by
  rw [agreeCount_def]
  set h₁ := min_le_left n m
  set h₂ := min_le_right n m
  refine card_bij (fun j _ => h⁻¹ (j.castLE h₂)) (fun j hj => ?_)
    (fun _ _ _ _ heq => Fin.castLE_injective h₂ (h⁻¹.injective heq)) (fun y hy => ?_)
  · rw [mem_filter] at hj ⊢
    refine ⟨mem_univ _, j.castLE h₁, by simp, ?_⟩
    simpa [mul_apply] using hj.2.symm
  · rw [mem_filter] at hy
    rcases hy.2 with ⟨i, hh, hg⟩
    let j : Fin (min n m) := ⟨h y, lt_min (hh ▸ i.isLt) (h y).isLt⟩
    have hc₁ : j.castLE h₁ = i := Fin.ext hh
    have hc₂ : j.castLE h₂ = h y := Fin.ext rfl
    refine ⟨j, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · rw [mul_apply, hc₁, hc₂]
      simp [hg]
    · rw [hc₂]
      simp

end Equiv.Perm

namespace Finset

open Equiv Equiv.Perm

variable {ι V : Type*} {n m : ℕ}

/-! ### Edge-sum identities and degree-mismatch baselines -/

/-- Summing `distErr` over a finite set expresses the total cost in terms of `#s` minus the
normalized total agreement count. -/
theorem sum_distErr_eq_card_sub_div (s : Finset ι) (f : ι → Perm (Fin n)) (g : ι → Perm (Fin m)) :
    (∑ x ∈ s, distErr (f x) (g x)) =
      (#s : ℝ) - ((∑ x ∈ s, agreeCount (f x) (g x) : ℕ) : ℝ) / max n m := by
  simp only [distErr_def, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, div_eq_mul_inv,
    ← sum_mul, Nat.cast_sum]

/-- Every sum of `distErr` over `s` is at least `#s * (1 - min n m / max n m)`. -/
theorem card_mul_one_sub_min_div_max_le_sum_distErr (s : Finset ι) (f : ι → Perm (Fin n))
    (g : ι → Perm (Fin m)) :
    (#s : ℝ) * (1 - (min n m : ℝ) / max n m) ≤ ∑ x ∈ s, distErr (f x) (g x) := by
  simpa [nsmul_eq_mul] using
    s.card_nsmul_le_sum _ _ fun x _ => one_sub_min_div_max_le_distErr (f x) (g x)

/-- Comparing permutations of degree `3` against permutations of any unequal degree `m ≥ 2` over a
finite set `s` has total distance with errors at least `#s / 4`. -/
theorem card_div_four_le_sum_distErr_three_of_ne (s : Finset ι) (f : ι → Perm (Fin 3))
    (g : ι → Perm (Fin m)) (hm : 2 ≤ m) (hne : m ≠ 3) :
    (#s : ℝ) / 4 ≤ ∑ x ∈ s, distErr (f x) (g x) := by
  have h := s.card_nsmul_le_sum _ _ fun x _ =>
    one_div_four_le_distErr_three_of_ne (f x) (g x) hm hne
  simpa [nsmul_eq_mul, div_eq_mul_inv] using h

/-- When `n ≤ m`, transforming `α` by a degree-`n` vertex gauge `γ : V → Perm (Fin n)` preserves the
infimum of the degree-`m` cross-degree pair cost over `E`. -/
theorem ciInf_sum_distErr_conj_eq (E : Finset (V × V)) (α : V → V → Perm (Fin n))
    (γ : V → Perm (Fin n)) (hnm : n ≤ m) :
    (⨅ β : V → Perm (Fin m),
        ∑ e ∈ E, distErr ((γ e.1)⁻¹ * α e.1 e.2 * γ e.2) (β e.1 * (β e.2)⁻¹)) =
      ⨅ β : V → Perm (Fin m), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  let emb : V → Perm (Fin m) := fun v => (γ v).viaEmbedding (Fin.castLEEmb hnm)
  let ev : (V → Perm (Fin m)) ≃ (V → Perm (Fin m)) :=
    { toFun := fun β v => emb v * β v
      invFun := fun β v => (emb v)⁻¹ * β v
      left_inv := fun β => funext fun v => inv_mul_cancel_left (emb v) (β v)
      right_inv := fun β => funext fun v => mul_inv_cancel_left (emb v) (β v) }
  exact ev.iInf_congr fun β =>
    sum_congr rfl fun e _ =>
      (distErr_conj_mul_inv (α e.1 e.2) (γ e.1) (γ e.2) (β e.1) (β e.2) hnm).symm

/-! ### Fiber counting and partial colourings -/

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
    rw [sum_const, card_univ, smul_eq_mul]
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

/-- On a 4-element linearly ordered vertex set with strictly increasing edges, bounding total
agreements across every degree `m` reduces to showing that every total function `f : V → Fin n`
satisfies at most `4` edges of `E`. -/
theorem sum_agreeCount_mul_inv_le_four_mul_min [Fintype V] [LinearOrder V] (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (β : V → Perm (Fin m))
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

/-- Distance-with-errors consequence of `Finset.sum_agreeCount_mul_inv_le_four_mul_min`. -/
theorem card_sub_four_mul_min_div_le_sum_distErr_mul_inv [Fintype V] [LinearOrder V]
    (E : Finset (V × V)) (α : V → V → Perm (Fin n)) (β : V → Perm (Fin m))
    (hV : Fintype.card V = 4) (hE : ∀ e ∈ E, e.1 < e.2)
    (hf : ∀ f : V → Fin n, #{e ∈ E | f e.1 = α e.1 e.2 (f e.2)} ≤ 4) :
    (#E : ℝ) - ((4 * min n m : ℕ) : ℝ) / max n m ≤
      ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  rw [E.sum_distErr_eq_card_sub_div (fun e => α e.1 e.2) (fun e => β e.1 * (β e.2)⁻¹)]
  gcongr
  exact_mod_cast E.sum_agreeCount_mul_inv_le_four_mul_min α β hV hE hf

end Finset

namespace TauCeti

open Equiv Equiv.Perm

/-! ### Exact cross-degree optimization for the three-transposition configuration on `Fin 4` -/

private theorem isSwap_fin_three_iff (σ : Perm (Fin 3)) :
    σ.IsSwap ↔ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 1 2 := by
  rcases fin_three_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨fun h => ?_, fun h => absurd h (by decide)⟩
    have hs := h.sign_eq
    norm_num at hs
  · exact ⟨fun _ => Or.inl rfl, fun _ => swap_isSwap_iff.mpr (by decide)⟩
  · exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => swap_isSwap_iff.mpr (by decide)⟩
  · exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => swap_isSwap_iff.mpr (by decide)⟩
  · refine ⟨fun h => ?_, fun h => absurd h (by decide)⟩
    have hs : Perm.sign (finRotate 3) = 1 := by decide
    exact absurd (hs.symm.trans h.sign_eq) (by decide)
  · refine ⟨fun h => ?_, fun h => absurd h (by decide)⟩
    have hs : Perm.sign (finRotate 3)⁻¹ = 1 := by decide
    exact absurd (hs.symm.trans h.sign_eq) (by decide)

private theorem finset_three_swaps_eq {α : Fin 4 → Fin 4 → Perm (Fin 3)}
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    ({α 1 2, α 1 3, α 2 3} : Finset (Perm (Fin 3))) =
      {Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2} := by
  rw [← coe_inj]
  ext σ
  simpa [isSwap_fin_three_iff] using Set.ext_iff.mp hswaps σ

/-- When the star of `0 : Fin 4` carries `1` and the opposite triangle `{1, 2, 3}` carries the three
transpositions of `Perm (Fin 3)`, no function `f : Fin 4 → Fin 3` is compatible with more than `4`
of the `6` edges `u < v`. -/
theorem card_filter_lt_eq_apply_le_four (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap})
    (f : Fin 4 → Fin 3) :
    #{e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)) |
      f e.1 = α e.1 e.2 (f e.2)} ≤ 4 := by
  have hfin := finset_three_swaps_eq hswaps
  let S : Finset (Perm (Fin 3)) := {Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2}
  have h12 : α 1 2 ∈ S := by dsimp only [S]; rw [← hfin]; simp
  have h13 : α 1 3 ∈ S := by dsimp only [S]; rw [← hfin]; simp
  have h23 : α 2 3 ∈ S := by dsimp only [S]; rw [← hfin]; simp
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

private theorem sum_three_swaps_agreeCount_one (m : ℕ) :
    (∑ σ ∈ ({Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2} : Finset (Perm (Fin 3))),
      agreeCount σ (1 : Perm (Fin m))) = min 3 m := by
  repeat rw [sum_insert (by decide)]
  rw [sum_singleton]
  simp only [agreeCount_def, coe_one, id_eq, Fin.val_castLE, card_filter]
  rw [← sum_add_distrib, ← sum_add_distrib]
  have hone (j : Fin (min 3 m)) :
      (if (Equiv.swap (0 : Fin 3) 1 (j.castLE (min_le_left 3 m)) : ℕ) = j then 1 else 0) +
        ((if (Equiv.swap (0 : Fin 3) 2 (j.castLE (min_le_left 3 m)) : ℕ) = j then 1 else 0) +
          (if (Equiv.swap (1 : Fin 3) 2 (j.castLE (min_le_left 3 m)) : ℕ) = j then 1 else 0)) =
        1 := by
    have hpt : ∀ x : Fin 3,
        (if (Equiv.swap (0 : Fin 3) 1 x : ℕ) = x then 1 else 0) +
          ((if (Equiv.swap (0 : Fin 3) 2 x : ℕ) = x then 1 else 0) +
            (if (Equiv.swap (1 : Fin 3) 2 x : ℕ) = x then 1 else 0)) = 1 := by decide
    simpa using hpt (j.castLE (min_le_left 3 m))
  simp_rw [hone]
  simp

/-- Against the identity permutation of degree `m`, the three-transposition configuration on `Fin 4`
has exactly `4 * min 3 m` agreements across the `6` edges `u < v`. -/
theorem sum_agreeCount_one_fin_four_three_swaps (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) (m : ℕ) :
    (∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
        agreeCount (α e.1 e.2) (1 : Perm (Fin m))) = 4 * min 3 m := by
  have hfin := finset_three_swaps_eq hswaps
  have hcard3 : #({α 1 2, α 1 3, α 2 3} : Finset (Perm (Fin 3))) = 3 := by
    rw [hfin]; decide
  have hnotMem : α 1 2 ∉ ({α 1 3, α 2 3} : Finset (Perm (Fin 3))) := by
    intro h
    rw [insert_eq_of_mem h] at hcard3
    have hle : #({α 1 3, α 2 3} : Finset (Perm (Fin 3))) ≤ 2 :=
      (card_insert_le _ _).trans (by simp)
    omega
  have hne13_23 : α 1 3 ≠ α 2 3 := by
    intro h
    rw [h, insert_eq_of_mem (mem_singleton_self _)] at hcard3
    have hle : #({α 1 2, α 2 3} : Finset (Perm (Fin 3))) ≤ 2 :=
      (card_insert_le _ _).trans (by simp)
    omega
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
    rw [sum_insert hnotMem, sum_insert (by simp [hne13_23]), sum_singleton]
  rw [hsum_swaps, hfin, sum_three_swaps_agreeCount_one]
  omega

/-- Against the constant gauge `fun _ => 1` of degree `m`, the three-transposition configuration on
`Fin 4` has cross-degree pair cost `6 - 4 * min 3 m / max 3 m`. -/
theorem sum_distErr_one_fin_four_three_swaps (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) (m : ℕ) :
    (∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
        distErr (α e.1 e.2) (1 : Perm (Fin m))) =
      6 - ((4 * min 3 m : ℕ) : ℝ) / max 3 m := by
  have hcard : #({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)) = 6 := by decide
  have hsum := Finset.sum_distErr_eq_card_sub_div
    ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4))
    (fun e => α e.1 e.2) (fun _ => (1 : Perm (Fin m)))
  rw [hsum, hcard, sum_agreeCount_one_fin_four_three_swaps α h0 hswaps m]
  norm_num

/-- Exact degree-`m` cross-degree pair-cost infimum for the three-transposition configuration on
`Fin 4`: for every `m : ℕ`, the infimum over `β : Fin 4 → Perm (Fin m)` equals
`6 - 4 * min 3 m / max 3 m`. -/
theorem ciInf_sum_distErr_fin_four_three_swaps (α : Fin 4 → Fin 4 → Perm (Fin 3))
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
    have h := E.card_sub_four_mul_min_div_le_sum_distErr_mul_inv α β (by simp)
      (fun _ he => (mem_filter.mp he).2) (card_filter_lt_eq_apply_le_four α h0 hswaps)
    simpa [hcard] using h
  have hbdd : BddBelow (Set.range fun β : Fin 4 → Perm (Fin m) =>
      ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) :=
    ⟨0, by rintro _ ⟨β, rfl⟩; exact sum_nonneg fun _ _ => distErr_nonneg _ _⟩
  refine le_antisymm ?_ (le_ciInf hlower)
  refine (ciInf_le hbdd (fun _ => (1 : Perm (Fin m)))).trans_eq ?_
  simpa using sum_distErr_one_fin_four_three_swaps α h0 hswaps m

/-- In degree `1`, the three-transposition configuration on `Fin 4` has cross-degree pair-cost
infimum `14 / 3`. -/
theorem ciInf_sum_distErr_fin_four_three_swaps_one (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ β : Fin 4 → Perm (Fin 1),
        ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
          distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 14 / 3 := by
  rw [ciInf_sum_distErr_fin_four_three_swaps α h0 hswaps 1]
  norm_num

/-- In degree `2`, the three-transposition configuration on `Fin 4` has cross-degree pair-cost
infimum `10 / 3`. -/
theorem ciInf_sum_distErr_fin_four_three_swaps_two (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ β : Fin 4 → Perm (Fin 2),
        ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
          distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 10 / 3 := by
  rw [ciInf_sum_distErr_fin_four_three_swaps α h0 hswaps 2]
  norm_num

/-- In equal degree `3`, the three-transposition configuration on `Fin 4` has cross-degree pair-cost
infimum `2`. -/
theorem ciInf_sum_distErr_fin_four_three_swaps_three (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ β : Fin 4 → Perm (Fin 3),
        ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
          distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 2 := by
  rw [ciInf_sum_distErr_fin_four_three_swaps α h0 hswaps 3]
  norm_num

/-- In degree `4`, the three-transposition configuration on `Fin 4` has cross-degree pair-cost
infimum `3`. -/
theorem ciInf_sum_distErr_fin_four_three_swaps_four (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ β : Fin 4 → Perm (Fin 4),
        ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
          distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 3 := by
  rw [ciInf_sum_distErr_fin_four_three_swaps α h0 hswaps 4]
  norm_num

/-- In every degree `m ≥ 5`, the three-transposition configuration on `Fin 4` has cross-degree
pair-cost infimum at least `18 / 5`. -/
theorem eighteen_div_five_le_ciInf_sum_distErr_fin_four_three_swaps
    (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap})
    {m : ℕ} (hm : 5 ≤ m) :
    (18 : ℝ) / 5 ≤ ⨅ β : Fin 4 → Perm (Fin m),
      ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
        distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  rw [ciInf_sum_distErr_fin_four_three_swaps α h0 hswaps m,
    Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]
  have hm' : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hdiv : ((4 * 3 : ℕ) : ℝ) / m ≤ 12 / 5 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    norm_num
    linarith
  linarith

/-- Every gauge `β : Fin 4 → Perm (Fin m)` of every degree `m : ℕ` has cross-degree pair cost at
least `2` against the three-transposition configuration on `Fin 4`. -/
theorem two_le_sum_distErr_fin_four_three_swaps (α : Fin 4 → Fin 4 → Perm (Fin 3))
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
  rw [ciInf_sum_distErr_fin_four_three_swaps α h0 hswaps m]
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
theorem iInf_sum_distErr_fin_four_three_swaps (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ (m : ℕ) (β : Fin 4 → Perm (Fin (m + 2))),
        ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
          distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 2 := by
  let f (m : ℕ) : ℝ := ⨅ β : Fin 4 → Perm (Fin (m + 2)),
    ∑ e ∈ ({p : Fin 4 × Fin 4 | p.1 < p.2} : Finset (Fin 4 × Fin 4)),
      distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)
  have hf_ge (m : ℕ) : 2 ≤ f m := le_ciInf (two_le_sum_distErr_fin_four_three_swaps α h0 hswaps)
  have hbdd : BddBelow (Set.range f) := ⟨2, by rintro _ ⟨m, rfl⟩; exact hf_ge m⟩
  refine le_antisymm ?_ (le_ciInf hf_ge)
  exact (ciInf_le hbdd 1).trans_eq (ciInf_sum_distErr_fin_four_three_swaps_three α h0 hswaps)

/-! ### Lexicographic cluster replication of cross-degree pair costs -/

section Replication

variable {V ι : Type*} [Fintype V] [LinearOrder V] [Fintype ι] [LinearOrder ι] {n : ℕ}

omit [LinearOrder ι] in
private theorem sum_filter_fst_lt_lex (w : (V ×ₗ ι) × (V ×ₗ ι) → ℝ) :
    (∑ p ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | (ofLex p.1).1 < (ofLex p.2).1} :
        Finset ((V ×ₗ ι) × (V ×ₗ ι))), w p) =
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        ∑ a : ι, ∑ b : ι, w (toLex (e.1, a), toLex (e.2, b)) := by
  set EV : Finset (V × V) := {p : V × V | p.1 < p.2}
  have hbij : (∑ p ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | (ofLex p.1).1 < (ofLex p.2).1} :
        Finset ((V ×ₗ ι) × (V ×ₗ ι))), w p) =
      ∑ q ∈ (EV ×ˢ (univ : Finset ι)) ×ˢ (univ : Finset ι),
        w (toLex (q.1.1.1, q.1.2), toLex (q.1.1.2, q.2)) := by
    refine (sum_bij (fun q _ => (toLex (q.1.1.1, q.1.2), toLex (q.1.1.2, q.2)))
      (fun q hq => ?_) (fun q₁ _ q₂ _ h => ?_) (fun p hp => ?_) (fun _ _ => rfl)).symm
    · simp only [mem_product, mem_filter, mem_univ, true_and, and_true, ofLex_toLex, EV] at hq ⊢
      exact hq
    · simp only [Prod.ext_iff, EmbeddingLike.apply_eq_iff_eq] at h
      ext <;> simp [h]
    · simp only [mem_filter, mem_univ, true_and] at hp
      refine ⟨((((ofLex p.1).1, (ofLex p.2).1), (ofLex p.1).2), (ofLex p.2).2), ?_, ?_⟩
      · simp [EV, hp]
      · simp [toLex_ofLex]
  rw [hbij, sum_product, sum_product]

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
  set EV : Finset (V × V) := {p : V × V | p.1 < p.2}
  set Elex : Finset ((V ×ₗ ι) × (V ×ₗ ι)) := {p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2}
  set Einter : Finset ((V ×ₗ ι) × (V ×ₗ ι)) :=
    {p : (V ×ₗ ι) × (V ×ₗ ι) | (ofLex p.1).1 < (ofLex p.2).1}
  have hsub : Einter ⊆ Elex := fun p hp => by
    simp only [mem_filter, mem_univ, true_and, Einter, Elex] at hp ⊢
    exact Prod.Lex.lt_iff.mpr (Or.inl hp)
  have hbdd₀ : BddBelow (Set.range fun β₀ : V → Perm (Fin m) =>
      ∑ e ∈ EV, distErr (α e.1 e.2) (β₀ e.1 * (β₀ e.2)⁻¹)) :=
    ⟨0, by rintro _ ⟨β₀, rfl⟩; exact sum_nonneg fun _ _ => distErr_nonneg _ _⟩
  refine le_ciInf fun β => ?_
  have hinter_le : (∑ e ∈ Einter,
      distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
        (β e.1 * (β e.2)⁻¹)) ≤
      ∑ e ∈ Elex,
        distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
          (β e.1 * (β e.2)⁻¹) :=
    sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => distErr_nonneg _ _
  refine le_trans ?_ hinter_le
  rw [sum_filter_fst_lt_lex]
  have hsimp : (∑ e ∈ EV, ∑ a : ι, ∑ b : ι,
      distErr (if (ofLex (toLex (e.1, a), toLex (e.2, b)).1).1 =
          (ofLex (toLex (e.1, a), toLex (e.2, b)).2).1
        then 1 else α (ofLex (toLex (e.1, a), toLex (e.2, b)).1).1
          (ofLex (toLex (e.1, a), toLex (e.2, b)).2).1)
        (β (toLex (e.1, a)) * (β (toLex (e.2, b)))⁻¹)) =
      ∑ e ∈ EV, ∑ a : ι, ∑ b : ι,
        distErr (α e.1 e.2) (β (toLex (e.1, a)) * (β (toLex (e.2, b)))⁻¹) := by
    refine sum_congr rfl fun e he => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    split_ifs with h
    · exact absurd (by simpa using h : e.1 = e.2) (ne_of_lt (mem_filter.mp he).2)
    · rfl
  rw [hsimp]
  have hsec := EV.card_sq_nsmul_le_sum_of_forall_le_sum
    (fun _ he => ne_of_lt (mem_filter.mp he).2)
    (fun e a b => distErr (α e.1 e.2) (β (toLex (e.1, a)) * (β (toLex (e.2, b)))⁻¹))
    (fun s => ciInf_le hbdd₀ (fun v => β (toLex (v, s v))))
  simpa [nsmul_eq_mul, Nat.cast_pow] using hsec

/-- In equal nonzero degree `n`, lexicographic cluster replication multiplies the cross-degree
pair-cost infimum by `Fintype.card ι ^ 2` with equality, because cluster-constant gauges have zero
intra-cluster distance with errors. -/
theorem ciInf_sum_distErr_lex_eq [NeZero n] (α : V → V → Perm (Fin n)) :
    (⨅ β : (V ×ₗ ι) → Perm (Fin n),
        ∑ e ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι))),
          distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
            (β e.1 * (β e.2)⁻¹)) =
      (Fintype.card ι : ℝ) ^ 2 *
        ⨅ β₀ : V → Perm (Fin n),
          ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
            distErr (α e.1 e.2) (β₀ e.1 * (β₀ e.2)⁻¹) := by
  refine le_antisymm ?_ (card_sq_mul_ciInf_le_ciInf_sum_distErr_lex α n)
  set EV : Finset (V × V) := {p : V × V | p.1 < p.2}
  set Elex : Finset ((V ×ₗ ι) × (V ×ₗ ι)) := {p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2}
  set Einter : Finset ((V ×ₗ ι) × (V ×ₗ ι)) :=
    {p : (V ×ₗ ι) × (V ×ₗ ι) | (ofLex p.1).1 < (ofLex p.2).1}
  have hsub : Einter ⊆ Elex := fun p hp => by
    simp only [mem_filter, mem_univ, true_and, Einter, Elex] at hp ⊢
    exact Prod.Lex.lt_iff.mpr (Or.inl hp)
  have hbdd : BddBelow (Set.range fun β : (V ×ₗ ι) → Perm (Fin n) =>
      ∑ e ∈ Elex,
        distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
          (β e.1 * (β e.2)⁻¹)) :=
    ⟨0, by rintro _ ⟨β, rfl⟩; exact sum_nonneg fun _ _ => distErr_nonneg _ _⟩
  rw [Real.mul_iInf_of_nonneg (sq_nonneg (Fintype.card ι : ℝ))]
  refine le_ciInf fun β₀ => ?_
  refine (ciInf_le hbdd (fun x => β₀ (ofLex x).1)).trans_eq ?_
  have hvanish : (∑ e ∈ Elex,
      distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
        (β₀ (ofLex e.1).1 * (β₀ (ofLex e.2).1)⁻¹)) =
      ∑ e ∈ Einter,
        distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
          (β₀ (ofLex e.1).1 * (β₀ (ofLex e.2).1)⁻¹) := by
    refine (sum_subset hsub fun p hp hnot => ?_).symm
    simp only [mem_filter, mem_univ, true_and, Elex, Einter] at hp hnot
    rcases Prod.Lex.lt_iff.mp hp with hlt | ⟨heq, _⟩
    · exact absurd hlt hnot
    · simp [heq]
  rw [hvanish, sum_filter_fst_lt_lex, mul_sum]
  refine sum_congr rfl fun e he => ?_
  have hconst : (∑ a : ι, ∑ b : ι,
      distErr (if (ofLex (toLex (e.1, a), toLex (e.2, b)).1).1 =
          (ofLex (toLex (e.1, a), toLex (e.2, b)).2).1
        then 1 else α (ofLex (toLex (e.1, a), toLex (e.2, b)).1).1
          (ofLex (toLex (e.1, a), toLex (e.2, b)).2).1)
        (β₀ (ofLex (toLex (e.1, a))).1 * (β₀ (ofLex (toLex (e.2, b))).1)⁻¹)) =
      ∑ _a : ι, ∑ _b : ι, distErr (α e.1 e.2) (β₀ e.1 * (β₀ e.2)⁻¹) := by
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    split_ifs with h
    · exact absurd (by simpa using h : e.1 = e.2) (ne_of_lt (mem_filter.mp he).2)
    · rfl
  rw [hconst]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  ring

/-- Whenever a degree-`(k + 2)` edge assignment on `V` attains its cross-degree pair-cost infimum
over all degrees `m + 2 ≥ 2` at its own degree `k + 2`, its lexicographic replication on `V ×ₗ ι`
also attains its cross-degree infimum at degree `k + 2`, with value multiplied by
`Fintype.card ι ^ 2`. -/
theorem iInf_sum_distErr_lex_eq {k : ℕ} (α : V → V → Perm (Fin (k + 2)))
    (hmin : ∀ m : ℕ,
      (⨅ β₀ : V → Perm (Fin (k + 2)),
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
        ⨅ β₀ : V → Perm (Fin (k + 2)),
          ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
            distErr (α e.1 e.2) (β₀ e.1 * (β₀ e.2)⁻¹) := by
  let F (m : ℕ) : ℝ := ⨅ β : (V ×ₗ ι) → Perm (Fin (m + 2)),
    ∑ e ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι))),
      distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
        (β e.1 * (β e.2)⁻¹)
  have hF_nonneg (m : ℕ) : 0 ≤ F m :=
    le_ciInf fun _ => sum_nonneg fun _ _ => distErr_nonneg _ _
  have hbdd : BddBelow (Set.range F) := ⟨0, by rintro _ ⟨m, rfl⟩; exact hF_nonneg m⟩
  refine le_antisymm ?_ ?_
  · exact (ciInf_le hbdd k).trans_eq (ciInf_sum_distErr_lex_eq α)
  · refine le_ciInf fun m => ?_
    exact (mul_le_mul_of_nonneg_left (hmin m) (sq_nonneg _)).trans
      (card_sq_mul_ciInf_le_ciInf_sum_distErr_lex α (m + 2))

end Replication

/-- Replicating the three-transposition configuration on `Fin 4` along `Fin 4 ×ₗ ι` yields exact
cross-degree pair-cost infimum `2 * Fintype.card ι ^ 2` across all gauge degrees `m + 2 ≥ 2`. -/
theorem iInf_sum_distErr_lex_fin_four_three_swaps {ι : Type*} [Fintype ι] [LinearOrder ι]
    (α : Fin 4 → Fin 4 → Perm (Fin 3))
    (h0 : ∀ v : Fin 4, 0 < v → α 0 v = 1)
    (hswaps : ({α 1 2, α 1 3, α 2 3} : Set (Perm (Fin 3))) = {σ | σ.IsSwap}) :
    (⨅ (m : ℕ) (β : (Fin 4 ×ₗ ι) → Perm (Fin (m + 2))),
        ∑ e ∈ ({p : (Fin 4 ×ₗ ι) × (Fin 4 ×ₗ ι) | p.1 < p.2} :
            Finset ((Fin 4 ×ₗ ι) × (Fin 4 ×ₗ ι))),
          distErr (if (ofLex e.1).1 = (ofLex e.2).1 then 1 else α (ofLex e.1).1 (ofLex e.2).1)
            (β e.1 * (β e.2)⁻¹)) =
      2 * (Fintype.card ι : ℝ) ^ 2 := by
  have h := iInf_sum_distErr_lex_eq (ι := ι) (k := 1) α fun m => by
    rw [ciInf_sum_distErr_fin_four_three_swaps_three α h0 hswaps]
    exact le_ciInf (two_le_sum_distErr_fin_four_three_swaps α h0 hswaps)
  rw [h, ciInf_sum_distErr_fin_four_three_swaps_three α h0 hswaps]
  ring

end TauCeti

end
