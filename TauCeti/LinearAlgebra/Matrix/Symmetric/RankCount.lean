/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Matrix.Symmetric.BorderRank

/-!
# MacWilliams's count of symmetric matrices of each rank over a finite field

Let `F` be a finite field with `q` elements and let `N(n, k)` be the number of symmetric `n × n`
matrices over `F` of rank `k`. Every characteristic is allowed: the diagonal is unrestricted, so in
characteristic two the alternating matrices are counted together with the others.

A symmetric `(n + 1) × (n + 1)` matrix is a symmetric `n × n` matrix `S` bordered by a column `v`,
its transpose and a corner `a`. When `S` has rank `r`, the border has rank `r` for `q ^ r` of the
pairs `(v, a)`, rank `r + 1` for `(q - 1) q ^ r` of them and rank `r + 2` for the remaining
`q ^ (n + 1) - q ^ (r + 1)`: a column in the range of `S` has one corner keeping the rank, and a
column outside it raises the rank by two. Grouping by `r` gives the recurrence
`N(n + 1, k) = ∑_{r ≤ n} N(n, r) c(n, r, k)` with these coefficients. MacWilliams's product
`P(s, k) = ∏_{i=1}^{⌊k/2⌋} q^(2i) / (q^(2i) - 1) · ∏_{i=0}^{k-1} (q^(s-i) - 1)` satisfies the same
recurrence and the same initial row, so `N(s, k) = P(s, k)` for all `s` and `k`.

## Main results

* `Matrix.IsSymm.natCard_rank_fromBlocks_eq`: the number of borders `(v, a)` of a symmetric `S`
  giving each rank.
* `Matrix.natCard_isSymm_rank_sum_unit` and `Matrix.natCard_isSymm_rank_succ`: the recurrence for
  the number of symmetric matrices of each rank.
* `Matrix.symmetricRankProduct_succ_eq_sum`: MacWilliams's product satisfies the same recurrence.
* `Matrix.natCard_isSymm_rank_eq_prod`: **MacWilliams's formula** for the number of symmetric
  `s × s` matrices of rank `k`.

## References

* R. P. Stanley, *Spanning trees and a conjecture of Kontsevich*, Ann. Comb. 2 (1998), 351–363,
  §4, First proof (J. MacWilliams), equations (4.2)–(4.3).
* J. MacWilliams, *Orthogonal matrices over finite fields*, Amer. Math. Monthly 76 (1969),
  152–164.
-/

public section

namespace Matrix

open Finset

section Finite

variable {F n : Type*} [Field F] [Finite F] [Fintype n] {S : Matrix n n F}

open Classical in
/-- The number of corners `a` for which bordering a symmetric `S` by the column `v` has rank `k`:
for `v` in the range of `S` one corner keeps the rank and the others raise it by one, and for `v`
outside the range every corner raises it by two. -/
private theorem IsSymm.natCard_corner_rank_eq (hS : S.IsSymm) (v : n → F) (k : ℕ) :
    Nat.card {a : F // (Matrix.fromBlocks S (replicateCol Unit v) (replicateRow Unit v)
      (of fun _ _ => a)).rank = k} =
      if v ∈ LinearMap.range S.mulVecLin then
        (if k = S.rank then 1 else if k = S.rank + 1 then Nat.card F - 1 else 0)
      else if k = S.rank + 2 then Nat.card F else 0 := by
  classical
  have := Fintype.ofFinite F
  by_cases hv : v ∈ LinearMap.range S.mulVecLin
  · simp only [hv, ↓reduceIte]
    obtain ⟨x, rfl⟩ := hv
    simp_rw [mulVecLin_apply, hS.rank_fromBlocks_mulVec]
    split_ifs with h₁ h₂
    · rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun a => a = x ⬝ᵥ S *ᵥ x)
        fun a => by split_ifs <;> simp_all), Nat.card_eq_fintype_card, Fintype.card_subtype_eq]
    · rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun a => ¬a = x ⬝ᵥ S *ᵥ x)
        fun a => by split_ifs <;> simp_all), Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq, Nat.card_eq_fintype_card]
    · rw [Nat.card_eq_zero]
      refine Or.inl ⟨fun ⟨a, ha⟩ => ?_⟩
      split_ifs at ha <;> omega
  · simp only [hS.rank_fromBlocks_of_notMem_range hv, hv, ↓reduceIte]
    split_ifs with h
    · rw [← h, Nat.card_eq_fintype_card]
      simp
    · simp [show S.rank + 2 ≠ k from fun e => h e.symm]

/-- **The rank fibres of the borders of a symmetric matrix.** If `S` is a symmetric `n × n` matrix
of rank `r` over a field with `q` elements, the pairs `(v, a)` for which the border
`[[S, v], [vᵀ, a]]` has rank `k` number `q ^ r` if `k = r`, `(q - 1) q ^ r` if `k = r + 1`,
`q ^ (n + 1) - q ^ (r + 1)` if `k = r + 2`, and none otherwise. -/
theorem IsSymm.natCard_rank_fromBlocks_eq (hS : S.IsSymm) (k : ℕ) :
    Nat.card {p : (n → F) × F // (Matrix.fromBlocks S (replicateCol Unit p.1)
      (replicateRow Unit p.1) (of fun _ _ => p.2)).rank = k} =
      if k = S.rank then Nat.card F ^ S.rank
      else if k = S.rank + 1 then (Nat.card F - 1) * Nat.card F ^ S.rank
      else if k = S.rank + 2 then Nat.card F ^ (Fintype.card n + 1) - Nat.card F ^ (S.rank + 1)
      else 0 := by
  classical
  have := Fintype.ofFinite F
  set W := LinearMap.range S.mulVecLin
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun v a =>
    (Matrix.fromBlocks S (replicateCol Unit v) (replicateRow Unit v) (of fun _ _ => a)).rank = k),
    Nat.card_sigma, Fintype.sum_congr _ _ fun v => hS.natCard_corner_rank_eq v k, sum_ite,
    sum_const, sum_const, smul_eq_mul, smul_eq_mul]
  -- The range of `S` has `q ^ r` elements, and its complement the remaining `q ^ n - q ^ r`.
  have hW : #{v | v ∈ W} = Nat.card F ^ S.rank := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := F), finrank_range_mulVecLin]
  have hWc := card_filter_add_card_filter_not (s := univ) (· ∈ W)
  rw [card_univ, Fintype.card_fun, ← Nat.card_eq_fintype_card, hW] at hWc
  rw [hW, show #{v | v ∉ W} = Nat.card F ^ Fintype.card n - Nat.card F ^ S.rank by omega]
  split_ifs <;> first
    | omega
    | rw [mul_zero, add_zero, mul_comm]
    | rw [mul_zero, zero_add, Nat.sub_mul, ← pow_succ, ← pow_succ]

end Finite

section Count

variable (F : Type*) [Field F]

/-- A symmetric matrix on `ι ⊕ Unit` is a symmetric matrix on `ι` bordered by a column, its
transpose and a corner. -/
private def isSymmSumUnitEquiv (ι : Type*) :
    {M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) F // M.IsSymm} ≃
      {S : Matrix ι ι F // S.IsSymm} × (ι → F) × F where
  toFun M := (⟨M.val.toBlocks₁₁,
    (isSymm_fromBlocks_iff.mp (M.val.fromBlocks_toBlocks ▸ M.property)).left⟩,
    fun i => M.val (.inl i) (.inr ()), M.val (.inr ()) (.inr ()))
  invFun p := ⟨Matrix.fromBlocks p.1.val (replicateCol Unit p.2.1) (replicateRow Unit p.2.1)
    (of fun _ _ => p.2.2), p.1.property.fromBlocks (by simp) (by ext; simp)⟩
  left_inv M := by
    ext (i | i) (j | _)
    · simp [toBlocks₁₁]
    · simp
    · simpa using (M.property.apply _ _).symm
    · simp
  right_inv p := by ext <;> simp [toBlocks₁₁]

variable [Finite F]

/-- **The symmetric rank count recurrence.** Group the symmetric matrices on `ι ⊕ Unit` of rank
`k` by the rank `r` of their principal `ι × ι` block: each symmetric block of rank `r` has
`q ^ r`, `(q - 1) q ^ r` or `q ^ (n + 1) - q ^ (r + 1)` borders of rank `k` according as
`k = r`, `r + 1` or `r + 2`, where `n` is the cardinality of `ι` and `q` that of the field. -/
theorem natCard_isSymm_rank_sum_unit (ι : Type*) [Fintype ι] (k : ℕ) :
    Nat.card {M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) F // M.IsSymm ∧ M.rank = k} =
      ∑ r ∈ range (Fintype.card ι + 1),
        Nat.card {S : Matrix ι ι F // S.IsSymm ∧ S.rank = r} *
          if k = r then Nat.card F ^ r
          else if k = r + 1 then (Nat.card F - 1) * Nat.card F ^ r
          else if k = r + 2 then Nat.card F ^ (Fintype.card ι + 1) - Nat.card F ^ (r + 1)
          else 0 := by
  classical
  have := Fintype.ofFinite F
  let P : {S : Matrix ι ι F // S.IsSymm} → (ι → F) × F → Prop := fun S p =>
    (Matrix.fromBlocks S.val (replicateCol Unit p.1) (replicateRow Unit p.1)
      (of fun _ _ => p.2)).rank = k
  have e₁ : {M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) F // M.IsSymm ∧ M.rank = k} ≃
      {M : {M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) F // M.IsSymm} // M.val.rank = k} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  have e₂ : {M : {M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) F // M.IsSymm} // M.val.rank = k} ≃
      {p : {S : Matrix ι ι F // S.IsSymm} × (ι → F) × F // P p.1 p.2} :=
    ((isSymmSumUnitEquiv F ι).symm.subtypeEquiv (p := fun p => P p.1 p.2)
      (q := fun M => M.val.rank = k) fun _ => Iff.rfl).symm
  set c : ℕ → ℕ := fun r => if k = r then Nat.card F ^ r
    else if k = r + 1 then (Nat.card F - 1) * Nat.card F ^ r
    else if k = r + 2 then Nat.card F ^ (Fintype.card ι + 1) - Nat.card F ^ (r + 1) else 0
  calc Nat.card {M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) F // M.IsSymm ∧ M.rank = k}
      = ∑ S : {S : Matrix ι ι F // S.IsSymm}, c S.val.rank := by
        rw [Nat.card_congr (e₁.trans <| e₂.trans (Equiv.subtypeProdEquivSigmaSubtype P)),
          Nat.card_sigma]
        exact Fintype.sum_congr _ _ fun S => S.property.natCard_rank_fromBlocks_eq k
    _ = _ := by
        -- Group the symmetric blocks by their rank.
        rw [← sum_fiberwise_of_maps_to' (t := range (Fintype.card ι + 1))
          (g := fun S : {S : Matrix ι ι F // S.IsSymm} => S.val.rank)
          (fun S _ => mem_range.mpr (Nat.lt_succ_of_le S.val.rank_le_card_width))]
        refine sum_congr rfl fun r _ => ?_
        rw [sum_const, smul_eq_mul, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
          Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun S : Matrix ι ι F => S.IsSymm) (fun S => S.rank = r))]

/-- **The symmetric rank count recurrence** for `(n + 1) × (n + 1)` matrices over a field with `q`
elements: `N(n + 1, k) = ∑_{r ≤ n} N(n, r) c(n, r, k)`, where `N(n, r)` counts the symmetric
`n × n` matrices of rank `r` and `c(n, r, k)` is `q ^ r`, `(q - 1) q ^ r` or
`q ^ (n + 1) - q ^ (r + 1)` according as `k = r`, `r + 1` or `r + 2`, and zero otherwise. -/
theorem natCard_isSymm_rank_succ (n k : ℕ) :
    Nat.card {M : Matrix (Fin (n + 1)) (Fin (n + 1)) F // M.IsSymm ∧ M.rank = k} =
      ∑ r ∈ range (n + 1),
        Nat.card {S : Matrix (Fin n) (Fin n) F // S.IsSymm ∧ S.rank = r} *
          if k = r then Nat.card F ^ r
          else if k = r + 1 then (Nat.card F - 1) * Nat.card F ^ r
          else if k = r + 2 then Nat.card F ^ (n + 1) - Nat.card F ^ (r + 1)
          else 0 := by
  have h := natCard_isSymm_rank_sum_unit F (Fin n) k
  rw [Fintype.card_fin] at h
  rw [← h]
  let e : Fin (n + 1) ≃ Fin n ⊕ Unit := finSumFinEquiv.symm.trans (.sumCongr (.refl _) finOneEquiv)
  exact Nat.card_congr <| (reindex e e).subtypeEquiv fun M => by
    rw [isSymm_reindex_iff, rank_reindex]

end Count

section Product

/-- A sum over `r ≤ n` of terms supported on `r + d = k` picks out `r = k - d`, provided the
summand vanishes beyond `n`. -/
private theorem sum_range_ite_add_eq {M : Type*} [AddCommMonoid M] (n d k : ℕ) (f : ℕ → M)
    (hf : ∀ t, n < t → f t = 0) :
    ∑ r ∈ range (n + 1), (if k = r + d then f r else 0) = if d ≤ k then f (k - d) else 0 := by
  split_ifs with hdk
  · simp_rw [show ∀ r, (k = r + d) ↔ (k - d = r) by omega, sum_ite_eq, mem_range]
    split_ifs with h
    · rfl
    · exact (hf _ (by omega)).symm
  · exact sum_eq_zero fun r _ => ite_eq_right_iff.mpr fun h => absurd h (by omega)

/-- Evaluate a sum against the border coefficients, for a sequence vanishing beyond `n`. -/
private theorem sum_mul_borderCoeff (q n k : ℕ) (g : ℕ → ℚ) (hg : ∀ t, n < t → g t = 0) :
    ∑ r ∈ range (n + 1), g r * ((if k = r then q ^ r
      else if k = r + 1 then (q - 1) * q ^ r
      else if k = r + 2 then q ^ (n + 1) - q ^ (r + 1) else 0 : ℕ) : ℚ) =
      g k * q ^ k + (if 1 ≤ k then g (k - 1) * ((q - 1) * q ^ (k - 1) : ℕ) else 0) +
        if 2 ≤ k then g (k - 2) * ((q ^ (n + 1) - q ^ (k - 2 + 1) : ℕ) : ℚ) else 0 := by
  have h0 := sum_range_ite_add_eq n 0 k (fun r => g r * (q ^ r : ℕ)) fun t ht => by simp [hg t ht]
  have h1 := sum_range_ite_add_eq n 1 k (fun r => g r * ((q - 1) * q ^ r : ℕ))
    fun t ht => by simp [hg t ht]
  have h2 := sum_range_ite_add_eq n 2 k (fun r => g r * ((q ^ (n + 1) - q ^ (r + 1) : ℕ) : ℚ))
    fun t ht => by simp [hg t ht]
  simp only [add_zero, zero_le, ↓reduceIte, Nat.sub_zero, Nat.cast_pow] at h0
  rw [← h1, ← h2, ← h0, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun r _ => ?_
  split_ifs <;> first | omega | simp

/-- MacWilliams's product `∏_{i=1}^{⌊t/2⌋} q^(2i) / (q^(2i) - 1) · ∏_{i=0}^{t-1} (q^(s-i) - 1)`. -/
private def symmRankProd (q s t : ℕ) : ℚ :=
  (∏ i ∈ range (t / 2), (q : ℚ) ^ (2 * (i + 1)) / ((q : ℚ) ^ (2 * (i + 1)) - 1)) *
    ∏ i ∈ range t, ((q : ℚ) ^ (s - i) - 1)

/-- MacWilliams's product vanishes beyond the diagonal, through its factor `q ^ 0 - 1`. -/
private theorem symmRankProd_of_lt {q s t : ℕ} (h : s < t) : symmRankProd q s t = 0 := by
  rw [symmRankProd, prod_eq_zero (mem_range.mpr h) (by simp), mul_zero]

/-- The three-term recurrence of MacWilliams's product in the range `2 ≤ k ≤ n`, written with
`n = j + 1 + m` and `k = j + 2`. -/
private theorem symmRankProd_add_two {q : ℕ} (hq : 2 ≤ q) (j m : ℕ) :
    symmRankProd q (j + 1 + m + 1) (j + 1 + 1) =
      symmRankProd q (j + 1 + m) (j + 1 + 1) * (q : ℚ) ^ (j + 1 + 1) +
        symmRankProd q (j + 1 + m) (j + 1) * (((q : ℚ) - 1) * (q : ℚ) ^ (j + 1)) +
        symmRankProd q (j + 1 + m) j * ((q : ℚ) ^ (j + m + 2) - (q : ℚ) ^ (j + 1)) := by
  have hX : (1 : ℚ) < q := by exact_mod_cast hq
  simp only [symmRankProd]
  set X : ℚ := (q : ℚ)
  -- Peel the last factors off the products over `i < j + 2` and `i < j + 1`.
  set Q := ∏ i ∈ range j, (X ^ (j + 1 + m - i) - 1)
  have hQ1 : ∏ i ∈ range (j + 1), (X ^ (j + 1 + m - i) - 1) = Q * (X ^ (m + 1) - 1) := by
    rw [prod_range_succ, show j + 1 + m - j = m + 1 by omega]
  have hQ2 : ∏ i ∈ range (j + 1 + 1), (X ^ (j + 1 + m - i) - 1) =
      Q * (X ^ (m + 1) - 1) * (X ^ m - 1) := by
    rw [prod_range_succ, hQ1, show j + 1 + m - (j + 1) = m by omega]
  have hQ3 : ∏ i ∈ range (j + 1 + 1), (X ^ (j + 1 + m + 1 - i) - 1) =
      (X ^ (j + m + 2) - 1) * (Q * (X ^ (m + 1) - 1)) := by
    rw [prod_range_succ', ← hQ1, mul_comm, Nat.sub_zero, show j + 1 + m + 1 = j + m + 2 by omega]
    exact congrArg _ (prod_congr rfl fun i _ => by rw [show j + m + 2 - (i + 1) = j + 1 + m - i by
      omega])
  have hA (h : ℕ) : X ^ (2 * (h + 1)) - 1 ≠ 0 := sub_ne_zero.mpr (one_lt_pow₀ hX (by omega)).ne'
  rw [hQ1, hQ2, hQ3]
  -- Peel the last factor off the first product, according to the parity of `j`.
  obtain ⟨h, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [show (2 * h + 1 + 1) / 2 = h + 1 by omega, show (2 * h + 1) / 2 = h by omega,
      show 2 * h / 2 = h by omega, prod_range_succ _ h]
    field_simp [hA h]
    ring
  · rw [show (2 * h + 1 + 1 + 1) / 2 = h + 1 by omega,
      show (2 * h + 1 + 1) / 2 = h + 1 by omega,
      show (2 * h + 1) / 2 = h by omega, prod_range_succ _ h]
    field_simp [hA h]
    ring

/-- MacWilliams's product satisfies the symmetric rank count recurrence. -/
private theorem symmRankProd_succ_eq_sum {q : ℕ} (hq : 2 ≤ q) (n k : ℕ) :
    symmRankProd q (n + 1) k = ∑ r ∈ range (n + 1), symmRankProd q n r *
      ((if k = r then q ^ r else if k = r + 1 then (q - 1) * q ^ r
        else if k = r + 2 then q ^ (n + 1) - q ^ (r + 1) else 0 : ℕ) : ℚ) := by
  rw [sum_mul_borderCoeff q n k _ fun t => symmRankProd_of_lt]
  rcases k with _ | _ | j
  · simp [symmRankProd]
  · simp only [symmRankProd]
    push_cast [Nat.one_le_of_lt hq]
    simp
    ring
  simp only [show j + 1 + 1 - 1 = j + 1 by omega, show j + 1 + 1 - 2 = j by omega,
    le_add_iff_nonneg_left, zero_le, ↓reduceIte]
  rcases le_or_gt n j with hnj | hjn
  · -- Every term vanishes, through a factor `q ^ 0 - 1` or, at `j = n`, through the
    -- coefficient `q ^ (n + 1) - q ^ (j + 1)`.
    rw [symmRankProd_of_lt (by omega), symmRankProd_of_lt (by omega),
      symmRankProd_of_lt (t := j + 1) (by omega)]
    rcases hnj.eq_or_lt with rfl | hnj
    · simp
    · simp [symmRankProd_of_lt hnj]
  obtain ⟨m, rfl⟩ : ∃ m, n = j + 1 + m := ⟨n - (j + 1), by omega⟩
  have hc : ((q ^ (j + 1 + m + 1) - q ^ (j + 1) : ℕ) : ℚ) =
      (q : ℚ) ^ (j + m + 2) - (q : ℚ) ^ (j + 1) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) (by omega)), Nat.cast_pow, Nat.cast_pow,
      show j + 1 + m + 1 = j + m + 2 by omega]
  rw [hc, Nat.cast_mul, Nat.cast_sub (Nat.one_le_of_lt hq), Nat.cast_pow, Nat.cast_one]
  exact symmRankProd_add_two hq j m

/-- **The symmetric rank product recurrence.** For every integer `q ≥ 2`, MacWilliams's product
`P(s, t) = ∏_{i=1}^{⌊t/2⌋} q^(2i) / (q^(2i) - 1) · ∏_{i=0}^{t-1} (q^(s-i) - 1)` satisfies
`P(n + 1, k) = ∑_{r ≤ n} P(n, r) c(n, r, k)` with the coefficients `c(n, r, k)` of
`Matrix.natCard_isSymm_rank_succ`. It need not be a prime power. -/
theorem symmetricRankProduct_succ_eq_sum {q : ℕ} (hq : 2 ≤ q) (n k : ℕ) :
    let P : ℕ → ℕ → ℚ := fun s t =>
      (∏ i ∈ range (t / 2), (q : ℚ) ^ (2 * (i + 1)) / ((q : ℚ) ^ (2 * (i + 1)) - 1)) *
        ∏ i ∈ range t, ((q : ℚ) ^ (s - i) - 1)
    P (n + 1) k = ∑ r ∈ range (n + 1), P n r * ((if k = r then q ^ r
      else if k = r + 1 then (q - 1) * q ^ r
      else if k = r + 2 then q ^ (n + 1) - q ^ (r + 1) else 0 : ℕ) : ℚ) :=
  symmRankProd_succ_eq_sum hq n k

end Product

/-- **MacWilliams's formula.** Over a finite field with `q` elements, the number of symmetric
`s × s` matrices of rank `k` is
`∏_{i=1}^{⌊k/2⌋} q^(2i) / (q^(2i) - 1) · ∏_{i=0}^{k-1} (q^(s-i) - 1)`.
For `k > s` both sides vanish. -/
theorem natCard_isSymm_rank_eq_prod (F : Type*) [Field F] [Finite F] (s k : ℕ) :
    (Nat.card {M : Matrix (Fin s) (Fin s) F // M.IsSymm ∧ M.rank = k} : ℚ) =
      (∏ i ∈ range (k / 2), (Nat.card F : ℚ) ^ (2 * (i + 1)) /
        ((Nat.card F : ℚ) ^ (2 * (i + 1)) - 1)) *
        ∏ i ∈ range k, ((Nat.card F : ℚ) ^ (s - i) - 1) := by
  induction s generalizing k with
  | zero =>
    -- The empty matrix is the only `0 × 0` matrix; it is symmetric of rank zero.
    have hrank (M : Matrix (Fin 0) (Fin 0) F) : M.rank = 0 := Nat.le_zero.mp M.rank_le_width
    rcases k with _ | k
    · rw [Nat.card_eq_one_iff_exists.mpr ⟨⟨0, isSymm_zero, hrank 0⟩,
        fun M => Subtype.ext (Subsingleton.elim _ _)⟩]
      simp
    · rw [prod_eq_zero (mem_range.mpr k.succ_pos) (by simp), mul_zero, Nat.cast_eq_zero,
        Nat.card_eq_zero]
      exact Or.inl ⟨fun ⟨M, _, hM⟩ => by simp [hrank] at hM⟩
  | succ s ih =>
    rw [natCard_isSymm_rank_succ, Nat.cast_sum]
    simp_rw [Nat.cast_mul, ih]
    exact (symmetricRankProduct_succ_eq_sum Finite.one_lt_card s k).symm

end Matrix
