/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Count
import Mathlib.Basic.Finite.Sigma
import Mathlib.Tactic.FinCases

/-!
# Symplectic Gelfand-Tsetlin patterns

The restriction `Sp₂ᵣ ↓ Sp₂₍ᵣ₋₁₎` is **not** multiplicity-free, so the symplectic analogue of a
Gelfand-Tsetlin pattern carries more than a chain of interlacing rows.  Following Zhelobenko, a
**symplectic pattern** of rank `r` has, for each `k = r, r - 1, …, 1`, an *unprimed* row
`a⁽ᵏ⁾ = (a₀,ₖ, …, aₖ₋₁,ₖ)` and an *intermediate* row `b⁽ᵏ⁾ = (b₀,ₖ, …, bₖ₋₁,ₖ)`, both of length `k`,
arranged as

```text
        a⁽ʳ⁾
        b⁽ʳ⁾
      a⁽ʳ⁻¹⁾
      b⁽ʳ⁻¹⁾
         ⋮
        a⁽¹⁾
        b⁽¹⁾
```

subject to the betweenness inequalities

* `aᵢ,ₖ ≥ bᵢ,ₖ ≥ aᵢ₊₁,ₖ` for `i < k - 1` and `aₖ₋₁,ₖ ≥ bₖ₋₁,ₖ ≥ 0`, that is, `b⁽ᵏ⁾` interlaces the
  row `a⁽ᵏ⁾` padded by a final zero;
* `bᵢ,ₖ ≥ aᵢ,ₖ₋₁ ≥ bᵢ₊₁,ₖ` for `i < k - 1`, that is, `a⁽ᵏ⁻¹⁾` interlaces `b⁽ᵏ⁾`.

The top row `a⁽ʳ⁾` is the highest weight `λ`, and the unprimed row `a⁽ʳ⁻¹⁾` is the highest weight
of a constituent of the restriction of `V_λ` to `Sp₂₍ᵣ₋₁₎`.  The intermediate row `b⁽ʳ⁾` is genuine
multiplicity data: by Zhelobenko's branching rule the multiplicity of `V_μ` in the restriction of
`V_λ` is the number of rows `b` with `(λ, 0) ≻ b ≻ μ`, and forgetting the intermediate rows loses
vectors already in the standard module of `Sp₄`.  Iterating the rule, the patterns with top row
`λ` index a basis of the irreducible representation `V_λ`, so their count is its dimension; this
file develops the combinatorics only, not the representations.

As for `TauCeti.GTPattern`, both arrays are carried by unrestricted functions `ℕ → ℕ → ℤ` that
vanish off the triangle `i < k ≤ r`, so two patterns agreeing on the informative cells are equal.
No sign condition is imposed: every entry is nonnegative and every row weakly decreasing as a
consequence of the inequalities (`TauCeti.SymplecticGTPattern.entry_nonneg`,
`TauCeti.SymplecticGTPattern.entry_antitone`), so only nonnegative dominant top rows occur
(`TauCeti.SymplecticGTPattern.nonempty_topRow_eq_iff`).

The engine is `TauCeti.SymplecticGTPattern.truncateEquiv`: deleting the two top rows identifies the
patterns of rank `r + 1` over `λ` with a choice of intermediate row `b` interlacing `(λ, 0)`
together with a pattern of rank `r` whose top row interlaces `b`.  It gives the branching recursion
for the count (`TauCeti.SymplecticGTPattern.card_topRow_succ`), the count `λ₀ + 1` in rank one,
and the worked `Sp₄` counts of the standard, the second fundamental and the adjoint module.

## Main definitions

* `TauCeti.SymplecticGTPattern r`: symplectic Gelfand-Tsetlin patterns of rank `r`.
* `TauCeti.SymplecticGTPattern.topRow` and `TauCeti.SymplecticGTPattern.topMidRow`: the top
  unprimed row (the highest weight) and the intermediate row below it.
* `TauCeti.SymplecticGTPattern.truncate` and `TauCeti.SymplecticGTPattern.extend`: deleting and
  prepending the two top rows.

## Main results

* `TauCeti.SymplecticGTPattern.entry_nonneg` and `TauCeti.SymplecticGTPattern.entry_antitone`:
  entries are nonnegative and rows weakly decreasing.
* `TauCeti.SymplecticGTPattern.truncateEquiv`: the patterns over `λ`, split by their top
  intermediate row.
* `TauCeti.SymplecticGTPattern.truncateFiberEquiv`: the patterns over `λ` whose second unprimed row
  is `μ` are the intermediate rows between `(λ, 0)` and `μ` times the patterns over `μ`.
* `TauCeti.SymplecticGTPattern.card_topRow_succ`: the branching recursion for the count.
* `TauCeti.SymplecticGTPattern.nonempty_topRow_eq_iff`: a sequence is a top row exactly when it is
  weakly decreasing and nonnegative.
* `TauCeti.SymplecticGTPattern.card_topRow_zero` and `TauCeti.SymplecticGTPattern.card_topRow_one`:
  the counts in rank zero and one.
* `TauCeti.SymplecticGTPattern.card_topRow_two`: the rank-two count as an explicit sum, with the
  worked examples `(1, 0)`, `(1, 1)` and `(2, 0)` giving `4`, `5` and `10`.

## References

* D. P. Zhelobenko, *Classical groups. Spectral analysis of finite-dimensional representations*,
  Uspekhi Mat. Nauk **17** (1962), 27-120.
* A. I. Molev, *Gelfand-Tsetlin bases for classical Lie algebras*, in *Handbook of Algebra*
  Vol. 4 (2006), §3 (arXiv:math/0211289).
-/

public section

namespace TauCeti

/-- A **symplectic Gelfand-Tsetlin pattern** of rank `r`: for each `k ≤ r` an unprimed row
`entry · k` and an intermediate row `midEntry · k`, both of length `k`, such that the intermediate
row `k` interlaces the unprimed row `k` padded by a final zero and the unprimed row `k - 1`
interlaces the intermediate row `k`.

As for `TauCeti.GTPattern`, the arrays are unrestricted functions `ℕ → ℕ → ℤ` required to vanish
off the triangle `i < k ≤ r`.  With these zeros, the condition at the last cell of row `k`,
`midEntry (k - 1) k ≥ entry k k = 0`, is the nonnegativity of the padded interlacing. -/
structure SymplecticGTPattern (r : ℕ) where
  /-- `entry i k` is the `i`-th entry of the unprimed row `k`; the informative cells are
  `i < k ≤ r`. -/
  entry : ℕ → ℕ → ℤ
  /-- `midEntry i k` is the `i`-th entry of the intermediate row `k`, lying between the unprimed
  rows `k` and `k - 1`; the informative cells are `i < k ≤ r`. -/
  midEntry : ℕ → ℕ → ℤ
  /-- Cells of an unprimed row outside the triangle `i < k ≤ r` carry no data. -/
  zeros' : ∀ {i k : ℕ}, r < k ∨ k ≤ i → entry i k = 0
  /-- Cells of an intermediate row outside the triangle `i < k ≤ r` carry no data. -/
  midZeros' : ∀ {i k : ℕ}, r < k ∨ k ≤ i → midEntry i k = 0
  /-- The intermediate row `k` interlaces the unprimed row `k` padded by a zero:
  `aᵢ,ₖ ≥ bᵢ,ₖ ≥ aᵢ₊₁,ₖ`, with `aₖ,ₖ = 0`. -/
  midInterlacing' : ∀ {i k : ℕ}, i < k → k ≤ r →
    midEntry i k ≤ entry i k ∧ entry (i + 1) k ≤ midEntry i k
  /-- The unprimed row `k` interlaces the intermediate row `k + 1`:
  `bᵢ,ₖ₊₁ ≥ aᵢ,ₖ ≥ bᵢ₊₁,ₖ₊₁`. -/
  interlacing' : ∀ {i k : ℕ}, i < k → k < r →
    entry i k ≤ midEntry i (k + 1) ∧ midEntry (i + 1) (k + 1) ≤ entry i k

namespace SymplecticGTPattern

variable {r : ℕ}

@[ext]
theorem ext {P P' : SymplecticGTPattern r} (h : ∀ i k, P.entry i k = P'.entry i k)
    (h' : ∀ i k, P.midEntry i k = P'.midEntry i k) : P = P' := by
  obtain ⟨a, b, _, _, _, _⟩ := P
  obtain ⟨a', b', _, _, _, _⟩ := P'
  obtain rfl : a = a' := funext fun i => funext (h i)
  obtain rfl : b = b' := funext fun i => funext (h' i)
  rfl

theorem entry_eq_zero (P : SymplecticGTPattern r) {i k : ℕ} (h : r < k ∨ k ≤ i) :
    P.entry i k = 0 :=
  P.zeros' h

theorem midEntry_eq_zero (P : SymplecticGTPattern r) {i k : ℕ} (h : r < k ∨ k ≤ i) :
    P.midEntry i k = 0 :=
  P.midZeros' h

/-- An unprimed row past the top row is empty. -/
@[simp]
theorem entry_eq_zero_of_lt (P : SymplecticGTPattern r) {i k : ℕ} (h : r < k) :
    P.entry i k = 0 :=
  P.entry_eq_zero (Or.inl h)

/-- An unprimed row `k` has no cell past its length `k`. -/
@[simp]
theorem entry_eq_zero_of_le (P : SymplecticGTPattern r) {i k : ℕ} (h : k ≤ i) :
    P.entry i k = 0 :=
  P.entry_eq_zero (Or.inr h)

/-- An intermediate row past the top row is empty. -/
@[simp]
theorem midEntry_eq_zero_of_lt (P : SymplecticGTPattern r) {i k : ℕ} (h : r < k) :
    P.midEntry i k = 0 :=
  P.midEntry_eq_zero (Or.inl h)

/-- An intermediate row `k` has no cell past its length `k`. -/
@[simp]
theorem midEntry_eq_zero_of_le (P : SymplecticGTPattern r) {i k : ℕ} (h : k ≤ i) :
    P.midEntry i k = 0 :=
  P.midEntry_eq_zero (Or.inr h)

/-! ### Rows are nonnegative and weakly decreasing -/

/-- The first padded interlacing inequality `bᵢ,ₖ ≤ aᵢ,ₖ`.  It holds at every cell: off the
triangle both sides vanish. -/
theorem midEntry_le_entry (P : SymplecticGTPattern r) (i k : ℕ) : P.midEntry i k ≤ P.entry i k := by
  by_cases h : i < k ∧ k ≤ r
  · exact (P.midInterlacing' h.1 h.2).1
  · rw [P.midEntry_eq_zero (by omega), P.entry_eq_zero (by omega)]

/-- The second padded interlacing inequality `aᵢ₊₁,ₖ ≤ bᵢ,ₖ`.  At the last cell of the row it is
`0 ≤ bₖ₋₁,ₖ`; off the triangle both sides vanish. -/
theorem entry_succ_le_midEntry (P : SymplecticGTPattern r) (i k : ℕ) :
    P.entry (i + 1) k ≤ P.midEntry i k := by
  by_cases h : i < k ∧ k ≤ r
  · exact (P.midInterlacing' h.1 h.2).2
  · rw [P.midEntry_eq_zero (by omega), P.entry_eq_zero (by omega)]

/-- Unprimed rows decrease weakly, in adjacent form. -/
theorem entry_succ_le_entry (P : SymplecticGTPattern r) (i k : ℕ) :
    P.entry (i + 1) k ≤ P.entry i k :=
  (P.entry_succ_le_midEntry i k).trans (P.midEntry_le_entry i k)

/-- Intermediate rows decrease weakly, in adjacent form. -/
theorem midEntry_succ_le_midEntry (P : SymplecticGTPattern r) (i k : ℕ) :
    P.midEntry (i + 1) k ≤ P.midEntry i k :=
  (P.midEntry_le_entry (i + 1) k).trans (P.entry_succ_le_midEntry i k)

/-- **Unprimed rows decrease weakly.**  This is a consequence of the padded interlacing of each
intermediate row, not a separate hypothesis on a pattern. -/
theorem entry_antitone (P : SymplecticGTPattern r) (k : ℕ) : Antitone fun i => P.entry i k :=
  antitone_nat_of_succ_le fun i => P.entry_succ_le_entry i k

/-- **Intermediate rows decrease weakly.** -/
theorem midEntry_antitone (P : SymplecticGTPattern r) (k : ℕ) :
    Antitone fun i => P.midEntry i k :=
  antitone_nat_of_succ_le fun i => P.midEntry_succ_le_midEntry i k

/-- **Every entry of an unprimed row is nonnegative.**  Rows decrease weakly down to the empty
cell `aₖ,ₖ = 0`, so no sign condition has to be imposed on a pattern. -/
theorem entry_nonneg (P : SymplecticGTPattern r) (i k : ℕ) : 0 ≤ P.entry i k := by
  rcases le_or_gt i k with h | h
  · simpa using P.entry_antitone k h
  · rw [P.entry_eq_zero_of_le h.le]

/-- **Every entry of an intermediate row is nonnegative.** -/
theorem midEntry_nonneg (P : SymplecticGTPattern r) (i k : ℕ) : 0 ≤ P.midEntry i k :=
  (P.entry_nonneg (i + 1) k).trans (P.entry_succ_le_midEntry i k)

/-- The first interlacing inequality between rows, `aᵢ,ₖ ≤ bᵢ,ₖ₊₁`, below the top row. -/
theorem entry_le_midEntry_succ (P : SymplecticGTPattern r) {i k : ℕ} (hk : k < r) :
    P.entry i k ≤ P.midEntry i (k + 1) := by
  rcases lt_or_ge i k with h | h
  · exact (P.interlacing' h hk).1
  · rw [P.entry_eq_zero_of_le h]
    exact P.midEntry_nonneg _ _

/-- The second interlacing inequality between rows, `bᵢ₊₁,ₖ₊₁ ≤ aᵢ,ₖ`, below the top row. -/
theorem midEntry_succ_succ_le_entry (P : SymplecticGTPattern r) {i k : ℕ} (hk : k < r) :
    P.midEntry (i + 1) (k + 1) ≤ P.entry i k := by
  rcases lt_or_ge i k with h | h
  · exact (P.interlacing' h hk).2
  · rw [P.midEntry_eq_zero_of_le (by omega), P.entry_eq_zero_of_le h]

/-! ### The top rows -/

/-- The **top row** `(a₀,ᵣ, …, aᵣ₋₁,ᵣ)` of a symplectic pattern: the highest weight it refines. -/
def topRow (P : SymplecticGTPattern r) : Fin r → ℤ := fun i => P.entry i r

@[simp]
theorem topRow_apply (P : SymplecticGTPattern r) (i : Fin r) : P.topRow i = P.entry i r := (rfl)

/-- The **top intermediate row** `(b₀,ᵣ, …, bᵣ₋₁,ᵣ)`, between the top row and the second unprimed
row: the multiplicity datum of the branching `Sp₂ᵣ ↓ Sp₂₍ᵣ₋₁₎`. -/
def topMidRow (P : SymplecticGTPattern r) : Fin r → ℤ := fun i => P.midEntry i r

@[simp]
theorem topMidRow_apply (P : SymplecticGTPattern r) (i : Fin r) :
    P.topMidRow i = P.midEntry i r :=
  (rfl)

/-- The top row decreases weakly. -/
theorem topRow_antitone (P : SymplecticGTPattern r) : Antitone P.topRow :=
  fun _ _ h => P.entry_antitone r h

/-- The top row is nonnegative. -/
theorem topRow_nonneg (P : SymplecticGTPattern r) (i : Fin r) : 0 ≤ P.topRow i :=
  P.entry_nonneg i r

/-- The top row padded by a final zero is read off the top row of the array, whose cell `aᵣ,ᵣ` is
empty. -/
theorem snoc_topRow_apply (P : SymplecticGTPattern r) (i : Fin (r + 1)) :
    Fin.snoc (α := fun _ => ℤ) P.topRow 0 i = P.entry i r := by
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

/-- The top intermediate row interlaces the top row padded by a final zero. -/
theorem interlaces_snoc_topRow_topMidRow (P : SymplecticGTPattern r) :
    Interlaces (Fin.snoc P.topRow 0) P.topMidRow :=
  interlaces_iff.mpr fun i => by
    rw [snoc_topRow_apply, snoc_topRow_apply]
    exact ⟨P.midEntry_le_entry i r, P.entry_succ_le_midEntry i r⟩

/-! ### Deleting and prepending the two top rows -/

/-- Delete the top unprimed row and the top intermediate row of a pattern of rank `r + 1`. -/
def truncate (P : SymplecticGTPattern (r + 1)) : SymplecticGTPattern r where
  entry i k := if k ≤ r then P.entry i k else 0
  midEntry i k := if k ≤ r then P.midEntry i k else 0
  zeros' := by
    intro i k h
    split_ifs with hk
    · exact P.entry_eq_zero (by omega)
    · rfl
  midZeros' := by
    intro i k h
    split_ifs with hk
    · exact P.midEntry_eq_zero (by omega)
    · rfl
  midInterlacing' := by
    intro i k hik hk
    simp only [hk, ↓reduceIte]
    exact P.midInterlacing' hik (by omega)
  interlacing' := by
    intro i k hik hk
    have hk' : k + 1 ≤ r := hk
    simp only [hk.le, hk', ↓reduceIte]
    exact P.interlacing' hik (by omega)

@[simp]
theorem truncate_entry (P : SymplecticGTPattern (r + 1)) (i k : ℕ) :
    P.truncate.entry i k = if k ≤ r then P.entry i k else 0 :=
  (rfl)

@[simp]
theorem truncate_midEntry (P : SymplecticGTPattern (r + 1)) (i k : ℕ) :
    P.truncate.midEntry i k = if k ≤ r then P.midEntry i k else 0 :=
  (rfl)

/-- The top row of a truncated pattern is the second unprimed row of the original. -/
theorem topRow_truncate (P : SymplecticGTPattern (r + 1)) (i : Fin r) :
    P.truncate.topRow i = P.entry i r := by
  simp

/-- The second unprimed row interlaces the top intermediate row. -/
theorem interlaces_topMidRow_topRow_truncate (P : SymplecticGTPattern (r + 1)) :
    Interlaces P.topMidRow P.truncate.topRow :=
  interlaces_iff.mpr fun i => by
    rw [topRow_truncate]
    exact ⟨P.entry_le_midEntry_succ (by omega), P.midEntry_succ_succ_le_entry (by omega)⟩

/-- The top row padded by a zero, read at an explicit index. -/
private theorem snoc_apply_mk (l : Fin (r + 1) → ℤ) (i : ℕ) (hi : i < r + 2) :
    Fin.snoc (α := fun _ => ℤ) l 0 ⟨i, hi⟩ = if h : i < r + 1 then l ⟨i, h⟩ else 0 := by
  simp [Fin.snoc]

/-- Prepend the top row `l` and the intermediate row `b` on top of a pattern of rank `r`, provided
`b` interlaces `l` padded by a zero and the top row of the pattern interlaces `b`. -/
def extend (Q : SymplecticGTPattern r) (l b : Fin (r + 1) → ℤ)
    (hb : Interlaces (Fin.snoc l 0) b) (hQ : Interlaces b Q.topRow) :
    SymplecticGTPattern (r + 1) where
  entry i k := if k = r + 1 then (if hi : i < r + 1 then l ⟨i, hi⟩ else 0) else Q.entry i k
  midEntry i k := if k = r + 1 then (if hi : i < r + 1 then b ⟨i, hi⟩ else 0) else Q.midEntry i k
  zeros' := by
    intro i k h
    split_ifs with hk hi
    · omega
    · rfl
    · exact Q.entry_eq_zero (by omega)
  midZeros' := by
    intro i k h
    split_ifs with hk hi
    · omega
    · rfl
    · exact Q.midEntry_eq_zero (by omega)
  midInterlacing' := by
    intro i k hik hk
    by_cases hkr : k = r + 1
    · subst hkr
      have h₁ := hb.le_castSucc ⟨i, hik⟩
      have h₂ := hb.succ_le ⟨i, hik⟩
      rw [Fin.snoc_castSucc] at h₁
      rw [Fin.succ_mk, snoc_apply_mk] at h₂
      simp only [↓reduceIte, dite_eq_left hik]
      exact ⟨h₁, h₂⟩
    · simp only [hkr, ↓reduceIte]
      exact Q.midInterlacing' hik (by omega)
  interlacing' := by
    intro i k hik hk
    by_cases hkr : k = r
    · subst k
      have h₁ := hQ.le_castSucc ⟨i, hik⟩
      have h₂ := hQ.succ_le ⟨i, hik⟩
      simp only [topRow_apply, Fin.castSucc_mk, Fin.succ_mk] at h₁ h₂
      have hr : r ≠ r + 1 := by omega
      simp only [hr, ↓reduceIte, dite_eq_left (by omega : i < r + 1),
        dite_eq_left (by omega : i + 1 < r + 1)]
      exact ⟨h₁, h₂⟩
    · have h₁ : k ≠ r + 1 := by omega
      have h₂ : k + 1 ≠ r + 1 := by omega
      simp only [h₁, h₂, ↓reduceIte]
      exact Q.interlacing' hik (by omega)

section Extend

variable (Q : SymplecticGTPattern r) (l b : Fin (r + 1) → ℤ) (hb : Interlaces (Fin.snoc l 0) b)
  (hQ : Interlaces b Q.topRow)

@[simp]
theorem extend_entry_of_ne {i k : ℕ} (hk : k ≠ r + 1) :
    (Q.extend l b hb hQ).entry i k = Q.entry i k :=
  ite_eq_right hk

@[simp]
theorem extend_midEntry_of_ne {i k : ℕ} (hk : k ≠ r + 1) :
    (Q.extend l b hb hQ).midEntry i k = Q.midEntry i k :=
  ite_eq_right hk

@[simp]
theorem extend_entry_top {i : ℕ} (hi : i < r + 1) :
    (Q.extend l b hb hQ).entry i (r + 1) = l ⟨i, hi⟩ := by
  simp only [extend, ↓reduceIte, dite_eq_left hi]

@[simp]
theorem extend_midEntry_top {i : ℕ} (hi : i < r + 1) :
    (Q.extend l b hb hQ).midEntry i (r + 1) = b ⟨i, hi⟩ := by
  simp only [extend, ↓reduceIte, dite_eq_left hi]

@[simp]
theorem topRow_extend : (Q.extend l b hb hQ).topRow = l :=
  funext fun i => extend_entry_top Q l b hb hQ i.2

@[simp]
theorem topMidRow_extend : (Q.extend l b hb hQ).topMidRow = b :=
  funext fun i => extend_midEntry_top Q l b hb hQ i.2

@[simp]
theorem truncate_extend : (Q.extend l b hb hQ).truncate = Q := by
  ext i k
  · rw [truncate_entry]
    split_ifs with hk
    · exact extend_entry_of_ne Q l b hb hQ (by omega)
    · exact (Q.entry_eq_zero_of_lt (by omega)).symm
  · rw [truncate_midEntry]
    split_ifs with hk
    · exact extend_midEntry_of_ne Q l b hb hQ (by omega)
    · exact (Q.midEntry_eq_zero_of_lt (by omega)).symm

@[simp]
theorem extend_truncate (P : SymplecticGTPattern (r + 1)) :
    P.truncate.extend P.topRow P.topMidRow P.interlaces_snoc_topRow_topMidRow
      P.interlaces_topMidRow_topRow_truncate = P := by
  ext i k
  · by_cases hk : k = r + 1
    · subst hk
      by_cases hi : i < r + 1
      · rw [extend_entry_top _ _ _ _ _ hi, topRow_apply]
      · rw [P.entry_eq_zero_of_le (by omega)]
        simp only [extend, ↓reduceIte, dite_eq_right hi]
    · rw [extend_entry_of_ne _ _ _ _ _ hk, truncate_entry]
      split_ifs with hkr
      · rfl
      · exact (P.entry_eq_zero_of_lt (by omega)).symm
  · by_cases hk : k = r + 1
    · subst hk
      by_cases hi : i < r + 1
      · rw [extend_midEntry_top _ _ _ _ _ hi, topMidRow_apply]
      · rw [P.midEntry_eq_zero_of_le (by omega)]
        simp only [extend, ↓reduceIte, dite_eq_right hi]
    · rw [extend_midEntry_of_ne _ _ _ _ _ hk, truncate_midEntry]
      split_ifs with hkr
      · rfl
      · exact (P.midEntry_eq_zero_of_lt (by omega)).symm

end Extend

/-! ### The patterns over a top row, split by the intermediate row -/

/-- **Deleting the two top rows is a bijection.**  The symplectic patterns of rank `r + 1` and top
row `l` are exactly the choices of an intermediate row `b` interlacing `l` padded by a zero,
together with a pattern of rank `r` whose top row interlaces `b`.

For a nonnegative dominant `l` this is the combinatorial form of the branching
`Sp₂₍ᵣ₊₁₎ ↓ Sp₂ᵣ`: the constituents of the restriction of `V_l` are indexed by the possible second
unprimed rows, each appearing once for every intermediate row `b` between them and `l`. -/
def truncateEquiv (l : Fin (r + 1) → ℤ) :
    {P : SymplecticGTPattern (r + 1) // P.topRow = l} ≃
      Σ b : interlacingFinset (Fin.snoc l 0),
        {Q : SymplecticGTPattern r // Interlaces (b : Fin (r + 1) → ℤ) Q.topRow} where
  toFun P := ⟨⟨P.1.topMidRow, mem_interlacingFinset.mpr (by
      have h := P.1.interlaces_snoc_topRow_topMidRow
      rwa [P.2] at h)⟩,
    ⟨P.1.truncate, P.1.interlaces_topMidRow_topRow_truncate⟩⟩
  invFun x := ⟨x.2.1.extend l x.1 (mem_interlacingFinset.mp x.1.2) x.2.2, by simp⟩
  left_inv := by
    rintro ⟨P, rfl⟩
    exact Subtype.ext (extend_truncate P)
  right_inv x := Sigma.subtype_ext (Subtype.ext (by simp)) (by simp)

@[simp]
theorem truncateEquiv_apply_fst_coe (l : Fin (r + 1) → ℤ)
    (P : {P : SymplecticGTPattern (r + 1) // P.topRow = l}) :
    ((truncateEquiv l P).1 : Fin (r + 1) → ℤ) = P.1.topMidRow :=
  (rfl)

@[simp]
theorem truncateEquiv_apply_snd_coe (l : Fin (r + 1) → ℤ)
    (P : {P : SymplecticGTPattern (r + 1) // P.topRow = l}) :
    (truncateEquiv l P).2.1 = P.1.truncate :=
  (rfl)

@[simp]
theorem truncateEquiv_symm_apply_coe (l : Fin (r + 1) → ℤ)
    (x : Σ b : interlacingFinset (Fin.snoc l 0),
      {Q : SymplecticGTPattern r // Interlaces (b : Fin (r + 1) → ℤ) Q.topRow}) :
    ((truncateEquiv l).symm x).1 = x.2.1.extend l x.1 (mem_interlacingFinset.mp x.1.2) x.2.2 :=
  (rfl)

/-- The patterns whose top row interlaces `b`, sorted by that top row. -/
private def interlacesTopRowEquiv (b : Fin (r + 1) → ℤ) :
    {Q : SymplecticGTPattern r // Interlaces b Q.topRow} ≃
      Σ m : interlacingFinset b, {Q : SymplecticGTPattern r // Q.topRow = (m : Fin r → ℤ)} where
  toFun Q := ⟨⟨Q.1.topRow, mem_interlacingFinset.mpr Q.2⟩, ⟨Q.1, rfl⟩⟩
  invFun x := ⟨x.2.1, by rw [x.2.2]; exact mem_interlacingFinset.mp x.1.2⟩
  left_inv _ := rfl
  right_inv x := Sigma.subtype_ext (Subtype.ext x.2.2) rfl

/-- **The patterns over `l`, sorted by their top intermediate row and their second unprimed row.**
This is `TauCeti.SymplecticGTPattern.truncateEquiv` with the pattern of rank `r` further indexed
by its own top row. -/
def truncateSigmaEquiv (l : Fin (r + 1) → ℤ) :
    {P : SymplecticGTPattern (r + 1) // P.topRow = l} ≃
      Σ b : interlacingFinset (Fin.snoc l 0), Σ m : interlacingFinset (b : Fin (r + 1) → ℤ),
        {Q : SymplecticGTPattern r // Q.topRow = (m : Fin r → ℤ)} :=
  (truncateEquiv l).trans
    (Equiv.sigmaCongrRight fun b => interlacesTopRowEquiv (b : Fin (r + 1) → ℤ))

/-- **The multiplicity data of the branching.**  The patterns of rank `r + 1` with top row `l` and
second unprimed row `m` are the intermediate rows `b` with `(l, 0) ≻ b ≻ m`, times the patterns of
rank `r` with top row `m`.  For nonnegative dominant `l` and `m`, Zhelobenko's branching rule reads
the first factor as the multiplicity of `V_m` in the restriction of `V_l` along
`Sp₂ᵣ ⊂ Sp₂₍ᵣ₊₁₎`. -/
def truncateFiberEquiv (l : Fin (r + 1) → ℤ) (m : Fin r → ℤ) :
    {P : SymplecticGTPattern (r + 1) // P.topRow = l ∧ P.truncate.topRow = m} ≃
      {b : Fin (r + 1) → ℤ // Interlaces (Fin.snoc l 0) b ∧ Interlaces b m} ×
        {Q : SymplecticGTPattern r // Q.topRow = m} where
  toFun P := (⟨P.1.topMidRow,
      by have h := P.1.interlaces_snoc_topRow_topMidRow; rwa [P.2.1] at h,
      by have h := P.1.interlaces_topMidRow_topRow_truncate; rwa [P.2.2] at h⟩,
    ⟨P.1.truncate, P.2.2⟩)
  invFun x := ⟨x.2.1.extend l x.1.1 x.1.2.1 (by rw [x.2.2]; exact x.1.2.2),
    by simp, by simpa using x.2.2⟩
  left_inv := by
    rintro ⟨P, rfl, rfl⟩
    exact Subtype.ext (extend_truncate P)
  right_inv x := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))

/-! ### Finitely many patterns share a top row -/

/-- In rank zero there is exactly one pattern, the empty one. -/
instance : Unique (SymplecticGTPattern 0) where
  default :=
    { entry := fun _ _ => 0
      midEntry := fun _ _ => 0
      zeros' := fun _ => rfl
      midZeros' := fun _ => rfl
      midInterlacing' := fun _ hk => by omega
      interlacing' := fun _ hk => by omega }
  uniq P := by
    ext i k
    · exact P.entry_eq_zero (by omega)
    · exact P.midEntry_eq_zero (by omega)

/-- **Only finitely many patterns share a top row**, by induction on the rank through
`TauCeti.SymplecticGTPattern.truncateSigmaEquiv`. -/
instance finite_topRow_eq (l : Fin r → ℤ) : Finite {P : SymplecticGTPattern r // P.topRow = l} := by
  induction r with
  | zero => infer_instance
  | succ r ih => exact Finite.of_equiv _ (truncateSigmaEquiv l).symm

/-! ### Counting the patterns over a top row -/

/-- **The branching recursion for the count.**  The symplectic patterns of rank `r + 1` and top row
`l` are counted by the patterns of rank `r`, summed over the intermediate rows `b` interlacing `l`
padded by a zero and the rows `m` interlacing `b`.

For a nonnegative dominant `l` this is the combinatorial shadow of the restriction
`Sp₂₍ᵣ₊₁₎ ↓ Sp₂ᵣ`; unlike the `GL` recursion `TauCeti.GTPattern.card_topRow_succ`, a row `m` can
be reached through several intermediate rows `b`, the multiplicity of `V_m` in the restriction. -/
theorem card_topRow_succ (l : Fin (r + 1) → ℤ) :
    Nat.card {P : SymplecticGTPattern (r + 1) // P.topRow = l}
      = ∑ b ∈ interlacingFinset (Fin.snoc l 0), ∑ m ∈ interlacingFinset b,
          Nat.card {Q : SymplecticGTPattern r // Q.topRow = m} := by
  rw [Nat.card_congr (truncateSigmaEquiv l), Nat.card_sigma,
    ← Finset.sum_attach (interlacingFinset (Fin.snoc l 0))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Nat.card_sigma]
  exact Finset.sum_attach (interlacingFinset (b : Fin (r + 1) → ℤ))
    fun m => Nat.card {Q : SymplecticGTPattern r // Q.topRow = m}

/-- **The count in rank zero**: the empty pattern, the trivial representation of `Sp₀`. -/
theorem card_topRow_zero (l : Fin 0 → ℤ) :
    Nat.card {P : SymplecticGTPattern 0 // P.topRow = l} = 1 := by
  have : Unique {P : SymplecticGTPattern 0 // P.topRow = l} :=
    ⟨⟨⟨default, Subsingleton.elim _ _⟩⟩, fun _ => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Nat.card_unique

/-- **The count in rank one.**  A pattern of rank one with top row `(λ₀)` is its single
intermediate entry `λ₀ ≥ b ≥ 0`, so there are `(λ₀ + 1).toNat` of them.  For `λ₀ ≥ 0` this is the
dimension `λ₀ + 1` of the irreducible representation of `Sp₂ = SL₂` of highest weight `λ₀`. -/
theorem card_topRow_one (l : Fin 1 → ℤ) :
    Nat.card {P : SymplecticGTPattern 1 // P.topRow = l} = (l 0 + 1).toNat := by
  simp only [card_topRow_succ, card_topRow_zero, Finset.sum_const, card_interlacingFinset,
    Finset.univ_eq_empty, Finset.prod_empty, smul_eq_mul, mul_one]
  simp [Fin.snoc]

/-- **The count in rank two**, as an explicit sum over the two entries `b₀ ≥ b₁` of the top
intermediate row and the entry `m` of the second unprimed row, each contributing the `m + 1`
patterns of rank one over `m`. -/
theorem card_topRow_two (l : Fin 2 → ℤ) :
    Nat.card {P : SymplecticGTPattern 2 // P.topRow = l}
      = ∑ b₀ ∈ Finset.Icc (l 1) (l 0), ∑ b₁ ∈ Finset.Icc 0 (l 1), ∑ m ∈ Finset.Icc b₁ b₀,
          (m + 1).toNat := by
  rw [card_topRow_succ, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun b => (b 0, b 1)) (fun p => ![p.1, p.2]) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    rw [mem_interlacingFinset] at hb
    have h₀ := interlaces_iff.mp hb 0
    have h₁ := interlaces_iff.mp hb 1
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by simpa [Fin.snoc] using h₀.2, by simpa [Fin.snoc] using h₀.1⟩,
      ⟨by simpa [Fin.snoc] using h₁.2, by simpa [Fin.snoc] using h₁.1⟩⟩
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    rw [mem_interlacingFinset, interlaces_iff]
    intro i
    fin_cases i
    · simpa [Fin.snoc] using And.intro hp.1.2 hp.1.1
    · simpa [Fin.snoc] using And.intro hp.2.2 hp.2.1
  · intro b _
    ext i
    fin_cases i <;> rfl
  · intro p _
    rfl
  · intro b _
    refine Finset.sum_nbij' (fun m => m 0) (fun x => ![x]) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      rw [mem_interlacingFinset] at hm
      exact Finset.mem_Icc.mpr ⟨hm.succ_le 0, hm.le_castSucc 0⟩
    · intro x hx
      rw [Finset.mem_Icc] at hx
      rw [mem_interlacingFinset, interlaces_iff]
      intro i
      fin_cases i
      exact ⟨hx.2, hx.1⟩
    · intro m _
      ext i
      fin_cases i
      rfl
    · intro x _
      rfl
    · intro m _
      exact card_topRow_one m

/-- **The standard representation of `Sp₄`.**  The top row `(1, 0)` carries `4` patterns. -/
theorem card_topRow_one_zero : Nat.card {P : SymplecticGTPattern 2 // P.topRow = ![1, 0]} = 4 := by
  rw [card_topRow_two]
  decide

/-- **The second fundamental representation of `Sp₄`.**  The top row `(1, 1)` carries `5` patterns,
the dimension of the traceless part of `Λ² ℂ⁴`. -/
theorem card_topRow_one_one : Nat.card {P : SymplecticGTPattern 2 // P.topRow = ![1, 1]} = 5 := by
  rw [card_topRow_two]
  decide

/-- **The adjoint representation of `Sp₄`.**  The top row `(2, 0)` carries `10` patterns, the
dimension of `Sym² ℂ⁴ ≅ 𝔰𝔭₄`. -/
theorem card_topRow_two_zero : Nat.card {P : SymplecticGTPattern 2 // P.topRow = ![2, 0]} = 10 := by
  rw [card_topRow_two]
  decide

/-- **The branching multiplicities in rank two.**  The intermediate rows `b = (b₀, b₁)` with
`(λ₀, λ₁, 0) ≻ b ≻ (μ)` are cut out by the independent bounds `max λ₁ μ ≤ b₀ ≤ λ₀` and
`0 ≤ b₁ ≤ min λ₁ μ`.  For nonnegative dominant `λ` and `μ ≥ 0`, Zhelobenko's branching rule reads
this count as the multiplicity of the irreducible representation of highest weight `μ` in the
restriction of `V_λ` from `Sp₄` to `Sp₂`. -/
theorem card_midRows_two (l : Fin 2 → ℤ) (m : Fin 1 → ℤ) :
    Nat.card {b : Fin 2 → ℤ // Interlaces (Fin.snoc l 0) b ∧ Interlaces b m}
      = (l 0 + 1 - max (l 1) (m 0)).toNat * (min (l 1) (m 0) + 1).toNat := by
  let e : {b : Fin 2 → ℤ // Interlaces (Fin.snoc l 0) b ∧ Interlaces b m} ≃
      Finset.Icc (max (l 1) (m 0)) (l 0) ×ˢ Finset.Icc 0 (min (l 1) (m 0)) :=
    { toFun b := ⟨(b.1 0, b.1 1), by
        obtain ⟨h₁, h₂⟩ := b.2
        have h₀ := interlaces_iff.mp h₁ 0
        have h₁ := interlaces_iff.mp h₁ 1
        have h₂ := interlaces_iff.mp h₂ 0
        simp [Fin.snoc] at h₀ h₁ h₂
        simp only [Finset.mem_product, Finset.mem_Icc, max_le_iff, le_min_iff]
        omega⟩
      invFun p := ⟨![p.1.1, p.1.2], by
        have hp := p.2
        simp only [Finset.mem_product, Finset.mem_Icc, max_le_iff, le_min_iff] at hp
        refine ⟨interlaces_iff.mpr fun i => ?_, interlaces_iff.mpr fun i => ?_⟩ <;>
          fin_cases i <;> simp [Fin.snoc] <;> omega⟩
      left_inv b := Subtype.ext (funext fun i => by fin_cases i <;> rfl)
      right_inv p := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_product,
    Int.card_Icc, Int.card_Icc, sub_zero]

/-- **The intermediate row is multiplicity data.**  Of the `4` patterns over the standard
representation `(1, 0)` of `Sp₄`, the `2` whose second unprimed row is the trivial weight `(0)` of
`Sp₂` differ only in their intermediate row, `(1, 0)` or `(0, 0)`: the trivial representation
occurs twice in the restriction.  Forgetting the intermediate rows would lose one of them. -/
theorem card_topRow_one_zero_truncate_zero :
    Nat.card {P : SymplecticGTPattern 2 // P.topRow = ![1, 0] ∧ P.truncate.topRow = ![0]} = 2 := by
  rw [Nat.card_congr (truncateFiberEquiv _ _), Nat.card_prod, card_midRows_two, card_topRow_one]
  decide

/-- The other `2` patterns over `(1, 0)` have second unprimed row `(1)`: a single intermediate row
`(1, 0)`, over the `2` patterns of the standard representation of `Sp₂`.  Together with
`TauCeti.SymplecticGTPattern.card_topRow_one_zero_truncate_zero` this is `4 = 1 + 1 + 2`. -/
theorem card_topRow_one_zero_truncate_one :
    Nat.card {P : SymplecticGTPattern 2 // P.topRow = ![1, 0] ∧ P.truncate.topRow = ![1]} = 2 := by
  rw [Nat.card_congr (truncateFiberEquiv _ _), Nat.card_prod, card_midRows_two, card_topRow_one]
  decide

/-! ### Which sequences are top rows -/

/-- **A sequence is the top row of a pattern exactly when it is weakly decreasing and
nonnegative**, that is, when it is a dominant weight of `Sp₂ᵣ` in the coordinates of the standard
torus.  Conversely to `TauCeti.SymplecticGTPattern.topRow_antitone` and
`TauCeti.SymplecticGTPattern.topRow_nonneg`, such an `l` admits itself as intermediate row and
`l ∘ Fin.castSucc` as second unprimed row, so a pattern over it is built inductively. -/
theorem nonempty_topRow_eq_iff (l : Fin r → ℤ) :
    Nonempty {P : SymplecticGTPattern r // P.topRow = l} ↔ Antitone l ∧ ∀ i, 0 ≤ l i := by
  refine ⟨fun ⟨⟨P, hP⟩⟩ => hP ▸ ⟨P.topRow_antitone, P.topRow_nonneg⟩, ?_⟩
  induction r with
  | zero => exact fun _ => ⟨⟨default, funext fun i => i.elim0⟩⟩
  | succ r ih =>
    rintro ⟨hl, hl₀⟩
    obtain ⟨⟨Q, hQ⟩⟩ := ih (fun i => l i.castSucc)
      ⟨fun _ _ hij => hl (Fin.castSucc_le_castSucc_iff.mpr hij), fun i => hl₀ _⟩
    have hb : Interlaces (Fin.snoc l 0) l := interlaces_iff.mpr fun i => by
      rw [Fin.snoc_castSucc]
      refine ⟨le_rfl, ?_⟩
      induction i using Fin.lastCases with
      | last => rw [Fin.succ_last, Fin.snoc_last]; exact hl₀ _
      | cast i => rw [Fin.succ_castSucc, Fin.snoc_castSucc]; exact hl i.castSucc_le_succ
    have hQ' : Interlaces l Q.topRow :=
      interlaces_iff.mpr fun i => by rw [hQ]; exact ⟨le_rfl, hl i.castSucc_le_succ⟩
    exact ⟨⟨Q.extend l l hb hQ', by simp⟩⟩

/-- **A top row is counted at least once exactly when it is weakly decreasing and nonnegative.** -/
theorem card_topRow_pos_iff (l : Fin r → ℤ) :
    0 < Nat.card {P : SymplecticGTPattern r // P.topRow = l} ↔ Antitone l ∧ ∀ i, 0 ≤ l i := by
  rw [Nat.card_pos_iff, and_iff_left (finite_topRow_eq l), nonempty_topRow_eq_iff]

end SymplecticGTPattern

end TauCeti
