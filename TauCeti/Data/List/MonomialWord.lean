/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Sort

/-!
# Ordered monomial words

The ordered monomial word `1^{α₁} 2^{α₂} ⋯ m^{α_m}` of an exponent vector `α : Fin m → ℕ` is the
sorted list in which the letter `i` occurs `α i` times. Ordered monomial words index ordered PBW
monomials and the Sobolev seminorms of a Lie group representation. The exponent vectors of total
degree at most `k` form the finite type `SobolevIndex m k`, and the sorted words of length at most
`k` are exactly their ordered monomial words.

## Main definitions

* `TauCeti.monomialWord α`: the ordered monomial word of an exponent vector.
* `TauCeti.SobolevIndex m k`: the exponent vectors `α : Fin m → ℕ` with `|α| ≤ k`.

## Main results

* `TauCeti.length_monomialWord`, `TauCeti.count_monomialWord`: its length is `|α|` and the letter
  `i` occurs `α i` times.
* `TauCeti.monomialWord_eq_nil_iff`: the ordered monomial word is empty only for `α = 0`.
* `TauCeti.pairwise_monomialWord`: ordered monomial words are sorted.
* `TauCeti.monomialWord_count`: a sorted word is the ordered monomial word of its letter counts.
* `TauCeti.exists_sobolevIndex_monomialWord_eq`: a sorted word of length at most `k` is the
  ordered monomial word of an index in `SobolevIndex m k`.
-/

public section

namespace TauCeti

variable {m : ℕ}

/-- The ordered monomial word `1^{α₁} 2^{α₂} ⋯ m^{α_m}` of an exponent vector `α`. -/
def monomialWord (α : Fin m → ℕ) : List (Fin m) :=
  (List.finRange m).flatMap fun i ↦ List.replicate (α i) i

/-- The ordered monomial word of `α` lists the letters `1, …, m` in order, with `i` repeated
`α i` times. -/
theorem monomialWord_def (α : Fin m → ℕ) :
    monomialWord α = (List.finRange m).flatMap fun i ↦ List.replicate (α i) i :=
  (rfl)

/-- The ordered monomial word of `α` has length `|α|`. -/
@[simp]
theorem length_monomialWord (α : Fin m → ℕ) : (monomialWord α).length = ∑ i, α i := by
  simp [monomialWord, List.length_flatMap, Fin.sum_univ_def]

/-- The letter `i` occurs `α i` times in the ordered monomial word of `α`. -/
@[simp]
theorem count_monomialWord (α : Fin m → ℕ) (i : Fin m) : (monomialWord α).count i = α i := by
  rw [monomialWord, List.count_flatMap, ← Fin.sum_univ_def]
  simp [List.count_replicate]

/-- An ordered monomial word determines its exponent vector. -/
theorem monomialWord_injective : Function.Injective (monomialWord (m := m)) := fun α β h ↦
  funext fun i ↦ by rw [← count_monomialWord α i, ← count_monomialWord β i, h]

/-- The ordered monomial word of `α` is empty exactly for the zero exponent vector. -/
@[simp]
theorem monomialWord_eq_nil_iff {α : Fin m → ℕ} : monomialWord α = [] ↔ α = 0 := by
  rw [← List.length_eq_zero_iff, length_monomialWord, Finset.sum_eq_zero_iff, funext_iff]
  simp

/-- **Ordered monomial words are sorted.** -/
theorem pairwise_monomialWord (α : Fin m → ℕ) : (monomialWord α).Pairwise (· ≤ ·) := by
  rw [monomialWord, List.pairwise_flatMap]
  refine ⟨fun i _ ↦ List.pairwise_replicate.2 (Or.inr le_rfl), ?_⟩
  refine (List.pairwise_le_finRange m).imp fun {i j} hij x hx y hy ↦ ?_
  rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
  exact hij

/-- **A sorted word is the ordered monomial word of its letter counts.** -/
theorem monomialWord_count {w : List (Fin m)} (hw : w.Pairwise (· ≤ ·)) :
    monomialWord (fun i ↦ w.count i) = w :=
  List.Perm.eq_of_pairwise' (pairwise_monomialWord _) hw
    (List.perm_iff_count.2 fun i ↦ count_monomialWord _ i)

/-! ### Exponent vectors of bounded degree -/

/-- The exponent vectors `α : Fin m → ℕ` of total degree `|α| = ∑ i, α i ≤ k`, with entries
recorded in `Fin (k + 1)` so that they form a finite type. -/
abbrev SobolevIndex (m k : ℕ) : Type :=
  {α : Fin m → Fin (k + 1) // ∑ i, (α i : ℕ) ≤ k}

/-- The exponent vector in `ℕ` of an index in `SobolevIndex m k`. -/
def SobolevIndex.exponent {k : ℕ} (α : SobolevIndex m k) (i : Fin m) : ℕ :=
  α.val i

/-- The `i`-th entry of the exponent vector of `α`. -/
@[simp]
theorem SobolevIndex.exponent_apply {k : ℕ} (α : SobolevIndex m k) (i : Fin m) :
    α.exponent i = α.val i :=
  (rfl)

/-- An index in `SobolevIndex m k` is determined by its exponent vector. -/
theorem SobolevIndex.exponent_injective {k : ℕ} :
    Function.Injective (SobolevIndex.exponent (m := m) (k := k)) := fun _ _ h ↦
  Subtype.ext (funext fun i ↦ Fin.ext (congrFun h i))

/-- A sorted word of length at most `k` is the ordered monomial word of an index in
`SobolevIndex m k`. -/
theorem exists_sobolevIndex_monomialWord_eq {k : ℕ} {w : List (Fin m)}
    (hw : w.Pairwise (· ≤ ·)) (hk : w.length ≤ k) :
    ∃ α : SobolevIndex m k, monomialWord α.exponent = w := by
  have hsum : ∑ i, w.count i = w.length := by
    rw [← length_monomialWord, monomialWord_count hw]
  refine ⟨⟨fun i ↦ ⟨w.count i, Nat.lt_succ_of_le (List.count_le_length.trans hk)⟩, ?_⟩, ?_⟩
  · simpa [hsum] using hk
  · refine (congrArg monomialWord (funext fun i ↦ ?_)).trans (monomialWord_count hw)
    simp only [SobolevIndex.exponent_apply]

end TauCeti
