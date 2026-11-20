/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.InfWord.CDR

/-!
# Powers of infinite words and words with two periods

Let `Λ` be a discretely ordered abelian group and `X` a set. For a `Λ`-word `u` and a natural
number `n`, the word `u.npow n` is the concatenation of `n` copies of `u`; it is reduced for
every `n` when `u` is cyclically reduced, and then it is the `n`-th power of `u` for the partial
multiplication of reduced words.

The main result is the lemma of Myasnikov, Remeslennikov and Serbin on words with two periods,
well known for finite words: if a power of `f` and a power of `h` have a common initial segment of
length at least `|f| + |h|`, then `f` and `h` commute, that is, `f ++ h = h ++ f`. For lists the
sharper Fine–Wilf bound `|f| + |h| - gcd(|f|, |h|)` holds (`List.HasPeriod.gcd`); over a
non-Archimedean `Λ` the lengths have no greatest common divisor, and the bound `|f| + |h|` needs
no Archimedean hypothesis.

## Main definitions

* `TauCeti.InfWord.npow`: the concatenation of `n` copies of a word.

## Main results

* `TauCeti.InfWord.IsCyclicallyReduced.isMul_npow`: for a cyclically reduced word `u`,
  `uᵐ ∗ uⁿ = uᵐ⁺ⁿ`.
* `TauCeti.InfWord.append_comm_of_take_npow_eq`: two words with powers that agree on an initial
  segment of length `|f| + |h|` commute.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §3.3 and Lemma 6.4.
-/

public section

namespace TauCeti

namespace InfWord

variable {Λ X : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
  {f h u : InfWord Λ X} {m n : ℕ} {β : Λ}

/-- The concatenation of `n` copies of the word `u`. -/
def npow (u : InfWord Λ X) : ℕ → InfWord Λ X
  | 0 => empty Λ X
  | n + 1 => npow u n ++ u

@[simp]
theorem npow_zero (u : InfWord Λ X) : u.npow 0 = empty Λ X := (rfl)

theorem npow_succ (u : InfWord Λ X) (n : ℕ) : u.npow (n + 1) = u.npow n ++ u := (rfl)

@[simp]
theorem npow_one (u : InfWord Λ X) : u.npow 1 = u :=
  (npow_succ u 0).trans (empty_append u)

theorem npow_add (u : InfWord Λ X) (m n : ℕ) : u.npow (m + n) = u.npow m ++ u.npow n := by
  induction n with
  | zero => simp
  | succ n ih => simp [← add_assoc, npow_succ, ih]

theorem npow_succ' (u : InfWord Λ X) (n : ℕ) : u.npow (n + 1) = u ++ u.npow n := by
  rw [add_comm, npow_add, npow_one]

@[simp]
theorem length_npow (u : InfWord Λ X) (n : ℕ) : (u.npow n).length = n • u.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [npow_succ, ih, succ_nsmul]

@[simp]
theorem npow_empty (n : ℕ) : (empty Λ X).npow n = empty Λ X := by
  induction n <;> simp [npow_succ, *]

/-- A shorter power of `u` is an initial segment of a longer one. -/
theorem take_npow_of_le (hmn : m ≤ n) (hβ : β ≤ m • u.length) :
    (u.npow n).take β = (u.npow m).take β := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [npow_add, take_append_of_le_length _ (by simpa using hβ)]

/-- A power of `u` has period `|u|`: its initial segment of length `|u| + γ` is `u` followed by
its initial segment of length `γ`. -/
private theorem take_npow_length_add {γ : Λ} (hγ : 0 ≤ γ) (hk : u.length + γ ≤ n • u.length) :
    (u.npow n).take (u.length + γ) = u ++ (u.npow n).take γ := by
  cases n with
  | zero =>
    have : u = empty Λ X := length_eq_zero_iff.1 (by simp at hk; grind [u.length_nonneg])
    simp [this]
  | succ n =>
    rw [npow_succ', take_append_length_add _ _ hγ, ← npow_succ',
      take_npow_of_le n.le_succ (by rw [succ_nsmul] at hk; grind)]

/-- If powers `fᵐ` and `hⁿ` of two words agree on an initial segment of length at least
`|f| + |h|`, then `f` and `h` commute. -/
theorem append_comm_of_take_npow_eq (hβ : f.length + h.length ≤ β) (hn : β ≤ n • h.length)
    (heq : (f.npow m).take β = (h.npow n).take β) : f ++ h = h ++ f := by
  have hf := f.length_nonneg
  have hh := h.length_nonneg
  have htake (γ : Λ) (hγ : γ ≤ β) : (f.npow m).take γ = (h.npow n).take γ := by
    simpa [min_eq_left hγ] using congrArg (take · γ) heq
  have hm : β ≤ m • f.length := by
    have := congrArg length heq
    simp only [length_take, length_npow] at this
    grind [nsmul_nonneg hf m]
  have hf' := take_npow_length_add (n := m) hh (hβ.trans hm)
  have hh' := take_npow_length_add (n := n) hf (by rw [add_comm]; exact hβ.trans hn)
  have hf₀ := take_npow_length_add (u := f) (n := m) le_rfl (by grind)
  have hh₀ := take_npow_length_add (u := h) (n := n) le_rfl (by grind)
  simp only [add_zero, take_zero, append_empty] at hf₀ hh₀
  calc f ++ h = (f.npow m).take (f.length + h.length) := by
        rw [hf', htake _ (by grind), hh₀]
    _ = h ++ f := by rw [htake _ hβ, add_comm, hh', ← htake _ (by grind), hf₀]

section Discrete

variable [SuccOrder Λ]

@[simp]
theorem inv_npow (u : InfWord Λ X) (n : ℕ) : (u.npow n)⁻¹ = u⁻¹.npow n := by
  induction n with
  | zero => simp
  | succ n ih => rw [npow_succ, inv_append, ih, npow_succ']

private theorem IsCyclicallyReduced.isReduced_npow (hu : u.IsCyclicallyReduced) (n : ℕ) :
    (u.npow n).IsReduced := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine isReduced_append_iff.2 ⟨ih, hu.isReduced, fun hn hu0 => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
    rw [npow_succ, length_append, letter_append_length_add _ _ hu0]
    exact hu.letter_succ_zero_ne hu0

/-- The powers of a cyclically reduced word are cyclically reduced. -/
theorem IsCyclicallyReduced.npow (hu : u.IsCyclicallyReduced) (n : ℕ) :
    (u.npow n).IsCyclicallyReduced := by
  rw [isCyclicallyReduced_iff_isReduced_append_self, ← npow_add]
  exact hu.isReduced_npow _

/-- For a cyclically reduced word `u`, `uᵐ ∗ uⁿ = uᵐ⁺ⁿ`. -/
theorem IsCyclicallyReduced.isMul_npow (hu : u.IsCyclicallyReduced) (m n : ℕ) :
    IsMul (u.npow m) (u.npow n) (u.npow (m + n)) := by
  rw [npow_add]
  exact isMul_append (npow_add u m n ▸ hu.isReduced_npow (m + n))

end Discrete

end InfWord

end TauCeti
