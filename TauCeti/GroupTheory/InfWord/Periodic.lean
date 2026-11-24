/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.InfWord.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Words with two periods

Let `Λ` be an ordered abelian group and `X` a set. This file proves the lemma of Myasnikov,
Remeslennikov and Serbin on `Λ`-words with two periods, well known for finite words: if a power
`fᵐ` of `f` and a power `hⁿ` of `h` (`TauCeti.InfWord.npow`) have a common initial segment of
length at least `|f| + |h|`, then `f` and `h` commute, that is, `f ++ h = h ++ f`. For lists the
sharper Fine–Wilf bound `|f| + |h| - gcd(|f|, |h|)` holds (`List.HasPeriod.gcd`); over a
non-Archimedean `Λ` the lengths have no greatest common divisor, and the bound `|f| + |h|` needs
no Archimedean hypothesis.

## Main results

* `TauCeti.InfWord.append_comm_of_take_npow_eq`: two words with powers that agree on an initial
  segment of length `|f| + |h|` commute.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, Lemma 6.4.
-/

public section

namespace TauCeti

namespace InfWord

variable {Λ X : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
  {f h : InfWord Λ X} {m n : ℕ} {β : Λ}

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

end InfWord

end TauCeti
