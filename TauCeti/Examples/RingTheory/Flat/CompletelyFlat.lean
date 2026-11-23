/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Flat.CompletelyFlat
import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Module

/-!
# Checks for complete flatness

For a prime `p`, `ℤ` is `p`-completely faithfully flat over itself, being faithfully flat, but it
is not derived `p`-complete: the series `∑ (-p)ʲ`, whose sum would be `1 / (1 + p)`, has no sum
in `ℤ`. So complete flatness does not imply completeness. On the other hand `F_p = ℤ/(p)` is not
`p`-completely flat over `ℤ`, as `Tor_1^ℤ(F_p, F_p) ≠ 0`.
-/

namespace TauCeti.Examples

open DerivedDeRham

variable (p : ℕ) [hp : Fact p.Prime]

-- `ℤ` is `p`-completely flat and `p`-completely faithfully flat over itself.
example : IsCompletelyFlatModule ℤ (Ideal.span {(p : ℤ)}) (ModuleCat.of ℤ ℤ) :=
  isCompletelyFlatModule_of_flat _

example : IsCompletelyFaithfullyFlatModule ℤ (Ideal.span {(p : ℤ)}) (ModuleCat.of ℤ ℤ) :=
  isCompletelyFaithfullyFlatModule_of_faithfullyFlat _

-- `ℤ` is not derived `p`-complete: the telescope `(zₙ) ↦ (zₙ - p zₙ₊₁)` does not reach the
-- sequence `((-1)ⁿ)`, which would need `z₀ = 1 / (1 + p)`.
example : ¬ IsDerivedComplete (Ideal.span {(p : ℤ)}) ℤ := by
  intro h
  obtain ⟨z, hz⟩ := (h.bijective (Ideal.mem_span_singleton_self (p : ℤ))).2 fun n => (-1) ^ n
  have hstep (k : ℕ) : z k = (-1) ^ k + p * z (k + 1) := by
    have := congr_fun hz k
    simp only [telescope_apply, smul_eq_mul] at this
    linear_combination this
  let w (n : ℕ) : ℤ := (1 + p) * (-1) ^ n * z n - 1
  have hw (k : ℕ) : w 0 = (-p : ℤ) ^ k * w k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hsq : ((-1 : ℤ) ^ k) ^ 2 = 1 := by rw [← pow_mul]; exact Even.neg_one_pow ⟨k, by ring⟩
      rw [ih]
      simp only [w, hstep k, pow_succ]
      linear_combination (-(p : ℤ)) ^ k * (1 + p) * hsq
  have hw0 : w 0 = 0 := by
    have hdvd (k : ℕ) : (p : ℤ) ^ k ∣ w 0 := by
      rw [hw k, neg_pow]
      exact Dvd.intro_left ((-1) ^ k * w k) (by ring)
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd (w 0).natAbs) ?_
    rw [Int.natAbs_pow, Int.natAbs_natCast]
    exact Nat.lt_pow_self hp.out.one_lt
  have h1 : (1 + p : ℤ) * z 0 = 1 := by
    simp only [w, pow_zero, mul_one] at hw0
    linear_combination hw0
  have := hp.out.two_le
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h2 | h2 <;> omega

-- `F_p` is not `p`-completely flat over `ℤ`.
example : ¬ IsCompletelyFlatModule ℤ (Ideal.span {(p : ℤ)})
    (ModuleCat.of ℤ (ℤ ⧸ Ideal.span {(p : ℤ)})) :=
  not_isCompletelyFlatModule_quotient_self
    (IsRegular.of_ne_zero' (by exact_mod_cast hp.out.ne_zero))
    (by rw [Int.isUnit_iff]; have := hp.out.two_le; omega)

end TauCeti.Examples
