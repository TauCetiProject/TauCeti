/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coprime.Basic
public import TauCeti.NumberTheory.Markoff.Descent

import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FinCases

/-!
# The coordinates of a positive Markoff triple are pairwise coprime

If `(a, b, c)` is a positive Markoff triple, then `gcd(a, b) = gcd(b, c) = gcd(a, c) = 1`.

Under the Vieta move `R_i`, the new coordinate `3 x_{i+1} x_{i+2} - x_i` differs from `-x_i` by
a multiple of each of the other two coordinates, so its coprimality with each of them is that of
`x_i`; the other pairs are untouched. So the moves preserve pairwise coprimality, over any
commutative ring. Over `ℤ`, every positive Markoff triple is a word in the moves applied to
`(1, 1, 1)` by Markoff's theorem, and `(1, 1, 1)` is pairwise coprime.

## Main results

* `TauCeti.isCoprime_markoffVieta_apply_self_iff`: the moved coordinate is coprime to another
  coordinate exactly when the old one was.
* `TauCeti.pairwise_isCoprime_markoffVieta_iff`: a Vieta move preserves and reflects pairwise
  coprimality of the coordinates.
* `TauCeti.pairwise_isCoprime_of_mem_positiveMarkoffTriples`: the coordinates of a positive
  Markoff triple are pairwise coprime.
* `TauCeti.gcd_eq_one_of_mem_positiveMarkoffTriples`: the same statement as `Int.gcd`.

## References

* Y. Zhang, *Congruence and uniqueness of certain Markoff numbers*, Acta Arith. 128 (2007), §1,
  Theorem B(a). We replace the prime-divisibility argument there by preservation of pairwise
  coprimality under each Vieta move and induction on the word given by Markoff's theorem.
-/

public section

namespace TauCeti

section CommRing

variable {R : Type*} [CommRing R] {x : Fin 3 → R} {i j : Fin 3}

/-- The moved coordinate `3 x_{i+1} x_{i+2} - x_i` is coprime to another coordinate `x_j`
exactly when `x_i` is. -/
theorem isCoprime_markoffVieta_apply_self_iff (hji : j ≠ i) :
    IsCoprime (markoffVieta i x i) (x j) ↔ IsCoprime (x i) (x j) := by
  obtain ⟨c, hc⟩ : x j ∣ 3 * x (i + 1) * x (i + 2) := by
    have hj : j = i + 1 ∨ j = i + 2 := by
      fin_cases i <;> fin_cases j <;> simp_all
    rcases hj with rfl | rfl
    · exact (dvd_mul_left _ _).mul_right _
    · exact dvd_mul_left _ _
  rw [markoffVieta_apply_self, hc, sub_eq_neg_add, IsCoprime.add_mul_left_left_iff,
    IsCoprime.neg_left_iff]

/-- A Vieta move preserves pairwise coprimality of the coordinates. -/
theorem pairwise_isCoprime_markoffVieta (h : Pairwise fun j k => IsCoprime (x j) (x k))
    (i : Fin 3) : Pairwise fun j k => IsCoprime (markoffVieta i x j) (markoffVieta i x k) := by
  intro j k hjk
  by_cases hj : j = i <;> by_cases hk : k = i
  · exact absurd (hj.trans hk.symm) hjk
  · subst hj
    rw [markoffVieta_apply_of_ne hk]
    exact (isCoprime_markoffVieta_apply_self_iff hk).2 (h hjk)
  · subst hk
    rw [markoffVieta_apply_of_ne hj]
    exact ((isCoprime_markoffVieta_apply_self_iff hj).2 (h hjk.symm)).symm
  · rw [markoffVieta_apply_of_ne hj, markoffVieta_apply_of_ne hk]
    exact h hjk

/-- A Vieta move preserves and reflects pairwise coprimality of the coordinates. -/
@[simp]
theorem pairwise_isCoprime_markoffVieta_iff :
    (Pairwise fun j k => IsCoprime (markoffVieta i x j) (markoffVieta i x k)) ↔
      Pairwise fun j k => IsCoprime (x j) (x k) := by
  refine ⟨fun h => ?_, fun h => pairwise_isCoprime_markoffVieta h i⟩
  simpa only [markoffVieta_markoffVieta] using pairwise_isCoprime_markoffVieta h i

end CommRing

/-- **The coordinates of a positive Markoff triple are pairwise coprime.** -/
theorem pairwise_isCoprime_of_mem_positiveMarkoffTriples {x : Fin 3 → ℤ}
    (hx : x ∈ positiveMarkoffTriples) : Pairwise fun i j => IsCoprime (x i) (x j) := by
  obtain ⟨l, rfl⟩ := exists_foldr_markoffVieta_eq hx
  clear hx
  induction l with
  | nil => exact fun _ _ _ => isCoprime_one_left
  | cons i l ih => exact pairwise_isCoprime_markoffVieta ih i

/-- The coordinates of a positive Markoff triple are pairwise coprime, stated with `Int.gcd`. -/
theorem gcd_eq_one_of_mem_positiveMarkoffTriples {x : Fin 3 → ℤ}
    (hx : x ∈ positiveMarkoffTriples) {i j : Fin 3} (hij : i ≠ j) : Int.gcd (x i) (x j) = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp (pairwise_isCoprime_of_mem_positiveMarkoffTriples hx hij)

/-- `(5, 13, 194)` is a positive Markoff triple, so `gcd(13, 194) = 1`. -/
example : Int.gcd 13 194 = 1 := by
  have hx : ![(5 : ℤ), 13, 194] ∈ positiveMarkoffTriples := by
    refine mem_positiveMarkoffTriples.mpr ⟨by simp [mem_markoffSet], fun i => ?_⟩
    fin_cases i <;> simp
  simpa using gcd_eq_one_of_mem_positiveMarkoffTriples hx (i := 1) (j := 2) (by decide)

end TauCeti
