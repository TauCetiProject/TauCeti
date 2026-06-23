/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.NumberTheory.Multiquadratic.Degree
import TauCeti.NumberTheory.Multiquadratic.Squarefree
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Multiquadratic fields with pairwise-coprime squarefree integer radicands

The field-generic degree theorem `TauCeti.Multiquadratic.finrank_adjoin_range` gives a
multiquadratic field degree `2ⁿ` once its radicands are **square-class independent**: no nonempty
subset product of them is a square. The genus theory the roadmap targets works with the rational
field `ℚ(√d₁, …, √dₙ)` for **squarefree integers** `dᵢ`, where the radicands range over composite
and negative values (`ℚ(√-3, √-7)`, `ℚ(√6, √35)`), not just the distinct primes already handled in
`TauCeti.NumberTheory.Multiquadratic.PrimeRadicands`.

This file supplies square-class independence in that setting: a family of **pairwise coprime,
squarefree, non-unit** integers is square-class independent. The argument is the same one that
works for distinct primes, run at the level of the integers: a nonempty subset product of pairwise
coprime squarefree integers is again squarefree (Mathlib's
`Finset.squarefree_prod_of_pairwise_isCoprime`) and is not a unit (it has a non-unit factor), so it
is not a square; and an integer is a square in `ℚ` iff it is a square in `ℤ`
(`Rat.isSquare_intCast_iff`). The distinct-primes statement `not_isSquare_prod_primes` is the
special case where each radicand is prime.

## Main results

* `TauCeti.Multiquadratic.not_isSquare_prod_of_coprime_squarefree`: for pairwise coprime squarefree
  non-unit integers `d i`, no nonempty subset product `∏_{i ∈ S} d i` is a square in `ℤ`.
* `TauCeti.Multiquadratic.not_isSquare_prod_of_coprime_squarefree_rat`: the same square-class
  independence cast to `ℚ`, in the `∀ S` shape the degree theorem consumes.
* `TauCeti.Multiquadratic.finrank_adjoin_range_of_coprime_squarefree`:
  `[ℚ(√d₁, …, √dₙ) : ℚ] = 2^|ι|` for pairwise coprime squarefree non-unit integer radicands, the
  squarefree-integer corollary of `finrank_adjoin_range`.
* `TauCeti.Multiquadratic.finrank_adjoin_sqrt_six_thirtyfive`: `[ℚ(√6, √35) : ℚ] = 4`, a worked
  example with composite radicands, beyond the reach of the distinct-primes corollary.
-/

open scoped Function

namespace TauCeti.Multiquadratic

/-- **Square-class independence of pairwise coprime squarefree integers.** If the radicands `d i`
are pairwise coprime, each squarefree, and each a non-unit, then no nonempty subset product
`∏_{i ∈ S} d i` is a square in `ℤ`. This generalises `not_isSquare_prod_primes` (the distinct-primes
case) to the squarefree integers the genus theory uses, and supplies the square-class independence
the multiquadratic degree theorem `finrank_adjoin_range` consumes. -/
theorem not_isSquare_prod_of_coprime_squarefree {ι : Type*} (d : ι → ℤ) {S : Finset ι}
    (hcop : (S : Set ι).Pairwise (IsCoprime on d)) (hsf : ∀ i ∈ S, Squarefree (d i))
    (hnu : ∀ i ∈ S, ¬ IsUnit (d i)) (hS : S.Nonempty) :
    ¬ IsSquare (∏ i ∈ S, d i) := by
  refine not_isSquare_of_squarefree_of_not_isUnit ?_ ?_
  · exact Finset.squarefree_prod_of_pairwise_isCoprime
      (fun i hi j hj hij => (hcop hi hj hij).isRelPrime) hsf
  · obtain ⟨i, hi⟩ := hS
    exact fun hu => hnu i hi (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem d hi) hu)

/-- **Square-class independence cast to `ℚ`.** If `d : ι → ℤ` is pairwise coprime with each entry
squarefree and a non-unit, then no nonempty subset product `∏_{i ∈ S} (d i : ℚ)` is a square in
`ℚ`. This is the `∀ S` shape of `hindep` the degree and Galois-group theorems consume directly. -/
theorem not_isSquare_prod_of_coprime_squarefree_rat {ι : Type*} (d : ι → ℤ)
    (hcop : Pairwise (IsCoprime on d)) (hsf : ∀ i, Squarefree (d i)) (hnu : ∀ i, ¬ IsUnit (d i)) :
    ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)) := by
  intro S hS
  rw [← Int.cast_prod, Rat.isSquare_intCast_iff]
  exact not_isSquare_prod_of_coprime_squarefree d (hcop.set_pairwise _)
    (fun i _ => hsf i) (fun i _ => hnu i) hS

/-- **Degree of a multiquadratic field with squarefree integer radicands.** If `d : ι → ℤ` is
pairwise coprime with each entry squarefree and a non-unit, and `root i` is a square root of `d i`
in a field `L` over `ℚ` (so `ℚ(√d₁, …, √dₙ)` makes sense even for the negative radicands the genus
theory needs), then `[ℚ(rootᵢ : i) : ℚ] = 2^|ι|`. This is the squarefree-integer corollary of the
field-generic degree theorem `finrank_adjoin_range`. -/
theorem finrank_adjoin_range_of_coprime_squarefree {ι : Type*} [Finite ι] {L : Type*} [Field L]
    [Algebra ℚ L] (d : ι → ℤ) (root : ι → L) (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (d i))
    (hcop : Pairwise (IsCoprime on d)) (hsf : ∀ i, Squarefree (d i)) (hnu : ∀ i, ¬ IsUnit (d i)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range root)) = 2 ^ Nat.card ι :=
  finrank_adjoin_range (d := fun i => (d i : ℚ)) hroot
    (not_isSquare_prod_of_coprime_squarefree_rat d hcop hsf hnu)

/-- **Worked example: `[ℚ(√6, √35) : ℚ] = 4`.** The radicands `6 = 2·3` and `35 = 5·7` are
composite, so this lies beyond the distinct-primes corollary `finrank_adjoin_sqrt_primes`; it is
covered by `finrank_adjoin_range_of_coprime_squarefree` because `6` and `35` are coprime,
squarefree, and not units. -/
theorem finrank_adjoin_sqrt_six_thirtyfive :
    Module.finrank ℚ
      (IntermediateField.adjoin ℚ {Real.sqrt 6, Real.sqrt 35} : IntermediateField ℚ ℝ) = 4 := by
  have hcop : Pairwise (IsCoprime on (![6, 35] : Fin 2 → ℤ)) := by
    have h : IsCoprime (6 : ℤ) 35 := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
    have h' : IsCoprime (35 : ℤ) 6 := h.symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Function.onFun]
  have h6 : Squarefree (6 : ℤ) := by
    have : Squarefree ((2 : ℤ) * 3) := squarefree_mul_iff.mpr
      ⟨(Int.isCoprime_iff_gcd_eq_one.mpr (by decide)).isRelPrime,
        (Int.prime_iff_natAbs_prime.2 (by decide)).squarefree,
        (Int.prime_iff_natAbs_prime.2 (by decide)).squarefree⟩
    simpa using this
  have h35 : Squarefree (35 : ℤ) := by
    have : Squarefree ((5 : ℤ) * 7) := squarefree_mul_iff.mpr
      ⟨(Int.isCoprime_iff_gcd_eq_one.mpr (by decide)).isRelPrime,
        (Int.prime_iff_natAbs_prime.2 (by decide)).squarefree,
        (Int.prime_iff_natAbs_prime.2 (by decide)).squarefree⟩
    simpa using this
  have hsf : ∀ i, Squarefree ((![6, 35] : Fin 2 → ℤ) i) := by
    intro i
    fin_cases i
    · exact h6
    · exact h35
  have hnu : ∀ i, ¬ IsUnit ((![6, 35] : Fin 2 → ℤ) i) := by
    intro i
    fin_cases i <;> simp [Int.isUnit_iff]
  have h := finrank_adjoin_range_of_coprime_squarefree (L := ℝ) ![6, 35]
    (fun i => Real.sqrt ((![6, 35] : Fin 2 → ℤ) i))
    (fun i => by fin_cases i <;> exact sq_sqrt_intCast (by norm_num)) hcop hsf hnu
  have hset : (Set.range fun i : Fin 2 => Real.sqrt ((![6, 35] : Fin 2 → ℤ) i))
      = {Real.sqrt 6, Real.sqrt 35} := by
    ext x
    simp [Fin.exists_fin_two, eq_comm]
  rw [hset] at h
  rw [h]
  simp

end TauCeti.Multiquadratic
