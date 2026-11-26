/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Markoff.PennerWeight
public import Mathlib.Data.ZMod.Basic

import TauCeti.Algebra.BigOperators.Finset.Involution
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.LinearCombination

/-!
# Chen's divisibility theorem for Markoff graphs

Let `p` be a prime other than `3`. Every finite subset `S` of the nonzero locus `X*(𝔽_p)` of the
Markoff surface `x₀² + x₁² + x₂² = 3 x₀ x₁ x₂` that is stable under the three Vieta moves has
cardinality divisible by `p`. The orbits of the moves are such sets. The theorem is due to
W. Chen; we follow Martin's proof.

For `p > 3` the argument works over any field `K` in which `2` and `3` are nonzero. Each point of
`X*(K)` carries three Penner weights summing to `1` (`sum_pennerWeight`), and the `i`-th move
exchanges `w_i` with `1 - w_i` (`pennerWeight_add_pennerWeight_markoffVieta`). Summing the `i`-th
weight over `S` and pairing `x` with `R_i x` gives `#S / 2`, so summing all weights over `S` gives
both `#S` and `3 #S / 2` in `K`; hence `#S = 0` in `K`. Over a field of characteristic zero this
says that no nonempty finite subset of `X*(K)` is stable under the moves.

For `p = 2` the four points of `X*(𝔽₂)` other than the origin are joined by moves to `(1, 1, 1)`,
so a nonempty stable set is all of them. For `p = 3` the theorem fails: `X*(𝔽₃) = {±1}³` has
eight points and is stable, since each move changes the sign of one coordinate.

## Main results

* `TauCeti.natCast_card_eq_zero_of_markoffVieta_mem`: over a field with `2 ≠ 0` and `3 ≠ 0`, a
  finite Vieta-stable subset of `X*(K)` has cardinality zero in `K`.
* `TauCeti.mem_markoffSetNonzero_zmod_two`: `X*(𝔽₂)` consists of `(1, 1, 1)` and the three
  triples with one vanishing coordinate.
* `TauCeti.dvd_card_of_markoffVieta_mem`: **Chen's theorem**: for a prime `p ≠ 3`, a finite
  Vieta-stable subset of `X*(𝔽_p)` has cardinality divisible by `p`.

## References

* W. Y. Chen, *Nonabelian level structures, Nielsen equivalence, and Markoff triples*, Ann. of
  Math. 199 (2024), 301–443.
* D. E. Martin, *A new proof of Chen's theorem for Markoff graphs*, Invent. Math. 241 (2025),
  623–626, Theorem 1.4 and §2.
-/

public section

namespace TauCeti

open Finset

variable {K : Type*} [Field K]

/-- Pairing `x` with `R_i x` shows that the `i`-th Penner weights of an `R_i`-stable finite set
sum to half its cardinality. -/
private theorem two_mul_sum_pennerWeight_eq_card (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {S : Finset (Fin 3 → K)} (i : Fin 3) (hstable : ∀ x ∈ S, markoffVieta i x ∈ S) :
    2 * ∑ x ∈ S, pennerWeight i x = #S := by
  have h := two_nsmul_sum_eq_card_nsmul_of_involution S (markoffVieta i) hstable
    (fun x _ => markoffVieta_markoffVieta i x)
    (fun x _ => pennerWeight_add_pennerWeight_markoffVieta h2 h3 i x)
  rwa [nsmul_eq_mul, nsmul_one, Nat.cast_ofNat] at h

/-- **Chen's divisibility theorem, over a field.** If `2` and `3` are nonzero in the field `K`,
every finite subset `S` of the nonzero locus `X*(K)` that is stable under the three Vieta moves
has cardinality zero in `K`. In characteristic `p > 3` this says that `p` divides `#S`; in
characteristic zero it says that `S` is empty. -/
theorem natCast_card_eq_zero_of_markoffVieta_mem (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {S : Finset (Fin 3 → K)} (hS : ∀ x ∈ S, x ∈ markoffSetNonzero K)
    (hstable : ∀ i, ∀ x ∈ S, markoffVieta i x ∈ S) : (#S : K) = 0 := by
  -- Summing all three weights over `S` gives `#S`, since they sum to `1` at each point ...
  have htot : ∑ i, ∑ x ∈ S, pennerWeight i x = #S := by
    rw [sum_comm, sum_congr rfl fun x hx => sum_pennerWeight h2 h3 (hS x hx), sum_const,
      nsmul_one]
  -- ... and also `3 #S / 2`, since each weight sums to `#S / 2`.
  have h32 : (3 : K) * #S = 2 * #S := by
    calc (3 : K) * #S = ∑ i : Fin 3, 2 * ∑ x ∈ S, pennerWeight i x := by
          simp [two_mul_sum_pennerWeight_eq_card h2 h3 _ (hstable _)]
      _ = 2 * #S := by rw [← mul_sum, htot]
  linear_combination h32

/-- The nonzero locus `X*(𝔽₂)` consists of `(1, 1, 1)` and its three neighbours `(0, 1, 1)`,
`(1, 0, 1)` and `(1, 1, 0)`. -/
theorem mem_markoffSetNonzero_zmod_two {y : Fin 3 → ZMod 2} :
    y ∈ markoffSetNonzero (ZMod 2) ↔
      y ∈ ({![0, 1, 1], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1]} : Finset (Fin 3 → ZMod 2)) := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, y = ![a, b, c] :=
    ⟨y 0, y 1, y 2, by ext i; fin_cases i <;> rfl⟩
  simp only [mem_markoffSetNonzero, mem_markoffSet]
  revert a b c
  decide

/-- Over `𝔽₂` the Vieta move `R_i` sends `(1, 1, 1)` to the triple whose `i`-th coordinate is `0`
and whose other coordinates are `1`. -/
private theorem markoffVieta_one_zmod_two (i : Fin 3) :
    markoffVieta i (![1, 1, 1] : Fin 3 → ZMod 2) = Function.update ![1, 1, 1] i 0 := by
  ext j
  rcases eq_or_ne j i with rfl | h
  · rw [markoffVieta_apply_self, Function.update_self]
    fin_cases j <;> decide
  · simp [h]

/-- Chen's divisibility theorem at `p = 2`: a nonempty Vieta-stable subset of `X*(𝔽₂)` contains
`(1, 1, 1)`, hence its three neighbours, so it is all of `X*(𝔽₂)`, which has four points. -/
private theorem two_dvd_card_of_markoffVieta_mem {S : Finset (Fin 3 → ZMod 2)}
    (hS : ∀ x ∈ S, x ∈ markoffSetNonzero (ZMod 2))
    (hstable : ∀ i, ∀ x ∈ S, markoffVieta i x ∈ S) : 2 ∣ #S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  -- The neighbour of `(1, 1, 1)` with vanishing `i`-th coordinate, and its move back.
  have hnbr : ∀ i, Function.update ![1, 1, 1] i 0 ∈ S → (![1, 1, 1] : Fin 3 → ZMod 2) ∈ S :=
    fun i h => by
      simpa [← markoffVieta_one_zmod_two] using hstable i _ h
  have hone : (![1, 1, 1] : Fin 3 → ZMod 2) ∈ S := by
    have hxT := mem_markoffSetNonzero_zmod_two.mp (hS x hx)
    simp only [mem_insert, mem_singleton] at hxT
    rcases hxT with rfl | rfl | rfl | rfl
    · exact hnbr 0 (by convert hx using 1; decide)
    · exact hnbr 1 (by convert hx using 1; decide)
    · exact hnbr 2 (by convert hx using 1; decide)
    · exact hx
  have hS' : S = {![0, 1, 1], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1]} := by
    refine subset_antisymm (fun y hy => mem_markoffSetNonzero_zmod_two.mp (hS y hy)) ?_
    have hmove : ∀ i, Function.update ![1, 1, 1] i 0 ∈ S := fun i => by
      simpa [markoffVieta_one_zmod_two] using hstable i _ hone
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · convert hmove 0 using 1; decide
    · convert hmove 1 using 1; decide
    · convert hmove 2 using 1; decide
    · exact hone
  rw [hS']
  decide

/-- **Chen's divisibility theorem.** For a prime `p ≠ 3`, every finite subset of the nonzero
locus `X*(𝔽_p)` of the Markoff surface that is stable under the three Vieta moves has
cardinality divisible by `p`. The hypothesis `p ≠ 3` is necessary: `X*(𝔽₃)` is stable and has
eight points. -/
theorem dvd_card_of_markoffVieta_mem {p : ℕ} [Fact p.Prime] (hp : p ≠ 3)
    {S : Finset (Fin 3 → ZMod p)} (hS : ∀ x ∈ S, x ∈ markoffSetNonzero (ZMod p))
    (hstable : ∀ i, ∀ x ∈ S, markoffVieta i x ∈ S) : p ∣ #S := by
  rcases eq_or_ne p 2 with rfl | hp2
  · exact two_dvd_card_of_markoffVieta_mem hS hstable
  have h2 : (2 : ZMod p) ≠ 0 := by exact_mod_cast ZMod.prime_ne_zero p 2 hp2
  have h3 : (3 : ZMod p) ≠ 0 := by exact_mod_cast ZMod.prime_ne_zero p 3 hp
  exact (ZMod.natCast_eq_zero_iff _ _).mp
    (natCast_card_eq_zero_of_markoffVieta_mem (K := ZMod p) h2 h3 hS hstable)

/-! ### Examples -/

/-- The characteristic-three exception: the eight points of `X*(𝔽₃) = {±1}³` form a Vieta-stable
set whose cardinality is not divisible by `3`. -/
example : ∃ S : Finset (Fin 3 → ZMod 3), (∀ x ∈ S, x ∈ markoffSetNonzero (ZMod 3)) ∧
    (∀ i, ∀ x ∈ S, markoffVieta i x ∈ S) ∧ #S = 8 := by
  let S : Finset (Fin 3 → ZMod 3) := {![1, 1, 1], ![1, 1, -1], ![1, -1, 1], ![1, -1, -1],
    ![-1, 1, 1], ![-1, 1, -1], ![-1, -1, 1], ![-1, -1, -1]}
  have hS : ∀ y : Fin 3 → ZMod 3, y ∈ markoffSetNonzero (ZMod 3) ↔ y ∈ S := fun y => by
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, y = ![a, b, c] :=
      ⟨y 0, y 1, y 2, by ext i; fin_cases i <;> rfl⟩
    simp only [mem_markoffSetNonzero, mem_markoffSet, S]
    revert a b c
    decide
  refine ⟨S, fun x hx => (hS x).mpr hx, fun i x hx => ?_, by decide⟩
  exact (hS _).mp (markoffVieta_mem_markoffSetNonzero_iff.mpr ((hS x).mpr hx))

end TauCeti
