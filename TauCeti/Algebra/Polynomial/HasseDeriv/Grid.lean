/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import TauCeti.Algebra.Order.Floor.Semifield
public import TauCeti.Data.Int.Interval
public import TauCeti.Algebra.Polynomial.Roots
public import TauCeti.Algebra.Polynomial.Taylor
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Nonvanishing of univariate Hasse derivatives on finite grids

Over an integral domain, a nonzero polynomial of degree less than `S.card * (N + 1)` has a
nonvanishing Hasse derivative of order at most `N` at some point of the finite set `S`.
Otherwise every point of `S` would have root multiplicity at least `N + 1`, contradicting the
bound on the sum of root multiplicities.

In characteristic zero, taking the integer grid `[-⌊B⌋₊, ⌊B⌋₊]` gives a nonzero jet of order
at most `s / B` for every positive `B` and degree bound `s`. This is the one-variable case of
nonvanishing on rectangular integer grids.

## Main results

* `TauCeti.exists_eval_polynomial_hasseDeriv_ne_zero`: nonvanishing of a bounded-order
  Hasse derivative on a finite set, in any characteristic.
* `TauCeti.exists_eval_polynomial_hasseDeriv_intCast_ne_zero`: for nonzero `p : R[X]` of
  degree `≤ s` and `B > 0`, there exist `z : ℤ` and `i : ℕ` with `|z| ≤ B`, `i ≤ s / B`, and
  `(hasseDeriv i p).eval (z : R) ≠ 0`.

## References

* J.-H. Evertse, *An improvement of the quantitative Subspace Theorem*, Compos. Math. 101 (1996),
  225–311, §7, Lemma 25.
-/

public section

namespace TauCeti

open _root_.Polynomial

variable {R : Type*}

/-- A nonzero polynomial has a nonvanishing Hasse derivative of order at most `N` at a point
of `S` whenever `S.card * (N + 1)` exceeds its degree. -/
theorem exists_eval_polynomial_hasseDeriv_ne_zero [CommRing R] [IsDomain R] {p : R[X]} (hp : p ≠ 0)
    (S : Finset R) (N : ℕ) (hdeg : p.natDegree < S.card * (N + 1)) :
    ∃ a ∈ S, ∃ i ≤ N, (hasseDeriv i p).eval a ≠ 0 := by
  by_contra! h
  have hmult (a : R) (ha : a ∈ S) : N + 1 ≤ p.rootMultiplicity a :=
    le_rootMultiplicity_of_eval_hasseDeriv_eq_zero hp fun i hi ↦ h a ha i (by omega)
  have hsum : S.card * (N + 1) ≤ p.natDegree := by
    calc S.card * (N + 1) = ∑ _a ∈ S, (N + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ a ∈ S, p.rootMultiplicity a := Finset.sum_le_sum hmult
      _ ≤ p.natDegree := sum_rootMultiplicity_le_natDegree p S
  exact hdeg.not_ge hsum

/-- Over an integral domain of characteristic zero, for any nonzero polynomial `p : R[X]` of degree
at most `s` and any `B > 0`, there exist an integer `z` with `|z| ≤ B` and an order `i` with
`i ≤ s / B` such that the `i`-th Hasse derivative of `p` does not vanish at `z`. -/
theorem exists_eval_polynomial_hasseDeriv_intCast_ne_zero [CommRing R] [IsDomain R] [CharZero R]
    {p : R[X]} (hp : p ≠ 0) {s : ℕ} (hs : p.natDegree ≤ s) {B : ℝ} (hB : 0 < B) :
    ∃ z : ℤ, ∃ i : ℕ,
      (z.natAbs : ℝ) ≤ B ∧ (i : ℝ) ≤ (s : ℝ) / B ∧ (hasseDeriv i p).eval (z : R) ≠ 0 := by
  let I : Finset ℤ := Finset.Icc (-(⌊B⌋₊ : ℤ)) (⌊B⌋₊ : ℤ)
  obtain ⟨a, ha, i, hi, hne⟩ := exists_eval_polynomial_hasseDeriv_ne_zero hp
    (I.map ⟨Int.cast, Int.cast_injective⟩) ⌊(s : ℝ) / B⌋₊ (by
      rw [card_intCast_Icc_floor]
      exact hs.trans_lt (lt_two_mul_floor_add_one_mul_floor_div_add_one s hB))
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.1 ha
  refine ⟨z, i, ?_, ?_, hne⟩
  · exact natAbs_le_of_mem_Icc_floor hB.le hz
  · exact (Nat.cast_le.2 hi).trans (Nat.floor_le (div_nonneg (Nat.cast_nonneg s) hB.le))

/-- For `p = X (X - 1) (X + 1) = X³ - X` over `ℤ` with `s = 3` and `B = 1`, `p` vanishes in order
`i = 0` at every integer `z ∈ {-1, 0, 1}`, while its first Hasse derivative `3 X² - 1` is nonzero
at `z = 0`. -/
example : (∀ z ∈ ({-1, 0, 1} : Finset ℤ),
      (hasseDeriv 0 (X ^ 3 - X : ℤ[X])).eval z = 0) ∧
    (hasseDeriv 1 (X ^ 3 - X : ℤ[X])).eval (0 : ℤ) ≠ 0 := by
  refine ⟨by simp [hasseDeriv_zero], ?_⟩
  simp

/-- For `p = X³` over `ℤ` with `s = 3` and `B = 1 / 2`, the only integer with `|z| ≤ 1 / 2` is
`z = 0`, where the Hasse derivatives of orders `0, 1, 2` vanish and the Hasse derivative of order
`3` is `1 ≠ 0`. -/
example : (∀ i < 3, (hasseDeriv i (X ^ 3 : ℤ[X])).eval (0 : ℤ) = 0) ∧
    (hasseDeriv 3 (X ^ 3 : ℤ[X])).eval (0 : ℤ) = 1 := by
  refine ⟨fun i hi ↦ ?_, by simp [← taylor_coeff]⟩
  rw [← taylor_coeff, taylor_zero', LinearMap.id_apply, coeff_X_pow, ite_eq_right (by omega)]

/-- In positive characteristic, `exists_eval_polynomial_hasseDeriv_intCast_ne_zero` can fail:
over `ZMod 2`, the nonzero polynomial `X² - X` of degree `2` vanishes in order `0` at every integer
cast, so
`s = 2` and `B = 3` (which forces `i ≤ ⌊2 / 3⌋ = 0`) admit no nonvanishing grid jet. -/
example : (X ^ 2 - X : (ZMod 2)[X]) ≠ 0 ∧
    ∀ z : ℤ, (hasseDeriv 0 (X ^ 2 - X : (ZMod 2)[X])).eval (z : ZMod 2) = 0 := by
  refine ⟨?_, fun z ↦ ?_⟩
  · intro h
    have := congrArg (fun p : (ZMod 2)[X] ↦ p.coeff 1) h
    simp at this
  · rw [hasseDeriv_zero, LinearMap.id_apply, eval_sub, eval_pow, eval_X]
    generalize (z : ZMod 2) = x
    fin_cases x <;> rfl

end TauCeti
