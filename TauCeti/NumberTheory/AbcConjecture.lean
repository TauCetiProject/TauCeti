/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Radical.NatInt

/-!
# The abc conjecture

The **abc conjecture** of Masser and Oesterlé: for every `ε > 0` there is a constant `C` such that
every triple of coprime integers `a + b = c` satisfies

`max(|a|, |b|, |c|) ≤ C · rad(a b c) ^ (1 + ε)`,

where `rad n` is the product of the distinct primes dividing `n`. This file states the conjecture as
the proposition `TauCeti.AbcConjecture`, and proves that two other common formulations are
equivalent to it. It does not prove the conjecture.

The statement allows any signs, and zero. Coprimality of `a` and `b` makes `a`, `b` and `c`
pairwise coprime. When one of them vanishes the other two are `±1`, and the bound holds once
`C ≥ 1`. Otherwise two of `a`, `b` and `-c` have the same sign, and their absolute values add up to
the absolute value of the third. So every such triple is, up to order and signs, a triple of
coprime positive integers `x + y = z` with the same radical, and `z` is the largest of the three
absolute values. The conjecture is therefore equivalent to its form for positive integers
(`TauCeti.abcConjecture_iff_nat`).

The statement `ABC.abc` of the `formal-conjectures` project has another shape: for every `ε > 0`,
only finitely many triples of pairwise coprime positive integers `a + b = c` have
`rad(a b c) ^ (1 + ε) < c`. Its radical `n.primeFactors.prod id` is Mathlib's
`UniqueFactorizationMonoid.radical` on `ℕ` (`Nat.radical_eq_prod_primeFactors`). That statement is
equivalent to `TauCeti.AbcConjecture` too (`TauCeti.abcConjecture_iff_forall_finite`). A bound with
constant `C` at the exponent `1 + ε / 2` leaves as exceptions at the exponent `1 + ε` only triples
with `rad(a b c) ^ (ε / 2) < C`, and these have bounded `c`. Conversely, the largest `c` among the
finitely many exceptions at the exponent `1 + ε` is a constant for that exponent.

The weaker statements with `1 + ε` replaced by `κ + ε` for a fixed `κ ≥ 1` are the abc conjecture
with exponent `κ`, `TauCeti.AbcConjectureWithExponent κ`. Szpiro's conjecture implies the one with
exponent `3 / 2`, through the Frey curve
(`TauCeti.AlgorithmicSzpiroConjecture.abcConjectureWithExponent`).

## Main definitions

* `TauCeti.AbcConjecture`: the abc conjecture.
* `TauCeti.AbcConjectureWithExponent κ`: the abc conjecture with exponent `κ`.

## Main results

* `TauCeti.abcConjecture_iff_nat`: the conjecture is its form for coprime positive integers
  `a + b = c`, bounding `c`.
* `TauCeti.abcConjecture_iff_forall_finite`: the conjecture is the statement that, for every
  `ε > 0`, only finitely many triples have `rad(a b c) ^ (1 + ε) < c`.
* `TauCeti.AbcConjectureWithExponent.mono`: a larger exponent gives a weaker statement.
* `TauCeti.abcConjectureWithExponent_iff_nat`: for `κ ≥ 0`, the abc conjecture with exponent `κ` is
  its form for coprime positive integers, of which `TauCeti.abcConjecture_iff_nat` is the case
  `κ = 1`.

## References

* D. W. Masser, *Open problems*, in *Proceedings of the Symposium on Analytic Number Theory*
  (W. W. L. Chen, ed.), Imperial College, London, 1985.
* J. Oesterlé, *Nouvelles approches du « théorème » de Fermat*, Séminaire Bourbaki, exposé 694
  (1988), Astérisque 161–162, 165–186.
* The `formal-conjectures` project, `FormalConjectures/Wikipedia/ABC.lean`, theorem `ABC.abc`
  (`github.com/google-deepmind/formal-conjectures` @ `817d8a74`, Apache-2.0).
-/

public section

open UniqueFactorizationMonoid

namespace TauCeti

/-- **The abc conjecture with exponent `κ`**: for every `ε > 0` there is a constant `C` such that
`max(|a|, |b|, |c|) ≤ C · rad(a b c) ^ (κ + ε)` for all coprime integers `a` and `b` with
`a + b = c`. The radical is taken in `ℕ`, of `|a b c|`. The abc conjecture is the case `κ = 1`
(`TauCeti.AbcConjecture`), and the statement becomes weaker as
`κ` grows (`TauCeti.AbcConjectureWithExponent.mono`). -/
def AbcConjectureWithExponent (κ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℤ, IsCoprime a b → a + b = c →
    ((max (max a.natAbs b.natAbs) c.natAbs : ℕ) : ℝ) ≤
      C * ((radical (a * b * c).natAbs : ℕ) : ℝ) ^ (κ + ε)

/-- The abc conjecture with exponent `κ`, unfolded. -/
theorem abcConjectureWithExponent_iff (κ : ℝ) : AbcConjectureWithExponent κ ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℤ, IsCoprime a b → a + b = c →
      ((max (max a.natAbs b.natAbs) c.natAbs : ℕ) : ℝ) ≤
        C * ((radical (a * b * c).natAbs : ℕ) : ℝ) ^ (κ + ε) :=
  Iff.rfl

/-- **The abc conjecture** (Masser, Oesterlé): for every `ε > 0` there is a constant `C` such that
`max(|a|, |b|, |c|) ≤ C · rad(a b c) ^ (1 + ε)` for all coprime integers `a` and `b` with
`a + b = c`. It is the abc conjecture with exponent `1`. -/
def AbcConjecture : Prop :=
  AbcConjectureWithExponent 1

/-- The abc conjecture, unfolded. -/
theorem abcConjecture_iff : AbcConjecture ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℤ, IsCoprime a b → a + b = c →
      ((max (max a.natAbs b.natAbs) c.natAbs : ℕ) : ℝ) ≤
        C * ((radical (a * b * c).natAbs : ℕ) : ℝ) ^ (1 + ε) :=
  Iff.rfl

-- The radical of a natural number is at least `1`, and so is any nonnegative power of it.
private theorem one_le_radical_rpow (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    1 ≤ ((radical n : ℕ) : ℝ) ^ r :=
  Real.one_le_rpow (by exact_mod_cast Nat.radical_pos n) hr

/-- **The abc conjecture with a larger exponent is weaker**: a bound with exponent `κ + ε` gives
one with exponent `κ' + ε` for every `κ' ≥ κ`, since the radical is at least `1`. -/
theorem AbcConjectureWithExponent.mono {κ κ' : ℝ} (h : AbcConjectureWithExponent κ)
    (hκ : κ ≤ κ') : AbcConjectureWithExponent κ' := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨max C 0, fun a b c hab habc ↦ (hC a b c hab habc).trans ?_⟩
  have hR : (1 : ℝ) ≤ ((radical (a * b * c).natAbs : ℕ) : ℝ) := by
    exact_mod_cast Nat.radical_pos _
  calc C * ((radical (a * b * c).natAbs : ℕ) : ℝ) ^ (κ + ε)
      ≤ max C 0 * ((radical (a * b * c).natAbs : ℕ) : ℝ) ^ (κ + ε) :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * ((radical (a * b * c).natAbs : ℕ) : ℝ) ^ (κ' + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR (by linarith))
          (le_max_right C 0)

/-- **The abc conjecture with exponent `κ ≥ 0` for positive integers**: it is equivalent to ask, for
every `ε > 0`, for a constant `C` with `c ≤ C · rad(a b c) ^ (κ + ε)` for all coprime positive
integers `a` and `b` with `a + b = c`. -/
theorem abcConjectureWithExponent_iff_nat (κ : ℝ) (hκ : 0 ≤ κ) : AbcConjectureWithExponent κ ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → a.Coprime b → a + b = c →
      (c : ℝ) ≤ C * ((radical (a * b * c) : ℕ) : ℝ) ^ (κ + ε) := by
  refine forall₂_congr fun ε hε ↦ ⟨fun ⟨C, hC⟩ ↦ ⟨C, fun a b c _ _ hab habc ↦ ?_⟩,
    fun ⟨C, hC⟩ ↦ ⟨max C 1, fun a b c hab habc ↦ ?_⟩⟩
  · -- a triple of natural numbers is a triple of integers, whose largest entry is `c`
    have h := hC a b c (Nat.Coprime.isCoprime hab) (by exact_mod_cast habc)
    rwa [← Nat.cast_mul, ← Nat.cast_mul, Int.natAbs_natCast, Int.natAbs_natCast,
      Int.natAbs_natCast, show max (max a b) c = c by omega] at h
  · have hxy : a.natAbs.Coprime b.natAbs := Int.isCoprime_iff_nat_coprime.mp hab
    have hR := one_le_radical_rpow (a.natAbs * b.natAbs * c.natAbs) (by linarith : 0 ≤ κ + ε)
    have hR₀ : 0 ≤ ((radical (a.natAbs * b.natAbs * c.natAbs) : ℕ) : ℝ) ^ (κ + ε) :=
      zero_le_one.trans hR
    rw [Int.natAbs_mul, Int.natAbs_mul]
    by_cases h₀ : a.natAbs = 0 ∨ b.natAbs = 0 ∨ c.natAbs = 0
    · -- if one entry vanishes, the other two are `±1`
      have hle : max (max a.natAbs b.natAbs) c.natAbs ≤ 1 := by
        rcases h₀ with h | h | h
        · rw [h, Nat.coprime_zero_left] at hxy
          omega
        · rw [h, Nat.coprime_zero_right] at hxy
          omega
        · rw [show b.natAbs = a.natAbs by omega, Nat.coprime_self] at hxy
          omega
      exact (Nat.cast_le_one.mpr hle).trans (one_le_mul_of_one_le_of_one_le (le_max_right _ _) hR)
    -- otherwise the triple of absolute values is a positive triple `x + y = z` in some order
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left C 1) hR₀)
    rcases (by omega : a.natAbs + b.natAbs = c.natAbs ∨ a.natAbs + c.natAbs = b.natAbs ∨
        b.natAbs + c.natAbs = a.natAbs) with h | h | h
    · rw [show max (max a.natAbs b.natAbs) c.natAbs = c.natAbs by omega]
      exact hC _ _ _ (by omega) (by omega) hxy h
    · rw [← h, add_comm, Nat.coprime_add_self_right] at hxy
      rw [show max (max a.natAbs b.natAbs) c.natAbs = b.natAbs by omega,
        mul_right_comm]
      exact hC _ _ _ (by omega) (by omega) hxy h
    · rw [Nat.coprime_comm, ← h, add_comm, Nat.coprime_add_self_right] at hxy
      rw [show max (max a.natAbs b.natAbs) c.natAbs = a.natAbs by omega,
        show a.natAbs * b.natAbs * c.natAbs = b.natAbs * c.natAbs * a.natAbs by ring]
      exact hC _ _ _ (by omega) (by omega) hxy h

/-- **The abc conjecture for positive integers**: it is equivalent to ask, for every `ε > 0`, for
a constant `C` with `c ≤ C · rad(a b c) ^ (1 + ε)` for all coprime positive integers `a` and `b`
with `a + b = c`. -/
theorem abcConjecture_iff_nat : AbcConjecture ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → a.Coprime b → a + b = c →
      (c : ℝ) ≤ C * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε) :=
  abcConjectureWithExponent_iff_nat 1 zero_le_one

/-- **The abc conjecture as finitely many exceptions**, the form of `ABC.abc` in the
`formal-conjectures` project: it is equivalent to ask that, for every `ε > 0`, only finitely many
triples of pairwise coprime positive integers `a + b = c` have `rad(a b c) ^ (1 + ε) < c`. -/
theorem abcConjecture_iff_forall_finite : AbcConjecture ↔
    ∀ ε : ℝ, 0 < ε → {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧ a + b = c ∧
      ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε) < c}.Finite := by
  -- if `0 < b` and `a + b = c`, the entries are pairwise coprime exactly when `a` and `b` are
  have hpair {a b c : ℕ} (hb : 0 < b) (habc : a + b = c) :
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ↔ a.Coprime b := by
    subst habc
    simp only [Set.pairwise_insert_of_symm, Set.pairwise_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, true_and,
      Nat.coprime_self_add_right, Nat.coprime_add_self_right]
    refine ⟨fun ⟨_, hab, hac⟩ ↦ ?_, fun h ↦ ⟨fun _ ↦ h.symm, fun _ ↦ h, fun _ ↦ h⟩⟩
    by_cases h : a = b
    · exact hac (by omega)
    · exact hab h
  rw [abcConjecture_iff_nat]
  refine ⟨fun H ε hε ↦ ?_, fun H ε hε ↦ ?_⟩
  · -- a constant `C` at the exponent `1 + ε / 2` bounds `c` on the exceptions at `1 + ε`
    obtain ⟨C, hC⟩ := H (ε / 2) (by positivity)
    set B := C * (C ^ (ε / 2)⁻¹) ^ (1 + ε / 2)
    refine ((Set.finite_Iic ⌈B⌉₊).prod ((Set.finite_Iic ⌈B⌉₊).prod
      (Set.finite_Iic ⌈B⌉₊))).subset ?_
    rintro ⟨a, b, c⟩ ⟨ha, hb, -, hp, habc, hlt⟩
    set r : ℝ := ((radical (a * b * c) : ℕ) : ℝ)
    have hr : 0 < r := Nat.cast_pos.mpr (Nat.radical_pos _)
    have hle := hC a b c ha hb ((hpair hb habc).mp hp) habc
    -- `r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2)`, so `r ^ (ε / 2) < C`
    rw [show 1 + ε = 1 + ε / 2 + ε / 2 by ring, Real.rpow_add hr] at hlt
    have hrC : r ^ (ε / 2) < C :=
      lt_of_mul_lt_mul_left (by linarith) (Real.rpow_nonneg hr.le (1 + ε / 2))
    -- hence `r < C ^ (ε / 2)⁻¹`, and `c ≤ C * r ^ (1 + ε / 2) ≤ B`
    have hrB : r < C ^ (ε / 2)⁻¹ := by
      simpa only [Real.rpow_rpow_inv hr.le (by positivity : ε / 2 ≠ 0)] using
        Real.rpow_lt_rpow (z := (ε / 2)⁻¹) (Real.rpow_nonneg hr.le _) hrC (by positivity)
    have hcB : (c : ℝ) ≤ B := hle.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hr.le hrB.le (by positivity))
      ((Real.rpow_nonneg hr.le _).trans hrC.le))
    have hc : c ≤ ⌈B⌉₊ := by exact_mod_cast hcB.trans (Nat.le_ceil B)
    simp only [Set.mem_prod, Set.mem_Iic]
    omega
  · -- the largest `c` among the finitely many exceptions is a constant
    obtain ⟨M, hM⟩ := ((H ε hε).image fun t : ℕ × ℕ × ℕ ↦ (t.2.2 : ℝ)).bddAbove
    refine ⟨max M 1, fun a b c ha hb hab habc ↦ ?_⟩
    have hR := one_le_radical_rpow (a * b * c) (by linarith : (0 : ℝ) ≤ 1 + ε)
    by_cases hlt : ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε) < c
    · have hcM : (c : ℝ) ≤ M :=
        hM ⟨(a, b, c), ⟨ha, hb, by omega, (hpair hb habc).mpr hab, habc, hlt⟩, rfl⟩
      exact (hcM.trans (le_max_left M 1)).trans
        (le_mul_of_one_le_right (zero_le_one.trans (le_max_right M 1)) hR)
    · exact (not_lt.mp hlt).trans (le_mul_of_one_le_left (zero_le_one.trans hR) (le_max_right M 1))

end TauCeti

end
