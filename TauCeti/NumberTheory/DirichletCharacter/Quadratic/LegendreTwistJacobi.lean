/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
public import TauCeti.NumberTheory.LSeries.Quadratic.TwistSelection
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel

/-!
# Bridging Legendre twists and Jacobi-character products for prime selection

`DirichletCharacter.legendreTwist` forms the quadratic twist of a character `χ` modulo `q` by a
prime `d` at level `q * d`, whereas `TauCeti.exists_prime_quad_twist_zero_free_of_density` works
with the product `χ.mul (jacobiChar ℂ d)` at level `q.lcm d`. For `q ≠ 0` and a prime `d`, the
two moduli `q.lcm d` and `q * d` share the same prime factors, and `changeLevel` identifies
`χ.mul (jacobiChar ℂ d)` with `χ.legendreTwist d`. Hence their L-functions coincide (for all
`s : ℂ` when `d ≠ 2` and `q.Coprime d`), and a power-saving zero-density bound selects an odd
prime `d > N` in any reduced class modulo `q` whose `legendreTwist` L-functions and
`entireLFunction`s are zero-free in a prescribed box.

## Main results

* `DirichletCharacter.changeLevel_mul_jacobiChar_eq_legendreTwist`: raising the level of
  `χ.mul (jacobiChar ℂ d)` from `q.lcm d` to `q * d` yields `χ.legendreTwist d`.
* `DirichletCharacter.LFunction_legendreTwist_eq_LFunction_mul_jacobiChar`: the two twists have
  the same L-function at every `s : ℂ` when `d ≠ 2` and `q.Coprime d`.
* `TauCeti.exists_prime_legendreTwist_zero_free_of_density`: prime-selection theorem stated
  directly for `χ.legendreTwist d`, matching `TauCeti.OneSidedBound.Criterion`.

## Provenance

Adapted from `New.exists_entireL_quadTwist_ne_zero` in `grh/src/Lib/Analytic/QuadraticTwist.lean`
of `grh-lean` (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC) at
commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Filter Asymptotics

namespace DirichletCharacter

/-- Raising the level of `χ.mul (jacobiChar ℂ d)` from `q.lcm d` to `q * d` produces
`χ.legendreTwist d`. -/
theorem changeLevel_mul_jacobiChar_eq_legendreTwist {q d : ℕ} [NeZero q] [Fact d.Prime]
    (χ : DirichletCharacter ℂ q) :
    letI : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩
    letI : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
    letI : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
    (χ.mul (TauCeti.jacobiChar ℂ d)).changeLevel
      (Nat.lcm_dvd (dvd_mul_right q d) (dvd_mul_left d q)) = χ.legendreTwist d := by
  let : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩
  let : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  let : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  simp only [DirichletCharacter.mul, map_mul, ← changeLevel_trans, legendreTwist_def,
    TauCeti.jacobiChar_eq_ringHomComp_quadraticChar]

/-- For an odd prime `d` coprime to `q`, `χ.legendreTwist d` and `χ.mul (jacobiChar ℂ d)` have
the same L-function at every `s : ℂ`. -/
theorem LFunction_legendreTwist_eq_LFunction_mul_jacobiChar {q d : ℕ} [NeZero q] [Fact d.Prime]
    (χ : DirichletCharacter ℂ q) (hd : d ≠ 2) (hc : q.Coprime d) (s : ℂ) :
    letI : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩
    letI : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
    letI : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
    (χ.legendreTwist d).LFunction s = (χ.mul (TauCeti.jacobiChar ℂ d)).LFunction s := by
  let : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩
  let : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  let : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  have hdiv : q.lcm d ∣ q * d := Nat.lcm_dvd (dvd_mul_right q d) (dvd_mul_left d q)
  have hne : χ.mul (TauCeti.jacobiChar ℂ d) ≠ 1 := fun h1 ↦
    χ.legendreTwist_ne_one d hd hc (by
      rw [← χ.changeLevel_mul_jacobiChar_eq_legendreTwist, h1, changeLevel_one])
  have hpf : (q * d).primeFactors = (q.lcm d).primeFactors := by
    rw [hc.lcm_eq_mul]
  rw [← χ.changeLevel_mul_jacobiChar_eq_legendreTwist]
  exact LFunction_changeLevel_eq_of_primeFactors_eq _ hdiv hpf (.inl hne)

end DirichletCharacter

namespace TauCeti

/-- A power-saving zero-density bound on bad primes in a reduced residue class `a` modulo `q`
selects an odd prime `d > max N q` in that class (hence coprime to `q`) such that every
`χ.legendreTwist d` has nonvanishing `LFunction` and `entireLFunction` on `β ≤ Re s`,
`|Im s| ≤ H`. -/
theorem exists_prime_legendreTwist_zero_free_of_density {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) {β H B : ℝ} (hB : B < 1)
    (hcount : (fun x : ℝ ↦ ({d ∈ quadraticTwistBadPrimes a β H | (d : ℝ) ≤ x}.ncard : ℝ))
      =O[atTop] (· ^ B)) (N : ℕ) :
    ∃ d > N, ∃ hd : d.Prime, (d : ZMod q) = a ∧ d ≠ 2 ∧ q.Coprime d ∧
      letI : Fact d.Prime := ⟨hd⟩
      letI : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) hd.ne_zero⟩
      ∀ (χ : DirichletCharacter ℂ q) (s : ℂ),
        β ≤ s.re → |s.im| ≤ H →
          (χ.legendreTwist d).LFunction s ≠ 0 ∧ (χ.legendreTwist d).entireLFunction s ≠ 0 := by
  obtain ⟨d, hdgt, hd, hda, hfree⟩ :=
    exists_prime_quad_twist_zero_free_of_density ha hB hcount (max (max N q) 2)
  have hdN : d > N := lt_of_le_of_lt ((le_max_left N q).trans (le_max_left _ 2)) hdgt
  have hdq : q < d := lt_of_le_of_lt ((le_max_right N q).trans (le_max_left _ 2)) hdgt
  have hd2 : d ≠ 2 := ne_of_gt (lt_of_le_of_lt (le_max_right _ 2) hdgt)
  have hcop : q.Coprime d := (hd.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (NeZero.pos q) hdq)).symm
  let : Fact d.Prime := ⟨hd⟩
  let : NeZero d := ⟨hd.ne_zero⟩
  let : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) hd.ne_zero⟩
  let : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) hd.ne_zero⟩
  refine ⟨d, hdN, hd, hda, hd2, hcop, fun χ s hs ht ↦ ?_⟩
  have hL : (χ.legendreTwist d).LFunction s ≠ 0 := by
    rw [χ.LFunction_legendreTwist_eq_LFunction_mul_jacobiChar hd2 hcop]
    exact hfree χ s hs ht
  exact ⟨hL, by rwa [χ.entireLFunction_legendreTwist d hd2 hcop]⟩

end TauCeti
