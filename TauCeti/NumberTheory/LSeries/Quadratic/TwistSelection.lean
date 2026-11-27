/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Set.Card
import TauCeti.NumberTheory.LSeries.PrimesInAP

/-!
# Selecting a prime with zero-free quadratic twists

For primes in a reduced residue class, a power saving in the count of those whose
quadratic twists have a zero in a prescribed box suffices to choose a prime for which
all the twists are zero-free there. This is the prime-selection step in
`New.exists_entireL_quadTwist_ne_zero` of `grh-lean`,
`grh/src/Lib/Analytic/QuadraticTwist.lean` (revision `72fead1`).
-/

public section

open Filter Asymptotics

namespace TauCeti

/-- The primes in the residue class `a` for which some character modulo `q`, twisted by the
Legendre character of that prime, has a zero with real part at least `β` and imaginary part of
absolute value at most `H`. The product uses the least common multiple of the two levels. -/
def quadraticTwistBadPrimes {q : ℕ} [NeZero q] (a : ZMod q) (β H : ℝ) : Set ℕ :=
  {d | (d : ZMod q) = a ∧ ∃ hd : d.Prime,
    letI : NeZero d := ⟨hd.ne_zero⟩
    letI : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) hd.ne_zero⟩
    ∃ (χ : DirichletCharacter ℂ q) (s : ℂ),
      β ≤ s.re ∧ |s.im| ≤ H ∧ (χ.mul (jacobiChar ℂ d)).LFunction s = 0}

/-- Membership is equivalent to being a prime in the class with a zero of one of the
quadratic twists in the box. The nonzero levels for the twist follow from primality. -/
@[simp]
theorem mem_quadraticTwistBadPrimes_iff {q d : ℕ} [NeZero q] {a : ZMod q} {β H : ℝ} :
    d ∈ quadraticTwistBadPrimes a β H ↔ (d : ZMod q) = a ∧ ∃ hd : d.Prime,
      letI : NeZero d := ⟨hd.ne_zero⟩
      letI : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) hd.ne_zero⟩
      ∃ (χ : DirichletCharacter ℂ q) (s : ℂ),
        β ≤ s.re ∧ |s.im| ≤ H ∧ (χ.mul (jacobiChar ℂ d)).LFunction s = 0 :=
  Iff.rfl

/-- A power saving in the number of primes with a twist zero yields a prime above any cutoff
for which every twist is zero-free in the box. -/
theorem exists_prime_quad_twist_zero_free_of_density {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) {β H B : ℝ} (hB : B < 1)
    (hcount : (fun x : ℝ ↦ ({d ∈ quadraticTwistBadPrimes a β H | (d : ℝ) ≤ x}.ncard : ℝ))
      =O[atTop] (· ^ B)) (N : ℕ) :
    ∃ d > N, ∃ hd : d.Prime, (d : ZMod q) = a ∧
      letI : NeZero d := ⟨hd.ne_zero⟩
      letI : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) hd.ne_zero⟩
      ∀ (χ : DirichletCharacter ℂ q) (s : ℂ),
        β ≤ s.re → |s.im| ≤ H → (χ.mul (jacobiChar ℂ d)).LFunction s ≠ 0 := by
  have hinf := Nat.infinite_setOf_prime_and_eq_mod_and_notMem_of_ncard_isBigO ha hB hcount
  obtain ⟨d, ⟨hd, hda, hgood⟩, hdN⟩ := Set.infinite_iff_exists_gt.mp hinf N
  refine ⟨d, hdN, hd, hda, fun χ s hs ht hzero ↦ hgood ?_⟩
  exact mem_quadraticTwistBadPrimes_iff.mpr ⟨hda, hd, χ, s, hs, ht, hzero⟩

end TauCeti
