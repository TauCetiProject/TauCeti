/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Criterion
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters

/-!
# Nonvanishing from congruent prime remainder bounds

`DirichletCharacter.LFunction_ne_zero_of_congruent_prime_remainder_bound` uses the
signed-remainder criterion once a prime with zero-free Legendre twists has been selected
in the residue class. The prime may depend on the box, since the remainder bound holds
for every prime in the class.

`DirichletCharacter.LFunction_ne_zero_of_parameter_prime_remainder_bounds` applies this
criterion at level `18480 * N` and descends to level `N` via
`DirichletCharacter.LFunction_changeLevel`.

The reductions follow `New.LFunction_ne_zero_of_primeRemainder_le` and `New.grh` in
`grh/src/New/Reduction/Zeros/Criterion.lean` and `grh/src/New/Reduction/OneSidedBound.lean`
of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC),
revision `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Filter TauCeti.OneSidedBound

namespace DirichletCharacter

/-- The signed remainder bound for the primes in a reduced class gives nonvanishing
at `ρ` if that class contains an odd prime whose Legendre twists are zero-free in
`β < Re z < 1` and `|Im z| ≤ |Im ρ|`. -/
theorem LFunction_ne_zero_of_congruent_prime_remainder_bound {q a : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {β : ℝ} {ρ : ℂ} (hβ : 0 ≤ β) (hρ : β < ρ.re)
    (hreg : ρ ≠ 1 ∨ χ ≠ 1) (hc : a.Coprime q)
    (hR : ∀ (d : ℕ) [Fact d.Prime], d ≡ a [MOD q] →
      ∀ᶠ y : ℝ in atTop, primeRemainder d q y ≤ y ^ (β - 1))
    (hselect : ∃ (d : ℕ) (hd : d.Prime), d ≠ 2 ∧ d ≡ a [MOD q] ∧
      ∀ (ψ : DirichletCharacter ℂ q) (z : ℂ), β < z.re → z.re < 1 → |z.im| ≤ |ρ.im| →
        @LFunction (q * d) ⟨Nat.mul_ne_zero (NeZero.ne q) hd.ne_zero⟩
          (@legendreTwist q ψ d ⟨hd⟩) z ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  obtain ⟨d, hd, hd₂, hda, htwist⟩ := hselect
  let : Fact d.Prime := ⟨hd⟩
  have hqd : q.Coprime d := Nat.Coprime.symm (hda.gcd_eq.trans hc)
  exact TauCeti.OneSidedBound.LFunction_ne_zero_of_primeRemainder_le
    hd₂ hqd χ hβ hρ hreg (hR d hda) htwist

/-- Bounds with arbitrary positive exponent loss over the designated class at level
`18480 * N` give nonvanishing right of `1/2` at level `N`. The required prime-selection
input concerns the Legendre twists of characters at the enlarged level. -/
theorem LFunction_ne_zero_of_parameter_prime_remainder_bounds {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hreg : ρ ≠ 1 ∨ χ ≠ 1)
    (hR : ∀ (d : ℕ) [Fact d.Prime], d ≡ 18480 * N / 2 - 1 [MOD 18480 * N] →
      ∀ ε > (0 : ℝ), ∀ᶠ y : ℝ in atTop, primeRemainder d (18480 * N) y ≤ y ^ (-1 / 2 + ε))
    (hselect : ∀ {β : ℝ}, 1 / 2 < β → β < ρ.re → ∃ (d : ℕ) (hd : d.Prime),
      d ≡ 18480 * N / 2 - 1 [MOD 18480 * N] ∧
      ∀ (ψ : DirichletCharacter ℂ (18480 * N)) (z : ℂ), β < z.re → z.re < 1 → |z.im| ≤ |ρ.im| →
        @LFunction (18480 * N * d)
          ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (by decide) (NeZero.ne N)) hd.ne_zero⟩
          (@legendreTwist (18480 * N) ψ d ⟨hd⟩) z ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  obtain ⟨β, hβ, hβρ⟩ := exists_between hρ
  let q := 18480 * N
  have hq : q ≠ 0 := Nat.mul_ne_zero (by decide) (NeZero.ne N)
  let : NeZero q := ⟨hq⟩
  have hdiv : N ∣ q := dvd_mul_left _ _
  have h18480 : 18480 ∣ q := dvd_mul_right _ _
  obtain ⟨d, hd, hda, htwist⟩ := hselect hβ hβρ
  have h8 : 8 ∣ q := (by decide : 8 ∣ 18480).trans h18480
  have hd7 : d % 8 = 7 := (hda.of_dvd h8).trans (div_two_sub_one_modEq_seven hq h18480)
  have hreg' : ρ ≠ 1 ∨ χ.changeLevel hdiv ≠ 1 :=
    hreg.imp_right fun hχ ↦ hχ ∘ (changeLevel_eq_one_iff hdiv).mp
  have hrpow : -1 / 2 + (β - 1 / 2) = β - 1 := by ring
  have hR' (d : ℕ) [Fact d.Prime] (hd : d ≡ q / 2 - 1 [MOD q]) :
      ∀ᶠ y : ℝ in atTop, primeRemainder d q y ≤ y ^ (β - 1) := by
    rw [← hrpow]
    exact hR d hd (β - 1 / 2) (sub_pos.mpr hβ)
  have hnonzero := (χ.changeLevel hdiv).LFunction_ne_zero_of_congruent_prime_remainder_bound
    (by linarith) hβρ hreg' (coprime_div_two_sub_one_of_dvd hq h18480) hR'
    ⟨d, hd, by omega, hda, htwist⟩
  rw [LFunction_changeLevel hdiv χ hreg.symm] at hnonzero
  exact left_ne_zero_of_mul hnonzero

end DirichletCharacter
