/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Reduction
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
public import TauCeti.NumberTheory.LSeries.Quadratic.TwistSelection
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Criterion
import TauCeti.NumberTheory.LSeries.Quadratic.LegendreTwistSelection

/-!
# The one-sided prime-sum criterion in a residue class

A power saving for the number of bad quadratic twists lets us choose the twisting prime for
Landau's criterion *after* fixing the height at which we want nonvanishing. For a fixed
exponent, the remainder bound can have a separate starting point for each prime. The
reduction to parameter moduli then gives a criterion for every level.

The selection argument and the choice of residue classes follow
`New.LFunction_ne_zero_of_primeRemainder_le` and `New.grh` in [lsernau/grh-lean][short-proof],
in `New/Reduction/Zeros/Criterion.lean` and `New/Reduction/OneSidedBound.lean`, respectively.

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src
-/

public section

open Asymptotics DirichletCharacter Filter

namespace TauCeti.OneSidedBound

/-- A one-sided prime-remainder bound for the odd primes in a reduced class excludes zeros
at `ρ`, if the count of bad quadratic twists in that class has a power saving at height
`|Im ρ|`. The threshold in the remainder bound can depend on the prime. -/
theorem LFunction_ne_zero_of_primeRemainder_le_of_density {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (χ : DirichletCharacter ℂ q) {β : ℝ} {ρ : ℂ} (hβ : 0 ≤ β)
    (hρ : β < ρ.re) (hreg : ρ ≠ 1 ∨ χ ≠ 1)
    (hcount : ∃ B < (1 : ℝ), (fun x : ℝ ↦
      ({d ∈ quadraticTwistBadPrimes a β |ρ.im| | (d : ℝ) ≤ x}.ncard : ℝ)) =O[atTop] (· ^ B))
    (hR : ∀ {d : ℕ} [Fact d.Prime], (d : ZMod q) = a → Odd d →
      ∀ᶠ y : ℝ in atTop, primeRemainder d q y ≤ y ^ (β - 1)) :
    χ.LFunction ρ ≠ 0 := by
  obtain ⟨B, hB, hcount⟩ := hcount
  obtain ⟨d, hd₂, hd, hda, hodd, hfree⟩ :=
    exists_prime_entireLFunction_legendreTwist_ne_zero_of_density ha hB hcount 2
  let : Fact d.Prime := ⟨hd⟩
  have hqd : q.Coprime d := ((ZMod.isUnit_iff_coprime d q).mp (hda ▸ ha)).symm
  refine LFunction_ne_zero_of_primeRemainder_le hd₂.ne' hqd χ hβ hρ hreg (hR hda hodd) ?_
  intro ψ z hz _ him
  simpa only [entireLFunction_legendreTwist ψ d hd₂.ne' hqd] using hfree ψ z hz.le him

/-- To exclude zeros right of the critical line at all levels, it suffices to bound the
signed remainders for all admissible parameters, and to have a power saving in bad-twist
counts for their reduced classes at each threshold `β > 1/2` and height `H`. -/
theorem forall_zeroFreeRightOf_LFunction_of_primeRemainder_le_of_density
    (hcount : ∀ (q : ℕ) [NeZero q], 18480 ∣ q → ∀ β H : ℝ, 1 / 2 < β →
      ∃ B < (1 : ℝ), (fun x : ℝ ↦ ({d ∈ quadraticTwistBadPrimes ((q / 2 - 1 : ℕ) : ZMod q) β H |
        (d : ℝ) ≤ x}.ncard : ℝ)) =O[atTop] (· ^ B))
    (hR : ∀ (P : Parameters) (ε : ℝ), 0 < ε →
      ∀ᶠ y : ℝ in atTop, primeRemainder P.d P.q₀ y ≤ y ^ (-(1 / 2) + ε)) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), ZeroFreeRightOf (1 / 2) χ.LFunction := by
  apply forall_zeroFreeRightOf_LFunction_iff_forall_parameters.mpr
  intro P β hβ χ ρ hρ hreg
  have ha : IsUnit ((P.q₀ / 2 - 1 : ℕ) : ZMod P.q₀) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (coprime_div_two_sub_one_of_dvd P.q₀_ne_zero P.dvd_q₀)
  refine LFunction_ne_zero_of_primeRemainder_le_of_density ha χ (by linarith) hρ (.inl hreg)
    (hcount P.q₀ P.dvd_q₀ β |ρ.im| hβ) ?_
  intro d hd hda _
  let P' := Parameters.ofModEq P.dvd_q₀ hd.out ((ZMod.natCast_eq_natCast_iff _ _ _).mp hda)
  have hε : 0 < β - 1 / 2 := sub_pos.mpr hβ
  have hexp : -(1 / 2 : ℝ) + (β - 1 / 2) = β - 1 := by ring
  simpa only [P', Parameters.ofModEq_d, Parameters.ofModEq_q₀, hexp] using
    hR P' (β - 1 / 2) hε

end TauCeti.OneSidedBound
