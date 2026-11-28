/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.CompensatedRiesz
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist

/-!
# The prime remainder's quotient as a signed Riesz sum

The continued transform of the signed prime remainder can be written using a single
mean of logarithmic derivatives, or as a signed sum of the individual character transforms.
The second form gives access to the poles and residues at zeros of the character L-functions.
We identify the two forms on the half-plane of absolute convergence, retaining the correction
from the principal character in the untwisted sum.

The normalization is that of `New.integral_primeRemainder` in `New/Reduction/Zeros/PrimeError.lean`
in lsernau/grh-lean (`72fead1`).
-/

public section

open ArithmeticFunction.vonMangoldt DirichletCharacter Finset

namespace TauCeti.OneSidedBound

/-- At an odd prime `d` coprime to the base modulus `q`, the compensated difference
quotient of `logDerivMean` is the average of the untwisted Riesz expressions minus their
Legendre-twisted counterparts on `Re s > 1`. -/
theorem sum_sub_rieszRemainderMellin_eq_logDerivMean {d q : ℕ} [Fact d.Prime] [NeZero q]
    (hd : d ≠ 2) (hq : q.Coprime d) {s : ℂ} (hs : 1 < s.re) :
    letI : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
    (∑ χ : DirichletCharacter ℂ q, (rieszRemainderMellin χ.LFunction s -
      rieszRemainderMellin (quadraticTwist d χ).LFunction s)) / (q.totient : ℂ) =
      (logDerivMean d q s / s - logDerivMean d q 1) / (s - 1) := by
  classical
  have : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  have htwist (χ : DirichletCharacter ℂ q) : quadraticTwist d χ ≠ 1 := by
    suffices quadraticTwist d χ = χ.legendreTwist d by
      rw [this]
      exact χ.legendreTwist_ne_one d hd hq
    refine MulChar.ext fun a ↦ ?_
    rw [quadraticTwist_apply, ← ZMod.intCast_zmod_cast (a : ZMod (q * d)), legendreTwist_apply]
    simp [legendreSym]
  have hmean (z : ℂ) : logDerivMean d q z = LFunctionResidueClassAux (1 : ZMod q) z +
      (∑ χ : DirichletCharacter ℂ q, logDeriv (quadraticTwist d χ).LFunction z) /
        (q.totient : ℂ) - (q.totient : ℂ)⁻¹ := by
    have hsum : (∑ χ : DirichletCharacter ℂ q, logDeriv χ.entireLFunction z) =
        logDeriv (LFunctionTrivChar₁ q) z +
          ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), logDeriv χ.LFunction z := by
      rw [← sum_compl_add_sum ({1} : Finset (DirichletCharacter ℂ q)), sum_singleton,
        entireLFunction_one, add_comm]
      exact congrArg (_ + ·) <| sum_congr rfl fun χ hχ ↦ by
        rw [entireLFunction_of_ne_one (by simpa using hχ)]
    simp only [logDerivMean_def, entireLFunction_of_ne_one (htwist _), sum_sub_distrib, hsum]
    simp only [LFunctionResidueClassAux, ZMod.inv_one, MulChar.map_one, one_mul, logDeriv_apply,
      div_eq_mul_inv]
    ring
  simpa only [hmean] using sum_sub_rieszRemainderMellin_eq_compensated_mean
    (quadraticTwist d) htwist hs

end TauCeti.OneSidedBound
