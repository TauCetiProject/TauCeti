/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Perfectoid.FontaineTheta
import TauCeti.RingTheory.Perfectoid.Padic
import TauCeti.RingTheory.Perfectoid.Plus

/-!
# Checks for Frobenius on perfectoid plus rings

These checks use arbitrary rings of integral elements of `ℂ_p`, a product that is not a
field, and the zero ring. The Fontaine-map check supplies `p`-adic completeness directly
from the pseudouniformiser `p` of `ℂ_p`; it does not assume completeness as an extra input.
-/

open TauCeti.Huber TauCeti.Perfectoid

variable (p : ℕ) [Fact p.Prime]

-- Every plus ring, not just the maximal one, has surjective Frobenius modulo `p`.
example {S : Subring ℂ_[p]} (hS : IsRingOfIntegralElements S) :
    letI : Fact (¬ IsUnit (p : S)) := ⟨hS.not_isUnit_natCast⟩
    Function.Surjective (frobenius (ModP S p) p) := by
  have : Fact (¬ IsUnit (p : S)) := ⟨hS.not_isUnit_natCast⟩
  exact hS.surjective_frobenius_modP

-- A smaller parameter makes the quotient `p / ϖᵖ` topologically nilpotent in the plus ring.
example {S : Subring ℂ_[p]} (hS : IsRingOfIntegralElements S) :
    ∃ ϖ : S, IsPseudoUniformizer (ϖ : ℂ_[p]) ∧
      ∃ c : S, (p : S) = ϖ ^ p * c ∧ IsTopologicallyNilpotent (c : ℂ_[p]) :=
  hS.exists_pseudoUniformizer_natCast_eq_pow_mul

-- The same relative Frobenius works for any admissible pseudouniformiser of the plus ring.
example {S : Subring ℂ_[p]} (hS : IsRingOfIntegralElements S) (ϖ : S)
    (hϖ : IsPseudoUniformizer (ϖ : ℂ_[p])) (hdvd : ϖ ^ p ∣ (p : S)) :
    Function.Bijective (TauCeti.frobeniusModPow p hdvd) :=
  hS.bijective_frobeniusModPow hϖ hdvd

-- Roots modulo `ϖ p` have their error quotient in the actual plus ring.
example {S : Subring ℂ_[p]} (hS : IsRingOfIntegralElements S) (ϖ : S)
    (hϖ : IsPseudoUniformizer (ϖ : ℂ_[p])) (hdvd : ϖ ^ p ∣ (p : S)) (x : S) :
    ∃ y z : S, x - y ^ p = ϖ * p * z :=
  hS.exists_mul_natCast_dvd_sub_pow hϖ hdvd x

-- Feed the result straight into Mathlib's Fontaine surjectivity theorem.
example {S : Subring ℂ_[p]} (hS : IsRingOfIntegralElements S) :
    letI : Fact (¬ IsUnit (p : S)) := ⟨hS.not_isUnit_natCast⟩
    letI : IsAdicComplete (Ideal.span {(p : S)}) S := by
      have := IsPerfectoidTateRing.isUniform p (R := ℂ_[p])
      exact hS.isAdicComplete_span_singleton _
        (by simpa using isPseudoUniformizer_natCast_padicComplex p)
    Function.Surjective (WittVector.fontaineTheta S p) := by
  have : Fact (¬ IsUnit (p : S)) := ⟨hS.not_isUnit_natCast⟩
  have : IsAdicComplete (Ideal.span {(p : S)}) S := by
    have := IsPerfectoidTateRing.isUniform p (R := ℂ_[p])
    exact hS.isAdicComplete_span_singleton _
      (by simpa using isPseudoUniformizer_natCast_padicComplex p)
  exact surjective_fontaineTheta hS.surjective_frobenius_modP

-- No domain hypothesis is needed: the ambient product has nontrivial zero divisors.
example (x : powerBoundedSubring (ℂ_[p] × ℂ_[p])) :
    ∃ y : powerBoundedSubring (ℂ_[p] × ℂ_[p]),
      (p : powerBoundedSubring (ℂ_[p] × ℂ_[p])) ∣ x - y ^ p :=
  (isRingOfIntegralElements_powerBoundedSubring (ℂ_[p] × ℂ_[p])).exists_natCast_dvd_sub_pow x

-- The elementwise assertion includes zero rings, unlike Mathlib's characteristic-p Frobenius.
example {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R] [Subsingleton R]
    {S : Subring R} (hS : IsRingOfIntegralElements S) (x : S) :
    ∃ y : S, (p : S) ∣ x - y ^ p := by
  have := isPerfectoidTateRing_of_subsingleton p R
  exact hS.exists_natCast_dvd_sub_pow x
