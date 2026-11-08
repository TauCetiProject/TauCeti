/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.NumberTheory.Padics.RingHoms

import TauCeti.NumberTheory.Cyclotomic.Surjectivity
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.Cyclotomic.Irreducible
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Surjectivity of a local cyclotomic character

This file gives a criterion for the local `p`-adic cyclotomic character to be surjective: every
`p`-power cyclotomic polynomial must be irreducible over the base field. Since the cyclotomic
polynomials `Φ_{p^n}` are irreducible over `ℚ_p`, the cyclotomic character of `G_{ℚ_p}` is onto
`ℤ_pˣ`, and so is each of its reductions onto `(ℤ/p^n)ˣ`. This is the ambient image against which
the cyclotomic image of a finite extension of `ℚ_p` is measured. Over a proper extension of `ℚ_p`
the character need not be surjective: over `ℚ₂(i)` its image is `1 + 4ℤ₂`.

## Main results

* `TauCeti.localCyclotomicCharacter_surjective_of_irreducible`: the cyclotomic character is
  surjective when every `Φ_{p^n}` is irreducible over the base field.
* `TauCeti.surjective_localCyclotomicCharacter_ratPadic`,
  `TauCeti.range_localCyclotomicCharacter_ratPadic`: the cyclotomic character of `G_{ℚ_p}` is
  surjective.
* `TauCeti.surjective_toZModPow_localCyclotomicCharacter_ratPadic`: its reduction modulo `p^n` is
  onto `(ℤ/p^n)ˣ`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §4.
-/

public section

open Polynomial

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharZero K]

/-- The local `p`-adic cyclotomic character is surjective if all `p`-power cyclotomic
polynomials are irreducible over the base field. -/
theorem localCyclotomicCharacter_surjective_of_irreducible
    (hirr : ∀ n : ℕ, Irreducible (cyclotomic (p ^ n) K)) :
    Function.Surjective (localCyclotomicCharacter p K) := by
  intro u
  let t : ℕ → Set (Field.absoluteGaloisGroup K) := fun n ↦
    {σ | PadicInt.toZModPow n (localCyclotomicCharacter p K σ : ℤ_[p]) =
      PadicInt.toZModPow n (u : ℤ_[p])}
  have htclosed (n : ℕ) : IsClosed (t n) := by
    exact isClosed_eq
      ((PadicInt.continuous_toZModPow n).comp
        (Units.continuous_val.comp (localCyclotomicCharacter_continuous p K)))
      continuous_const
  have htnonempty (n : ℕ) : (t n).Nonempty := by
    obtain ⟨σ, hσ⟩ := modularCyclotomicCharacter_surjective_of_irreducible (K := K)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure K) (p ^ n))
      (hirr n) (Units.map (PadicInt.toZModPow n).toMonoidHom u)
    let g : Field.absoluteGaloisGroup K := σ
    refine ⟨g, ?_⟩
    dsimp only [t]
    rw [Set.mem_ofPred_eq, localCyclotomicCharacter_apply, cyclotomicCharacter.toZModPow]
    exact congrArg Units.val hσ
  have htmono (n : ℕ) : t (n + 1) ⊆ t n := by
    intro σ hσ
    dsimp [t] at hσ ⊢
    rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n), hσ,
      PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n)]
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    t htmono htnonempty (htclosed 0).isCompact htclosed
  refine ⟨σ, Units.ext (PadicInt.ext_of_toZModPow.mp fun n ↦ ?_)⟩
  exact Set.mem_iInter.mp hσ n

section RatPadic

variable (p)

/-- **The cyclotomic character of `G_{ℚ_p}` is surjective**, because every cyclotomic polynomial
`Φ_{p^n}` is irreducible over `ℚ_p`. -/
theorem surjective_localCyclotomicCharacter_ratPadic :
    Function.Surjective (localCyclotomicCharacter p ℚ_[p]) :=
  localCyclotomicCharacter_surjective_of_irreducible (irreducible_cyclotomic_prime_pow_ratPadic p)

/-- The image of the cyclotomic character of `G_{ℚ_p}` is all of `ℤ_pˣ`. -/
@[simp]
theorem range_localCyclotomicCharacter_ratPadic : (localCyclotomicCharacter p ℚ_[p]).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (surjective_localCyclotomicCharacter_ratPadic p)

/-- **The cyclotomic character of `G_{ℚ_p}` modulo `p^n` is onto `(ℤ/p^n)ˣ`.** That is, every
automorphism of the `p^n`-th roots of unity, `ζ ↦ ζ^a` with `a` prime to `p`, is induced by an
element of `G_{ℚ_p}`. -/
theorem surjective_toZModPow_localCyclotomicCharacter_ratPadic (n : ℕ) :
    Function.Surjective (PadicInt.unitsToZModPow n ∘ localCyclotomicCharacter p ℚ_[p]) :=
  (PadicInt.unitsToZModPow_surjective n).comp (surjective_localCyclotomicCharacter_ratPadic p)

end RatPadic

end TauCeti
