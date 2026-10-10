/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Solver
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.IntegerChecker

/-!
# Integer certificates in the cyclotomic Dixon solver

A certified integer character table can also be recovered by the cyclotomic Dixon solver.
Integer entries embed as constant power-basis vectors, so the balanced residue condition is
exactly the bound on the absolute values of the integral central-character entries. No bound
on the ordinary entries or separate choice of conjugate-row alignments is needed.

`TauCeti.ClassData.IsIntegerCharacterTableSpec.isSome_dixonCyclotomicCharacterTable` proves
success at any Dixon prime large enough for these central entries.
The existing prime-search API then transfers this criterion to the assembled algorithm.
The result uses the existing cyclotomic solver and preserves its exact-checker soundness
guarantees.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik **10**
  (1967), 446–450.
* G. J. A. Schneider, *Dixon's character table algorithm revisited*, Journal of Symbolic
  Computation **9** (1990), 601–606.
-/

public section

namespace TauCeti.ClassData.IsIntegerCharacterTableSpec

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {d : ClassData G}
variable {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ}
variable {degree : Fin d.numClasses → ℕ}

/-- The cyclotomic solver recovers a certified integer character table whenever each central
entry lies in the balanced residue window at the supplied Dixon prime. The conductor is the
group exponent, and the conclusion is independent of the prime data's chosen primitive root. -/
theorem isSome_dixonCyclotomicCharacterTable
    (h : d.IsIntegerCharacterTableSpec omega table degree)
    (e : ℕ) (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    (hbound : ∀ i j, 2 * (omega i j).natAbs < q.p) :
    (d.dixonCyclotomicCharacterTable? e q).isSome = true := by
  have : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  have hcast : d.IsCyclotomicCharacterTableSpec e
      (fun i j ↦ (omega i j : Cyclotomic e))
      (fun i j ↦ (table i j : Cyclotomic e)) degree :=
    h.map (Int.castRingHom (Cyclotomic e)) (fun z ↦ by simp)
  apply d.isSome_dixonCyclotomicCharacterTable_of_spec e he q _ _ degree hcast
  intro i j k
  rw [Cyclotomic.coeff_intCast]
  split_ifs
  · exact hbound i j
  · simpa using q.isGoodDixonPrime.prime.pos

end TauCeti.ClassData.IsIntegerCharacterTableSpec
