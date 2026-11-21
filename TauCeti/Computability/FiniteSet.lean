/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Computability.RE
public import TauCeti.Computability.RecursiveIn
import TauCeti.Computability.Primrec.FiniteSet

/-!
# Computability of binary-coded finite-set membership

For a sequence `A : ℕ → Finset ℕ` whose binary finite-set codes `∑ x ∈ A s, 2 ^ x` are computable
(or oracle-computable), membership `x ∈ A s` is uniformly computable (or oracle-computable) in
`(s, x)`.

## Main results

* `TauCeti.Enumeration.computableIn_mem_of_computableIn_equivBitIndices`: membership in finite
  stages with oracle-computable binary codes is oracle-computable.
* `TauCeti.Enumeration.computablePred_mem_of_computable_equivBitIndices`: ordinary computable
  specialization at the empty oracle.
-/

public section

namespace TauCeti.Enumeration

/-- Membership in finite stages is oracle-computable, uniformly in the stage and the element,
when their binary finite-set codes are oracle-computable. -/
theorem computableIn_mem_of_computableIn_equivBitIndices {G : Set (ℕ →. ℕ)}
    {A : ℕ → Finset ℕ}
    (hA : ComputableIn G fun s => Finset.equivBitIndices.symm (A s)) :
    ComputableIn G fun p : ℕ × ℕ => decide (p.2 ∈ A p.1) :=
  RecursiveIn.of_eq
    (Primrec.mem_equivBitIndices.decide.computableIn.comp
      ((hA.comp ComputableIn.fst).pair ComputableIn.snd)) fun p => by simp

/-- Membership in finite stages is computable, uniformly in the stage and the number, when their
binary finite-set codes are computable. -/
theorem computablePred_mem_of_computable_equivBitIndices {A : ℕ → Finset ℕ}
    (hA : Computable fun s => Finset.equivBitIndices.symm (A s)) :
    ComputablePred fun p : ℕ × ℕ => p.2 ∈ A p.1 :=
  (TauCeti.computableIn_empty_iff.1
    (computableIn_mem_of_computableIn_equivBitIndices hA.computableIn)).computablePred.of_eq
    fun p => by simp

end TauCeti.Enumeration
