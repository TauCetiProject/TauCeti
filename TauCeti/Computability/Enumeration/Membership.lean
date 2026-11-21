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

For a family `A : ι → Finset ℕ` indexed by a primitive-codable type `ι` whose binary finite-set
codes `∑ x ∈ A i, 2 ^ x` are computable (or oracle-computable), membership `x ∈ A i` is uniformly
computable (or oracle-computable) in `(i, x)`.

## Main results

* `TauCeti.Enumeration.computableIn_mem_of_computableIn_equivBitIndices`: membership in finite
  sets with oracle-computable binary codes is oracle-computable.
* `TauCeti.Enumeration.computablePred_mem_of_computable_equivBitIndices`: ordinary computable
  specialization at the empty oracle.
-/

public section

namespace TauCeti.Enumeration

/-- Membership in finite sets is oracle-computable, uniformly in the index and the element,
when their binary finite-set codes are oracle-computable. -/
theorem computableIn_mem_of_computableIn_equivBitIndices {ι : Type*} [Primcodable ι]
    {G : Set (ℕ →. ℕ)} {A : ι → Finset ℕ}
    (hA : ComputableIn G fun i => Finset.equivBitIndices.symm (A i)) :
    ComputableIn G fun p : ι × ℕ => decide (p.2 ∈ A p.1) :=
  RecursiveIn.of_eq
    (Primrec.mem_equivBitIndices.decide.computableIn.comp
      ((hA.comp ComputableIn.fst).pair ComputableIn.snd)) fun p => by simp

/-- Membership in finite sets is computable, uniformly in the index and the number, when their
binary finite-set codes are computable. -/
theorem computablePred_mem_of_computable_equivBitIndices {ι : Type*} [Primcodable ι]
    {A : ι → Finset ℕ} (hA : Computable fun i => Finset.equivBitIndices.symm (A i)) :
    ComputablePred fun p : ι × ℕ => p.2 ∈ A p.1 :=
  (TauCeti.computableIn_empty_iff.1
    (computableIn_mem_of_computableIn_equivBitIndices hA.computableIn)).computablePred.of_eq
    fun p => by simp

end TauCeti.Enumeration
