/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Approximation.Instability
import TauCeti.Computability.RE
import TauCeti.Computability.RecursiveIn

/-!
# Computable approximations with a limit-computable modulus have c.e. degree

If a total function has a uniformly computable approximation and a modulus computable from
that function, it is Turing equivalent to a c.e. set. The set is the approximation's instability
set: whether a coordinate changes after a given stage. The limit is computable from this set
by stable-stage search, while a modulus bounds the finite search deciding instability.

This proves the approximation-to-c.e.-degree direction of Soare's criterion, III.3.4.

## Main results

* `TauCeti.Approximation.IsModulus.instabilitySet_turingReducible`: any oracle computing a modulus
  decides the instability set of a computable approximation.
* `TauCeti.Approximation.IsModulus.turingEquivalent_instabilitySet`: a modulus computable from the
  limit identifies the limit's degree with the c.e. instability set.
* `TauCeti.Approximation.IsModulus.exists_rePred_turingEquivalent`: the limit has a c.e. degree.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, III.3.4.
-/

public section

namespace TauCeti.Approximation

variable {f : ℕ → ℕ → ℕ} {g m : ℕ → ℕ}

/-- Every oracle computing a modulus decides the instability set of a computable approximation. -/
theorem IsModulus.instabilitySet_turingReducible {O : ℕ →. ℕ} (hm : IsModulus f g m)
    (hf : Computable₂ f) (hmc : ComputableIn {O} m) :
    TuringReducible (instabilitySet f).oracle O := by
  classical
  have hq : ComputablePred fun p : (ℕ × ℕ) × ℕ =>
      f (p.1.2 + p.2) p.1.1 ≠ f p.1.2 p.1.1 := by
    exact (Computable.computablePred <| Primrec.eq.decide.to_comp.comp
      (hf.comp (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)
        (Computable.fst.comp Computable.fst))
      (hf.comp (Computable.snd.comp Computable.fst)
        (Computable.fst.comp Computable.fst))).not
  have hbound := ComputablePred.exists_lt (p := fun p : ℕ × ℕ => fun t =>
    f (p.2 + t) p.1 ≠ f p.2 p.1) hq
  have hb : ComputableIn {O} fun n : ℕ => m n.unpair.1 + 1 :=
    (Primrec.nat_add.to_comp.computableIn.comp <|
      (hmc.comp (Primrec.fst.comp Primrec.unpair).computableIn).pair
        (ComputableIn.const 1))
  have htest : ComputableIn {O} fun n : ℕ =>
      decide (∃ t < m n.unpair.1 + 1,
        f (n.unpair.2 + t) n.unpair.1 ≠ f n.unpair.2 n.unpair.1) :=
    hbound.decide.computableIn.comp (ComputableIn.unpair.pair hb)
  have hχ := Nat.RecursiveIn.cond htest
    (Nat.Primrec.const 1).recursiveIn (Nat.Primrec.const 0).recursiveIn
  apply (Set.turingReducible_iff_computableIn_indicator _ _).2
  refine RecursiveIn.of_eq (RecursiveIn.iff_nat.2 hχ) fun n => ?_
  have hiff : n ∈ instabilitySet f ↔ ∃ t < m n.unpair.1 + 1,
      f (n.unpair.2 + t) n.unpair.1 ≠ f n.unpair.2 n.unpair.1 := by
    simpa only [Nat.pair_unpair] using hm.mem_instabilitySet_iff n.unpair.1 n.unpair.2
  by_cases hn : n ∈ instabilitySet f <;> simp [← hiff, hn]

/-- A modulus computable from the limit makes the limit equivalent to the c.e. instability set. -/
theorem IsModulus.turingEquivalent_instabilitySet (hm : IsModulus f g m)
    (hf : Computable₂ f) (hmc : ComputableIn {fun x => Part.some (g x)} m) :
    TuringEquivalent (fun x => Part.some (g x)) (instabilitySet f).oracle :=
  ⟨hm.converges.computableIn_of_instabilitySet hf.computableIn
      (RecursiveIn.oracle _ rfl), hm.instabilitySet_turingReducible hf hmc⟩

/-- A total function with a computable approximation and a modulus computable from itself
has the degree of a c.e. set. -/
theorem IsModulus.exists_rePred_turingEquivalent (hm : IsModulus f g m)
    (hf : Computable₂ f) (hmc : ComputableIn {fun x => Part.some (g x)} m) :
    ∃ U : Set ℕ, REPred (· ∈ U) ∧ TuringEquivalent (fun x => Part.some (g x)) U.oracle :=
  ⟨instabilitySet f, rePred_mem_instabilitySet hf, hm.turingEquivalent_instabilitySet hf hmc⟩

end TauCeti.Approximation
