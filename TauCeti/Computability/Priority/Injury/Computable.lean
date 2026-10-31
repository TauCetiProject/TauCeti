/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Priority.Injury.Basic
public import TauCeti.Computability.RE
import Mathlib.Computability.Reduce

/-!
# Effectivity of the injury objects

Let a finite-injury construction enumerate `A` in finite stages, with restraints `r e s`. When
membership `x ∈ A s` is decidable by a computable procedure, uniformly in `s` and `x`, and the
restraint `r e s` is computable from `e` and `s`, the injury objects of
`TauCeti.Computability.Priority.Injury.Basic` are effective, uniformly in the requirement `e`:

* the injury events, and hence the membership relation of each injury batch, are computable;
* whether an injury batch is nonempty is computable: an injuring number lies at or below the
  active restraint, so a bounded search suffices;
* the injury stages are therefore computable;
* the injury set `I_e` is c.e.: a number is in it when it injures `e` at some stage.

The injury set is in general not computable uniformly in `e`: for a computable enumeration of the
halting set and the constant restraint `r e s = some e`, the injury set of `e` is the halting set
cut off at `e`, and the diagonal query `e ∈ I_e` would decide the halting set.

## Main results

* `TauCeti.Priority.computablePred_mem_injuryEvents`: the injury events are computable.
* `TauCeti.Priority.computablePred_injuriesAt_nonempty`: nonemptiness of injury batches is
  computable.
* `TauCeti.Priority.computablePred_mem_injuryStages`: the injury stages are computable.
* `TauCeti.Priority.rePred_mem_injurySet`: the injury sets are c.e.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.1.
-/

public section

open Computable

namespace TauCeti

namespace Priority

variable {A : ℕ → Finset ℕ} {r : ℕ → ℕ → Option ℕ}

/-- **The injury events are computable**, uniformly in the requirement, when membership in the
stages and the restraints are computable. -/
theorem computablePred_mem_injuryEvents (hA : ComputablePred fun p : ℕ × ℕ => p.2 ∈ A p.1)
    (hr : Computable₂ r) : ComputablePred fun p : ℕ × ℕ × ℕ => p.2 ∈ injuryEvents A r p.1 := by
  have hnew : ComputablePred fun p : ℕ × ℕ × ℕ => p.2.2 ∈ A (p.2.1 + 1) :=
    ComputablePred.computable_of_manyOneReducible
      ⟨fun p => (p.2.1 + 1, p.2.2), (succ.comp (fst.comp snd)).pair (snd.comp snd),
        fun _ => Iff.rfl⟩ hA
  have hold : ComputablePred fun p : ℕ × ℕ × ℕ => p.2.2 ∈ A p.2.1 :=
    ComputablePred.computable_of_manyOneReducible ⟨fun p => p.2, snd, fun _ => Iff.rfl⟩ hA
  have hle : ComputablePred fun p : ℕ × ℕ × ℕ => ∃ b, r p.1 p.2.1 = some b ∧ p.2.2 ≤ b :=
    ComputablePred.exists_eq_some_and (hr.comp fst (fst.comp snd))
      (PrimrecPred.computablePred
        (Primrec.nat_le.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  exact (hnew.and (hold.not.and hle)).of_eq fun p => by simp

/-- **Nonemptiness of the injury batches is computable**, uniformly in the requirement and the
stage, when membership in the stages and the restraints are computable. -/
theorem computablePred_injuriesAt_nonempty (hA : ComputablePred fun p : ℕ × ℕ => p.2 ∈ A p.1)
    (hr : Computable₂ r) : ComputablePred fun p : ℕ × ℕ => (injuriesAt A r p.1 p.2).Nonempty := by
  have hbound : Computable fun p : ℕ × ℕ => (r p.1 p.2).elim 0 (· + 1) :=
    (Computable.option_casesOn hr (const 0) (succ.comp snd).to₂).of_eq fun p => by
      cases r p.1 p.2 <;> rfl
  have hsearch := ComputablePred.exists_lt (p := fun (q : ℕ × ℕ) x => x ∈ injuriesAt A r q.1 q.2)
    (ComputablePred.computable_of_manyOneReducible
      ⟨fun q : (ℕ × ℕ) × ℕ => (q.1.1, q.1.2, q.2),
        (fst.comp fst).pair ((snd.comp fst).pair snd), fun _ => by simp⟩
      (computablePred_mem_injuryEvents hA hr))
  exact (ComputablePred.computable_of_manyOneReducible
    ⟨fun p : ℕ × ℕ => (p, (r p.1 p.2).elim 0 (· + 1)), Computable.id.pair hbound,
      fun _ => injuriesAt_nonempty_iff⟩ hsearch)

/-- **The injury stages are computable**, uniformly in the requirement, when membership in the
stages and the restraints are computable. -/
theorem computablePred_mem_injuryStages (hA : ComputablePred fun p : ℕ × ℕ => p.2 ∈ A p.1)
    (hr : Computable₂ r) : ComputablePred fun p : ℕ × ℕ => p.2 ∈ injuryStages A r p.1 := by
  have hpos : ComputablePred fun p : ℕ × ℕ => p.2 ≠ 0 :=
    (PrimrecPred.computablePred (Primrec.eq.comp Primrec.snd (Primrec.const 0))).not
  have hprev : ComputablePred fun p : ℕ × ℕ => (injuriesAt A r p.1 (p.2 - 1)).Nonempty :=
    ComputablePred.computable_of_manyOneReducible
      ⟨fun p : ℕ × ℕ => (p.1, p.2 - 1), fst.pair (Primrec.nat_sub.to_comp.comp snd (const 1)),
        fun _ => Iff.rfl⟩ (computablePred_injuriesAt_nonempty hA hr)
  refine (hpos.and hprev).of_eq fun ⟨e, t⟩ => ?_
  cases t <;> simp

/-- **The injury sets are c.e.**, uniformly in the requirement, when membership in the stages and
the restraints are computable. They need not be computable uniformly in the requirement. -/
theorem rePred_mem_injurySet (hA : ComputablePred fun p : ℕ × ℕ => p.2 ∈ A p.1)
    (hr : Computable₂ r) : REPred fun p : ℕ × ℕ => p.2 ∈ injurySet A r p.1 :=
  ComputablePred.rePred_exists (p := fun (q : ℕ × ℕ) s => q.2 ∈ injuriesAt A r q.1 s)
    (ComputablePred.computable_of_manyOneReducible
      ⟨fun q : (ℕ × ℕ) × ℕ => (q.1.1, q.2, q.1.2),
        (fst.comp fst).pair (snd.pair (snd.comp fst)), fun _ => by simp⟩
      (computablePred_mem_injuryEvents hA hr)) |>.of_eq fun _ => mem_injurySet.symm

end Priority

end TauCeti
