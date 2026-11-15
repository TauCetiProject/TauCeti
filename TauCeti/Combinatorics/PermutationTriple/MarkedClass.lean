/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.IsoClass

/-!
# Marked triple classes with a fixed label

The diagonal quotient defining `MarkedIsoClass n` lets a relabeling move both the triple and
its marked sheet. Equivalently, fix any label `i : Fin n` and quotient connected triples by
only the permutations fixing `i`. The equivalence sends the stabilizer orbit of `t` to the
marked class of `(t, i)` and commutes with forgetting the mark.

This gives a fixed-label description of the combinatorial invariant of pointed covers, without
identifying pointed classes with literal triples or with unpointed classes.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  London Mathematical Society Student Texts 79, Cambridge University Press 2012, §2.7.
-/

public section

namespace TauCeti

open Equiv

variable {n : ℕ}

/-- Forget a fixed marked label by enlarging its stabilizer to the full relabeling group. -/
def ConnectedIsoClass.ofStabilizerOrbit (i : Fin n) :
    MulAction.orbitRel.Quotient (MulAction.stabilizer (Perm (Fin n)) i) (ConnectedTriple n) →
      ConnectedIsoClass n :=
  Quotient.map' id fun _ _ ⟨τ, hτ⟩ =>
    ⟨(τ : Perm (Fin n)), by simpa only [Subgroup.smul_def, id_eq] using hτ⟩

@[simp]
theorem ConnectedIsoClass.ofStabilizerOrbit_mk (i : Fin n) (t : ConnectedTriple n) :
    ofStabilizerOrbit i (Quotient.mk'' t) = mk t := (rfl)

namespace MarkedIsoClass

/-- Forgetting the mark after fixing a label is just passing to the full relabeling orbit. -/
@[simp]
theorem forget_stabilizerEquiv (i : Fin n)
    (q : MulAction.orbitRel.Quotient (MulAction.stabilizer (Perm (Fin n)) i)
      (ConnectedTriple n)) :
    (stabilizerEquiv i q).forget = ConnectedIsoClass.ofStabilizerOrbit i q := by
  induction q using Quotient.inductionOn'
  simp

end MarkedIsoClass
end TauCeti
