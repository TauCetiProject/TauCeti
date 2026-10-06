/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.IsoClass
public import TauCeti.Algebra.GroupAction.DiagonalOrbits

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

/-- Fixing any label identifies its stabilizer-orbit quotient with marked triple classes.
For positive degree, `i = 0` gives the fixed-zero-label description. -/
noncomputable def stabilizerEquiv (i : Fin n) :
    MulAction.orbitRel.Quotient (MulAction.stabilizer (Perm (Fin n)) i) (ConnectedTriple n) ≃
      MarkedIsoClass n :=
  TauCeti.MulAction.orbitRelQuotientStabilizerEquiv
    (G := Perm (Fin n)) (X := ConnectedTriple n) i

/-- The stabilizer orbit of a triple is sent to its class marked at the fixed label. -/
@[simp]
theorem stabilizerEquiv_mk (i : Fin n) (t : ConnectedTriple n) :
    stabilizerEquiv i (Quotient.mk'' t) = mk t i := by
  rw [stabilizerEquiv]
  exact (TauCeti.MulAction.orbitRelQuotientStabilizerEquiv_mk
    (G := Perm (Fin n)) i t).trans (quotient_mk t i)

/-- A class already marked at the fixed label is sent back to the stabilizer orbit of its
triple. -/
@[simp]
theorem stabilizerEquiv_symm_mk (i : Fin n) (t : ConnectedTriple n) :
    (stabilizerEquiv i).symm (mk t i) = Quotient.mk'' t := by
  rw [← stabilizerEquiv_mk i t, Equiv.symm_apply_apply]

/-- Moving a marked label back to the fixed label also applies the inverse permutation to
its triple. -/
theorem stabilizerEquiv_symm_mk_apply (i : Fin n) (t : ConnectedTriple n)
    (τ : Perm (Fin n)) :
    (stabilizerEquiv i).symm (mk t (τ i)) = Quotient.mk'' (τ⁻¹ • t) := by
  apply (stabilizerEquiv i).injective
  simp only [Equiv.apply_symm_apply, stabilizerEquiv_mk]
  simpa only [smul_inv_smul] using mk_smul τ (τ⁻¹ • t) i

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
