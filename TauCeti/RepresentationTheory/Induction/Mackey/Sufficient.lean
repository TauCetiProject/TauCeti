/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Mackey.Endomorphism
import TauCeti.CategoryTheory.Simple.Endomorphism

/-!
# Mackey sufficiency over arbitrary fields

Let `H` be a subgroup of a finite group `G` whose order is invertible in a field `k`.
If `A` is a simple representation of `H` and its nonidentity Mackey intertwining spaces
vanish, then its induction to `G` is simple. No splitting-field hypothesis is needed:
the endomorphism algebra of `A` may be a division algebra larger than `k`.

The algebra comparison `FDRep.indEndAlgEquiv` transports Schur's division algebra to
the induced object, and Maschke's theorem supplies the converse to Schur's lemma.
We give the criterion both on double-coset representatives and on all elements
outside the subgroup. For a normal subgroup, the latter condition says that no such
element fixes the isomorphism class of `A` under conjugation.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §7.4, Proposition 23.
* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 5, Theorem 5.6.
* The algebra comparison `FDRep.indEndAlgEquiv` and the converse to Schur's lemma
  `CategoryTheory.simple_iff_nontrivial_end_and_isUnit` supply the two main steps.
-/

public section

open CategoryTheory TauCeti

namespace FDRep

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G] {H : Subgroup G}

/-- Mackey's sufficient criterion over any field satisfying Maschke's hypothesis:
induction of a simple representation is simple if the nonidentity double-coset
intertwining spaces vanish. -/
theorem simple_indFDRep_of_mackeyDisjoint_doubleCoset (A : FDRep k H) [Simple A]
    (hG : IsUnit (Nat.card G : k))
    (h : ∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G),
      D ≠ DoubleCoset.mk H H 1 → MackeyDisjoint A D.out) :
    Simple (indFDRep A) := by
  have : NeZero (Nat.card G : k) := ⟨hG.ne_zero⟩
  exact simple_of_ringEquiv_end (indFDRep A) (A.indEndAlgEquiv h).toRingEquiv

/-- Elementwise Mackey sufficiency over an arbitrary field: it is enough to check
disjointness at each group element outside the inducing subgroup. -/
theorem simple_indFDRep_of_forall_mackeyDisjoint (A : FDRep k H) [Simple A]
    (hG : IsUnit (Nat.card G : k)) (h : ∀ s ∉ H, MackeyDisjoint A s) :
    Simple (indFDRep A) :=
  A.simple_indFDRep_of_mackeyDisjoint_doubleCoset hG (A.forall_mackeyDisjoint_out_iff.mpr h)

/-- For a normal subgroup, a simple representation with no isomorphic conjugate
outside that subgroup induces to a simple representation over any Maschke field. -/
theorem simple_indFDRep_of_isEmpty_conjNormalFDRep_iso [H.Normal]
    (A : FDRep k H) [Simple A] (hG : IsUnit (Nat.card G : k))
    (h : ∀ s ∉ H, IsEmpty (conjNormalFDRep s A ≅ A)) :
    Simple (indFDRep A) := by
  exact A.simple_indFDRep_of_forall_mackeyDisjoint hG fun s hs =>
    (mackeyDisjoint_iff_isEmpty_iso_of_normal A s).mpr (h s hs)

end FDRep
