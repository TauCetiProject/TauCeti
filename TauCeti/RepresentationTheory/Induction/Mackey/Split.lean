/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Mackey.Sufficient

/-!
# The Mackey criterion over splitting fields

For a finite group over a field whose characteristic does not divide the group order,
Mackey disjointness is sufficient for induction of a simple representation to be simple.
It is necessary when the induced simple object has a one-dimensional endomorphism space.
Thus scalar Schur for simple representations of the ambient group gives the iff criterion,
without algebraic closure or characteristic zero. No splitting hypothesis on the subgroup
is required.

The necessity proof uses the natural-number intertwining formula, not its cast into the
coefficient field. Consequently it also works in positive characteristic. The sufficient
direction is the arbitrary-field division-algebra criterion in `Mackey.Sufficient`.

Algebraic closure supplies scalar Schur, yielding the corollaries
`TauCeti.simple_indFDRep_iff_doubleCoset`, `TauCeti.simple_indFDRep_iff` and
`TauCeti.simple_indFDRep_iff_of_normal`. They require only `[NeZero (Nat.card G : k)]`,
not characteristic zero, and are used by the reducibility and Clifford-theory applications.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §7.4, Proposition 23.
* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 5, Theorem 5.6.
-/

public section

open CategoryTheory TauCeti

namespace FDRep

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G] {H : Subgroup G}

/-- Mackey's iff criterion with scalar Schur imposed only on simple representations
of the ambient group. It is valid over non-algebraically-closed splitting fields and
in every characteristic in which the group order is invertible. -/
theorem simple_indFDRep_iff_doubleCoset_of_scalarSchur (A : FDRep k H)
    (hG : IsUnit (Nat.card G : k))
    (hSplitG : ∀ W : FDRep k G, Simple W → Module.finrank k (W ⟶ W) = 1) :
    Simple (indFDRep A) ↔ Simple A ∧
      ∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G),
        D ≠ DoubleCoset.mk H H 1 → MackeyDisjoint A D.out := by
  constructor
  · intro h
    exact A.simple_and_mackeyDisjoint_of_finrank_end_indFDRep_eq_one
      (isUnit_natCard_subgroup H hG) (hSplitG _ h)
  · rintro ⟨hA, h⟩
    have := hA
    exact A.simple_indFDRep_of_mackeyDisjoint_doubleCoset hG h

/-- The splitting-field Mackey criterion checked on all elements outside the subgroup,
rather than on chosen double-coset representatives. -/
theorem simple_indFDRep_iff_of_scalarSchur (A : FDRep k H)
    (hG : IsUnit (Nat.card G : k))
    (hSplitG : ∀ W : FDRep k G, Simple W → Module.finrank k (W ⟶ W) = 1) :
    Simple (indFDRep A) ↔ Simple A ∧ ∀ s ∉ H, MackeyDisjoint A s := by
  rw [A.simple_indFDRep_iff_doubleCoset_of_scalarSchur hG hSplitG,
    A.forall_mackeyDisjoint_out_iff]

/-- For a normal subgroup over a splitting field, simplicity of induction is equivalent
to simplicity of the original representation and absence of isomorphic conjugates outside
the subgroup. No scalar-Schur hypothesis on the subgroup is needed. -/
theorem simple_indFDRep_iff_of_normal_of_scalarSchur [H.Normal] (A : FDRep k H)
    (hG : IsUnit (Nat.card G : k))
    (hSplitG : ∀ W : FDRep k G, Simple W → Module.finrank k (W ⟶ W) = 1) :
    Simple (indFDRep A) ↔
      Simple A ∧ ∀ s ∉ H, IsEmpty (conjNormalFDRep s A ≅ A) := by
  rw [A.simple_indFDRep_iff_of_scalarSchur hG hSplitG]
  refine and_congr_right fun hA => ?_
  have := hA
  exact forall_congr' fun s => forall_congr' fun _ =>
    mackeyDisjoint_iff_isEmpty_iso_of_normal A s

end FDRep

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
  {H : Subgroup G}

/-- **The Mackey irreducibility criterion.** The representation induced from `A` is irreducible
exactly when `A` is irreducible and every double coset `HsH` other than `H` itself, read at its
chosen representative, is Mackey disjoint. Algebraic closure supplies scalar Schur. -/
theorem simple_indFDRep_iff_doubleCoset (A : FDRep k H) :
    Simple (indFDRep A) ↔ Simple A ∧
      ∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G), D ≠ DoubleCoset.mk H H 1 →
        MackeyDisjoint A D.out :=
  A.simple_indFDRep_iff_doubleCoset_of_scalarSchur (isUnit_iff_ne_zero.mpr (NeZero.ne _))
    fun W _ => CategoryTheory.finrank_endomorphism_simple_eq_one k W

/-- **The Mackey irreducibility criterion, elementwise.** The disjointness condition of
`TauCeti.simple_indFDRep_iff_doubleCoset` may equally be asked of every element `s ∉ H` rather than
of one chosen representative of every nonidentity double coset. -/
theorem simple_indFDRep_iff (A : FDRep k H) :
    Simple (indFDRep A) ↔ Simple A ∧ ∀ s ∉ H, MackeyDisjoint A s :=
  A.simple_indFDRep_iff_of_scalarSchur (isUnit_iff_ne_zero.mpr (NeZero.ne _))
    fun W _ => CategoryTheory.finrank_endomorphism_simple_eq_one k W

/-- **The Mackey irreducibility criterion for a normal subgroup.** If `H ◁ G`, then the
representation induced from `A` is irreducible exactly when `A` is irreducible and none of its
conjugates `{}^s A`, for `s ∉ H`, is isomorphic to `A`. -/
theorem simple_indFDRep_iff_of_normal [H.Normal] (A : FDRep k H) :
    Simple (indFDRep A) ↔
      Simple A ∧ ∀ s ∉ H, IsEmpty (conjNormalFDRep s A ≅ A) :=
  A.simple_indFDRep_iff_of_normal_of_scalarSchur (isUnit_iff_ne_zero.mpr (NeZero.ne _))
    fun W _ => CategoryTheory.finrank_endomorphism_simple_eq_one k W

end TauCeti
