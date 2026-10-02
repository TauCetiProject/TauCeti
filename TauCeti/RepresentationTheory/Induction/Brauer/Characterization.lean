/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Brauer.Induction

/-!
# Brauer's characterization of characters

Let `G` be a finite group and `k` an algebraically closed field of characteristic zero.  A class
function `f : G → k` is a virtual character of `G` exactly when its restriction to every
*elementary* subgroup `E ≤ G` is a virtual character of `E`
(`TauCeti.mem_virtualCharacters_iff_forall_comp_subtype_isElementary`).  One direction is the
compatibility of restriction with the lattice; the content is the converse, which certifies a class
function as a genuine integral combination of characters from purely local data.

The argument is the projection formula run against Brauer's induction theorem, and nothing in it is
special to the elementary subgroups: for an arbitrary family of subgroups satisfying an induction
theorem, `TauCeti.mem_virtualCharacters_iff_forall_comp_subtype` of
`TauCeti.RepresentationTheory.Induction.Ideal` already has the equivalence.  What this file adds is
the arithmetic input, `TauCeti.ClassFunction.indVirtualCharacters_eq_virtualCharacters_isElementary`
of `TauCeti.RepresentationTheory.Induction.Brauer.Induction`, which supplies that hypothesis for
the elementary subgroups.  It is not available for the cyclic subgroups, where Artin's theorem
gives only a multiple of `1`, so no cyclic form of the criterion follows: that gap is exactly what
separates Artin's theorem from Brauer's.

## Main statements

* `TauCeti.mem_virtualCharacters_iff_forall_comp_subtype_isElementary`: **Brauer's
  characterization of characters**.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part II,
  Section 11.1, "Characterization of characters".
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 8.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]

/-- **Brauer's characterization of characters.**  Over an algebraically closed field of
characteristic zero, a class function on a finite group is a virtual character if and only if its
restriction to every elementary subgroup is a virtual character.

The class-function hypothesis is not removable: on `G = Equiv.Perm (Fin 3)` the function supported
on a single transposition with value `2` restricts to a virtual character of every elementary
subgroup, all of which are cyclic there, yet is not constant on conjugacy classes. -/
theorem mem_virtualCharacters_iff_forall_comp_subtype_isElementary [CharZero k] [IsAlgClosed k]
    {f : G → k} (hf : f ∈ ClassFunction k G) :
    f ∈ virtualCharacters k G ↔
      ∀ E : Subgroup G, IsElementary E → (fun e : E => f e) ∈ virtualCharacters k E :=
  mem_virtualCharacters_iff_forall_comp_subtype
    ClassFunction.indVirtualCharacters_eq_virtualCharacters_isElementary hf

end TauCeti
