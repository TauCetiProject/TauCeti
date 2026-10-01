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

The argument is the projection formula run against Brauer's induction theorem.  That theorem writes
the constant function `1` as a sum of virtual characters `Ind_E^G ψ_E` induced from elementary
subgroups.  Multiplying by `f` and moving `f` inside each induction rewrites the summands as
`Ind_E^G ((Res_E f) · ψ_E)`, whose inner factor is a product of two virtual characters of `E` by
hypothesis; so `f = f · 1` is a sum of induced virtual characters, hence a virtual character.  The
only property of `f` used is that it is a class function, which is what the projection formula
needs, so the step is the ideal property of the induced virtual characters under its weakest
hypothesis, `TauCeti.ClassFunction.mul_mem_indVirtualCharacters_of_forall_comp_subtype`.

Nothing in that argument is special to the elementary subgroups.  A family `P` of subgroups from
which `1` is induced already gives the criterion
(`TauCeti.mem_virtualCharacters_of_forall_comp_subtype`), and a family for which the induction
theorem holds gives the equivalence
(`TauCeti.mem_virtualCharacters_iff_forall_comp_subtype`).  Brauer's induction theorem supplies
that hypothesis for the elementary subgroups.  It is not available for the cyclic subgroups, where
Artin's theorem gives only a multiple of `1`, so no cyclic form of the criterion follows: that gap
is exactly what separates Artin's theorem from Brauer's.

## Main statements

* `TauCeti.mem_virtualCharacters_of_forall_comp_subtype`: if `1` is induced from a family of
  subgroups, a class function whose restrictions to the family are virtual characters is a virtual
  character.
* `TauCeti.mem_virtualCharacters_iff_forall_comp_subtype`: for a family of subgroups satisfying an
  induction theorem, the restrictions to that family detect the virtual characters among the class
  functions.
* `TauCeti.mem_virtualCharacters_iff_forall_comp_subtype_isElementary`: **Brauer's
  characterization of characters**, the elementary-subgroup instance.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part II,
  Section 11.1, "Characterization of characters".
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 8.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] {P : Subgroup G → Prop}

/-- **The restriction criterion for virtual characters.**  If the constant function `1` is induced
from a family of subgroups, then a class function on `G` whose restriction to every subgroup of the
family is a virtual character is itself a virtual character.

Writing `f = f · 1` and pushing `f` inside the inductions through the projection formula
(`TauCeti.ClassFunction.mul_mem_indVirtualCharacters_of_forall_comp_subtype`) exhibits `f` as a sum
of virtual characters induced from the family.  By
`TauCeti.ClassFunction.indVirtualCharacters_eq_virtualCharacters_iff` the hypothesis on the family
is exactly the induction theorem for it. -/
theorem mem_virtualCharacters_of_forall_comp_subtype
    (h1 : (1 : G → k) ∈ ClassFunction.indVirtualCharacters k G P) {f : G → k}
    (hf : f ∈ ClassFunction k G)
    (hres : ∀ S : Subgroup G, P S → (fun s : S => f s) ∈ virtualCharacters k S) :
    f ∈ virtualCharacters k G := by
  have h := ClassFunction.mul_mem_indVirtualCharacters_of_forall_comp_subtype hf hres h1
  rw [mul_one] at h
  exact ClassFunction.indVirtualCharacters_le_virtualCharacters h

/-- **An induction theorem for a family of subgroups makes restriction to that family detect the
virtual characters.**  For a class function on `G`, membership in the virtual-character lattice is
equivalent to membership of all its restrictions to the family.

The forward direction `TauCeti.comp_subtype_mem_virtualCharacters` needs no hypothesis on the
family; the hypothesis is used only for the converse. -/
theorem mem_virtualCharacters_iff_forall_comp_subtype
    (hP : ClassFunction.indVirtualCharacters k G P = virtualCharacters k G) {f : G → k}
    (hf : f ∈ ClassFunction k G) :
    f ∈ virtualCharacters k G ↔
      ∀ S : Subgroup G, P S → (fun s : S => f s) ∈ virtualCharacters k S :=
  ⟨fun h S _ => comp_subtype_mem_virtualCharacters S h,
    mem_virtualCharacters_of_forall_comp_subtype
      (ClassFunction.indVirtualCharacters_eq_virtualCharacters_iff.mp hP) hf⟩

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
