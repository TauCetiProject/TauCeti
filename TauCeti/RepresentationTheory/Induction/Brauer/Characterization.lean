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

Two consequences are recorded alongside it.  The *certificate* form
`TauCeti.ClassFunction.mem_indCharacterSpanInt_of_forall_comp_subtype_isElementary` names the
integral combination the criterion produces, weakening the hypothesis of
`TauCeti.ClassFunction.character_mem_indCharacterSpanInt_isElementary` from "`f` is a character of
`G`" to the local criterion.  Composing instead with the norm-`1` classification
`TauCeti.exists_eq_irreducibleCharacter_or_neg` gives the **Brauer irreducibility test**: local
computations plus one inner product certify irreducibility without exhibiting any representation
of `G`, which is how exceptional characters are recognized.

## Main statements

* `TauCeti.mem_virtualCharacters_iff_forall_comp_subtype_isElementary`: **Brauer's
  characterization of characters**.
* `TauCeti.ClassFunction.mem_indCharacterSpanInt_of_forall_comp_subtype_isElementary`: the same
  hypothesis exhibits `f` as an integral combination of characters induced from irreducible
  characters of elementary subgroups.
* `TauCeti.exists_eq_irreducibleCharacter_or_neg_of_forall_comp_subtype_isElementary` and
  `TauCeti.mem_irreducibleCharacters_of_forall_comp_subtype_isElementary`: **the Brauer
  irreducibility test.**  A class function of norm `1` whose restrictions to the elementary
  subgroups are virtual characters is `±` an irreducible character, and is an irreducible character
  once its degree is a natural number.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part II,
  Section 11.1, "Characterization of characters".
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 8.
-/

public section

namespace TauCeti

universe u v

section Characterization

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

namespace ClassFunction

/-- **The certificate form of Brauer's characterization.**  A class function whose restrictions to
the elementary subgroups are virtual characters is an integral combination of characters induced
from *irreducible* characters of elementary subgroups.  This is
`TauCeti.ClassFunction.character_mem_indCharacterSpanInt_isElementary` with the hypothesis that `f`
is a character of `G` weakened to Brauer's local criterion. -/
theorem mem_indCharacterSpanInt_of_forall_comp_subtype_isElementary [CharZero k] [IsAlgClosed k]
    {f : G → k} (hf : f ∈ ClassFunction k G)
    (hres : ∀ E : Subgroup G, IsElementary E → (fun e : E => f e) ∈ virtualCharacters k E) :
    f ∈ indCharacterSpanInt k G (fun E ↦ IsElementary E) := by
  let _ : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [← indVirtualCharacters_eq_indCharacterSpanInt fun E _ ↦
    isUnit_natCard_subgroup E (isUnit_of_invertible _),
    indVirtualCharacters_eq_virtualCharacters_isElementary]
  exact (mem_virtualCharacters_iff_forall_comp_subtype_isElementary hf).mpr hres

end ClassFunction

end Characterization

/-! ### The Brauer irreducibility test

Norm `1` cuts the virtual-character lattice down to the irreducible characters and their negatives
(`TauCeti.exists_eq_irreducibleCharacter_or_neg`).  Composed with Brauer's characterization this
turns local computations plus one inner product into a proof of irreducibility.
-/

section IrreducibilityTest

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k] [CharZero k]
  [Invertible (Nat.card G : k)]

/-- **A class function of norm `1` whose restrictions to the elementary subgroups are virtual
characters is `±` an irreducible character.**  Brauer's characterization makes it a virtual
character, and `TauCeti.exists_eq_irreducibleCharacter_or_neg` classifies those of norm `1`.  The
sign ambiguity is genuine: `-χ` also has norm `1`, and its restrictions are virtual characters
too. -/
theorem exists_eq_irreducibleCharacter_or_neg_of_forall_comp_subtype_isElementary
    {f : ClassFunction k G}
    (hres : ∀ E : Subgroup G, IsElementary E →
      (fun e : E => (f : G → k) e) ∈ virtualCharacters k E)
    (hnorm : ClassFunction.characterPairing f f = 1) :
    ∃ i, (f : G → k) = irreducibleCharacter k i ∨
      (f : G → k) = -irreducibleCharacter k i :=
  exists_eq_irreducibleCharacter_or_neg
    ((mem_virtualCharacters_iff_forall_comp_subtype_isElementary f.2).mpr hres) hnorm

/-- **The Brauer irreducibility test.**  A class function of norm `1` whose degree is a natural
number and whose restrictions to the elementary subgroups are virtual characters is an irreducible
character of `G`.  The degree hypothesis excludes the negative alternative of
`TauCeti.exists_eq_irreducibleCharacter_or_neg_of_forall_comp_subtype_isElementary`. -/
theorem mem_irreducibleCharacters_of_forall_comp_subtype_isElementary {f : ClassFunction k G}
    (hres : ∀ E : Subgroup G, IsElementary E →
      (fun e : E => (f : G → k) e) ∈ virtualCharacters k E)
    (hnorm : ClassFunction.characterPairing f f = 1) {n : ℕ} (hn : (f : G → k) 1 = n) :
    (f : G → k) ∈ irreducibleCharacters k G :=
  mem_irreducibleCharacters_of_characterPairing_self_eq_one
    ((mem_virtualCharacters_iff_forall_comp_subtype_isElementary f.2).mpr hres) hnorm hn

end IrreducibilityTest

end TauCeti
