/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Brauer.Induction

/-!
# Brauer's characterization of characters

A class function on a finite group is a virtual character as soon as each of its restrictions to an
**elementary** subgroup is one:

`f ∈ virtualCharacters k G ↔ ∀ E, IsElementary E → Res_E f ∈ virtualCharacters k E`

over an algebraically closed field of characteristic zero.  This is
`TauCeti.ClassFunction.mem_virtualCharacters_iff_forall_comp_subtype_isElementary`, **Brauer's
characterization of characters**.  One direction is the compatibility of restriction with the
lattice (`TauCeti.comp_subtype_mem_virtualCharacters`); the content is the other, which turns a
family of local certificates into a global one and is the standard way to certify that a class
function assembled by hand — an exceptional character, a difference of induced characters — is a
genuine virtual character.

## The route

The only input beyond bookkeeping is Brauer's induction theorem
(`TauCeti.ClassFunction.indVirtualCharacters_eq_virtualCharacters_isElementary`), in the form that
the constant function `1` is induced from the elementary subgroups.  Given that, the argument is
one line of the ideal property: writing `1 = ∑ᵢ Ind_{Eᵢ} ψᵢ` and multiplying by `f`, the projection
formula rewrites each `f · Ind_{Eᵢ} ψᵢ` as `Ind_{Eᵢ} ((Res_{Eᵢ} f) · ψᵢ)`, whose inducing function
is a virtual character of `Eᵢ` because `Res_{Eᵢ} f` is one by hypothesis.  So `f = f · 1` is a sum
of induced virtual characters.

The point is that this uses `f` only through its restrictions, never through a property of `f`
itself, which is why it can *conclude* that `f` is a virtual character rather than having to assume
it.  That is exactly the generality of
`TauCeti.ClassFunction.mul_mem_indVirtualCharacters_of_forall_comp_subtype`, and it is what
separates this statement from the ideal property
`TauCeti.ClassFunction.mul_mem_indVirtualCharacters` it refines.

Nothing about elementary subgroups is used in the argument, so the criterion is proved for an
arbitrary family `P` of subgroups from which `1` is induced, alongside the ideal property in
`TauCeti.RepresentationTheory.Induction.Ideal`
(`TauCeti.ClassFunction.mem_indVirtualCharacters_iff_forall_comp_subtype`), and gives at once the
sharper conclusion that `f` is a `ℤ`-combination of characters *induced from members of the family*.
Brauer's theorem is that criterion specialized to `P = IsElementary`.  For the cyclic subgroups the
hypothesis `1 ∈ V_G` fails — Artin's induction theorem is only rational — so no such criterion
holds there, and the elementary subgroups are the smallest family for which one is available.

## Main statements

* `TauCeti.ClassFunction.one_mem_indVirtualCharacters_isElementary`: Brauer's induction theorem in
  the form the criterion consumes, that `1` is induced from the elementary subgroups.
* `TauCeti.ClassFunction.mem_virtualCharacters_iff_forall_comp_subtype_isElementary`: **Brauer's
  characterization of characters**.
* `TauCeti.ClassFunction.mem_indCharacterSpanInt_of_forall_comp_subtype_isElementary`: the same
  hypothesis exhibits `f` as an integral combination of characters induced from irreducible
  characters of elementary subgroups, the certificate form.
* `TauCeti.exists_eq_irreducibleCharacter_or_neg_of_forall_comp_subtype_isElementary` and
  `TauCeti.mem_irreducibleCharacters_of_forall_comp_subtype_isElementary`: **the Brauer
  irreducibility test.**  A class function of norm `1` whose restrictions to the elementary
  subgroups are virtual characters is `±` an irreducible character, and is an irreducible character
  once its degree is a natural number.  No representation carrying it need be exhibited.

## Implementation notes

The class-function hypothesis on `f` is not redundant and is carried explicitly.  The restriction
of `f` to a subgroup constrains the values of `f` on that subgroup only, and every cyclic subgroup
is elementary, so the local hypotheses alone say nothing about how `f` compares on two conjugate
elements lying in different cyclic subgroups; conjugation invariance has to be assumed.  It is what
the projection formula `TauCeti.indClassFun_comp_subtype_mul` needs of the multiplier.

Restriction along `E ≤ G` is written `fun e : E => f e`, the spelling of
`TauCeti.comp_subtype_mem_virtualCharacters` and of the projection formula, rather than through
`TauCeti.ClassFunction.comap`; the two agree, and the unbundled form is what the lattice statements
are phrased in.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part II,
  Section 11.1, Theorem 21.
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Theorem 8.4(a).
-/

public section

namespace TauCeti

universe u v

namespace ClassFunction

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [CharZero k] [IsAlgClosed k]

/-- **The constant function `1` is induced from the elementary subgroups.**  This is Brauer's
induction theorem `TauCeti.ClassFunction.indVirtualCharacters_eq_virtualCharacters_isElementary`
read through `TauCeti.ClassFunction.indVirtualCharacters_eq_virtualCharacters_iff`, and it is the
single arithmetic input to everything below. -/
theorem one_mem_indVirtualCharacters_isElementary :
    (1 : G → k) ∈ indVirtualCharacters k G (fun E ↦ IsElementary E) :=
  indVirtualCharacters_eq_virtualCharacters_iff.mp
    indVirtualCharacters_eq_virtualCharacters_isElementary

/-- **Brauer's characterization of characters.**  A class function on a finite group is a virtual
character exactly when each of its restrictions to an elementary subgroup is a virtual character of
that subgroup.

The forward direction is the compatibility of restriction with the virtual-character lattice.  The
converse is the local-to-global criterion
`TauCeti.ClassFunction.mem_indVirtualCharacters_iff_forall_comp_subtype` fed with Brauer's
induction theorem, and it is the useful one: it certifies a class function as a virtual character
from finitely many computations on elementary subgroups, with no representation of `G` in sight. -/
theorem mem_virtualCharacters_iff_forall_comp_subtype_isElementary {f : G → k}
    (hf : f ∈ ClassFunction k G) :
    f ∈ virtualCharacters k G ↔
      ∀ E : Subgroup G, IsElementary E → (fun e : E => f e) ∈ virtualCharacters k E := by
  rw [← indVirtualCharacters_eq_virtualCharacters_isElementary (k := k) (G := G)]
  exact mem_indVirtualCharacters_iff_forall_comp_subtype
    one_mem_indVirtualCharacters_isElementary hf

/-- **The certificate form of Brauer's characterization.**  A class function whose restrictions to
the elementary subgroups are virtual characters is an integral combination of characters induced
from *irreducible* characters of elementary subgroups.  This is the statement of
`TauCeti.ClassFunction.character_mem_indCharacterSpanInt_isElementary` with the hypothesis that `f`
is a character of `G` weakened to Brauer's local criterion. -/
theorem mem_indCharacterSpanInt_of_forall_comp_subtype_isElementary {f : G → k}
    (hf : f ∈ ClassFunction k G)
    (hres : ∀ E : Subgroup G, IsElementary E → (fun e : E => f e) ∈ virtualCharacters k E) :
    f ∈ indCharacterSpanInt k G (fun E ↦ IsElementary E) := by
  let _ : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [← indVirtualCharacters_eq_indCharacterSpanInt fun E _ ↦
    isUnit_natCard_subgroup E (isUnit_of_invertible _)]
  exact mem_indVirtualCharacters_of_forall_comp_subtype one_mem_indVirtualCharacters_isElementary
    hf hres

end ClassFunction

/-! ### The Brauer irreducibility test

Norm `1` cuts the virtual-character lattice down to the irreducible characters and their negatives
(`TauCeti.exists_eq_irreducibleCharacter_or_neg`).  Composed with Brauer's characterization this
turns local computations plus one inner product into a proof of irreducibility, which is how
exceptional characters are recognized.
-/

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
    ((ClassFunction.mem_virtualCharacters_iff_forall_comp_subtype_isElementary f.2).mpr hres) hnorm

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
    ((ClassFunction.mem_virtualCharacters_iff_forall_comp_subtype_isElementary f.2).mpr hres)
    hnorm hn

end TauCeti
