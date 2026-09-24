/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index

/-!
# Transitive actions

Mathlib's `MulAction.ofQuotientStabilizer` sends the coset of `g` in `G ⧸ stabilizer G b` to
`g • b`; it is injective by `MulAction.injective_ofQuotientStabilizer`, and its image is the orbit
of `b`, which is the orbit-stabiliser theorem. When the action is transitive that orbit is all of
`X`, so the map is a bijection. This file records that specialisation, together with the
equivariance -- Mathlib's `MulAction.ofQuotientStabilizer_smul` -- that makes it an isomorphism of
`G`-sets rather than a bare bijection.

It also records one closure property of pretransitivity, `TauCeti.isPretransitive_prod_left`,
which needs no group and no action laws and so comes first, before any of the above structure is
assumed.

## Main definitions

* `TauCeti.quotientStabilizerEquiv`: for a transitive action of `G` on `X` and a point `b : X`,
  the equivalence `G ⧸ stabilizer G b ≃ X` sending the coset of `g` to `g • b`.

## Main results

* `TauCeti.quotientStabilizerEquiv_mk`: its value on a coset, and
  `TauCeti.quotientStabilizerEquiv_smul`: its equivariance.
* `TauCeti.natCard_dvd_natCard_of_isPretransitive`: the number of points of a nonempty set acted
  on transitively divides the order of the group.
* `TauCeti.stabilizer_eq_bot_of_natCard_eq`, `TauCeti.eq_one_of_natCard_eq_of_smul_eq_self`: a
  transitive action of a group with as many elements as the finite set acted on is regular, so
  only the identity fixes a point.
* `TauCeti.isPretransitive_prod_left`: a product with a subsingleton stays pretransitive.

## Implementation notes

The equivalence is unbundled -- an `Equiv` of types together with a separate equivariance lemma --
because that is the shape the constructions consuming it take their argument in, for instance
`TauCeti.ofMulActionEquivCongr`, which builds the induced equivalence of permutation
representations.
-/

public section

open MulAction

namespace TauCeti

section SMul

variable {G : Type*} (X Y : Type*) [SMul G X] [SMul G Y]

/-- **Pairing a pretransitive action with a subsingleton leaves it pretransitive.** A scalar
carrying `p.1` to `q.1` carries `p` to `q` outright, the second coordinates being equal for want of
anywhere else to be, so neither a monoid nor any action law enters.

`Y` is allowed to be empty, in which case `X × Y` is empty and the statement is vacuous. Counting
the orbits of such a product -- via `TauCeti.MulAction.card_orbitRelQuotient_eq_one`, which is the
value Burnside's lemma takes on it -- needs more than this: a genuine `MulAction` of a group, and
`Nonempty` to rule the empty case back out. -/
theorem isPretransitive_prod_left [IsPretransitive G X] [Subsingleton Y] :
    IsPretransitive G (X × Y) :=
  ⟨fun p q => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G p.1 q.1
    exact ⟨g, Prod.fst_injective hg⟩⟩

end SMul

variable (G : Type*) {X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]

/-- **Orbit-stabiliser for a transitive action**: the coset space of the stabiliser of a point is
the set acted on, the coset of `g` corresponding to `g • b`.  This is
`MulAction.ofQuotientStabilizer`, which transitivity makes surjective. -/
noncomputable def quotientStabilizerEquiv (b : X) : G ⧸ stabilizer G b ≃ X :=
  Equiv.ofBijective (ofQuotientStabilizer G b)
    ⟨injective_ofQuotientStabilizer G b, fun x => by
      obtain ⟨g, hg⟩ := exists_smul_eq G b x
      exact ⟨QuotientGroup.mk g, (ofQuotientStabilizer_mk G b g).trans hg⟩⟩

/-- The computation rule for `TauCeti.quotientStabilizerEquiv`: on the coset represented by `g` it
takes the value `g • b`. -/
@[simp]
theorem quotientStabilizerEquiv_mk (b : X) (g : G) :
    quotientStabilizerEquiv G b (QuotientGroup.mk g) = g • b :=
  ofQuotientStabilizer_mk G b g

/-- The identification of the coset space with the set acted on is equivariant. -/
@[simp]
theorem quotientStabilizerEquiv_smul (b : X) (g : G) (q : G ⧸ stabilizer G b) :
    quotientStabilizerEquiv G b (g • q) = g • quotientStabilizerEquiv G b q :=
  ofQuotientStabilizer_smul G b g q

/-- If `G` acts transitively on a nonempty set `X`, then the number of points of `X` divides the
order of `G`: it is the index of a point stabiliser, by `MulAction.index_stabilizer_of_transitive`.
Both cardinalities are `Nat.card`, so the statement also holds, trivially, for infinite `G`. -/
theorem natCard_dvd_natCard_of_isPretransitive [Nonempty X] : Nat.card X ∣ Nat.card G := by
  obtain ⟨x⟩ := ‹Nonempty X›
  simpa [index_stabilizer_of_transitive G x] using (stabilizer G x).index_dvd_card

variable {G} in
/-- **A transitive action of a group with as many elements as the finite set acted on is
regular**: every point stabiliser is trivial. The index of a point stabiliser is the number of
points, by `MulAction.index_stabilizer_of_transitive`, so the stabiliser has one element. -/
theorem stabilizer_eq_bot_of_natCard_eq [Finite X] (h : Nat.card G = Nat.card X) (x : X) :
    stabilizer G x = ⊥ := by
  have : Nonempty X := ⟨x⟩
  have hmul := (stabilizer G x).index_mul_card
  rw [index_stabilizer_of_transitive G x, h] at hmul
  exact Subgroup.card_eq_one.mp
    (Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [hmul, mul_one]))

variable {G} in
/-- In a transitive action of a group with as many elements as the finite set acted on, an
element fixing a point is the identity. -/
theorem eq_one_of_natCard_eq_of_smul_eq_self [Finite X] (h : Nat.card G = Nat.card X) {g : G}
    {x : X} (hgx : g • x = x) : g = 1 :=
  Subgroup.mem_bot.mp (stabilizer_eq_bot_of_natCard_eq h x ▸ mem_stabilizer_iff.mpr hgx)

end TauCeti
