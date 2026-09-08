/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Decomposition

/-!
# The dimension formula of Clifford's theorem

Let `N` be a normal subgroup of a finite group `G` and let `W` be an irreducible representation of
`G` over an algebraically closed field of characteristic zero.  Clifford's theorem describes the
restriction of `W` to `N`: its irreducible constituents form a single `G`-orbit, indexed by the
left cosets of the inertia group of any one of them, and they all occur with one common positive
multiplicity `e`.  Counting dimensions in that description gives

`dim W = e · [G : inertia V] · dim V`

for an irreducible constituent `V` of `Res_N W`.  This file proves that identity and reads off the
two divisibilities it contains: both the index of the inertia group of a constituent and the
dimension of the constituent divide the dimension of `W`.  The index of the inertia group also
divides `[G : N]`, since the inertia group contains `N`, so the count of distinct conjugates is
constrained from both sides.

The proof is the character form of Clifford's theorem
(`TauCeti.clifford_restrict_character`) evaluated at the identity.  There the restriction character
is exhibited as `e` times the sum of the characters of the conjugates `{}^g V` over a left
transversal `reps` of `inertia V`, so at the identity the left-hand side is `dim W` and each of the
`reps.card` summands on the right is `dim V`, a conjugate having the same dimension.  Two small
steps finish it: the transversal has `[G : inertia V]` elements, because a finite set meeting every
left coset of a subgroup exactly once is a complement of it in the sense of
`Subgroup.IsComplement`; and the resulting identity in `k` is an identity of natural
numbers, because `k` has characteristic zero.

Characteristic zero is used only for that last cast.  The character identity itself needs no more
than Maschke's condition `IsUnit (Nat.card G : k)`, but in characteristic `p` the identity in `k`
determines the dimensions only modulo `p`, so the natural-number equation below would not follow.

## Main statements

* `TauCeti.clifford_finrank`: **Clifford's dimension formula**,
  `dim W = e · [G : inertia V] · dim V` for a simple constituent `V` of the restriction and its
  multiplicity `e`.
* `TauCeti.clifford_dvd_finrank`: the divisibilities it contains, `[G : inertia V] ∣ dim W` and
  `dim V ∣ dim W`, together with `[G : inertia V] ∣ [G : N]`.
* `TauCeti.clifford_inertia_eq_top_of_finrank_eq_one`: a one-dimensional representation of `G`
  restricts to a one-dimensional representation of `N` whose inertia group is all of `G`.

## References

This is the numerical half of the **Clifford's theorem** milestone of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, which asks for the
consequence that "`t = [G : inertia V]` divides `finrank W / (e · finrank V)`".  The packaged
decomposition `Res_N W ≅ e · ⨁ᵢ {}^{gᵢ} V` as an isomorphism of representations is a separate
target and is not proved here.

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 6.2 and its corollaries.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §49.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

variable {k : Type u} {G : Type v} [Field k] [Group G] {N : Subgroup G} [N.Normal]

/-- A finite set meeting every left coset of `H` exactly once has `H.index` elements.  This is
`Subgroup.IsComplement.card_left` read for the transversal condition in the form
`TauCeti.clifford_restrict_character` states it, `∃! r ∈ reps, g⁻¹ * r ∈ H`; the inversion is
harmless because `H` is closed under inverses. -/
private theorem card_eq_index_of_forall_existsUnique {H : Subgroup G} {reps : Finset G}
    (h : ∀ g : G, ∃! r, r ∈ reps ∧ g⁻¹ * r ∈ H) : reps.card = H.index := by
  have hcompl : Subgroup.IsComplement (reps : Set G) (H : Set G) := by
    refine Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr fun g => ?_
    obtain ⟨r, ⟨hr, hrH⟩, huniq⟩ := h g
    refine ⟨⟨r, hr⟩, ?_, ?_⟩
    · simpa using (Subgroup.inv_mem_iff H).mpr hrH
    · rintro ⟨s, hs⟩ hsH
      have : s = r := huniq s ⟨hs, by simpa using (Subgroup.inv_mem_iff H).mpr hsH⟩
      exact Subtype.ext this
  simpa using hcompl.card_left

/-- **Clifford's dimension formula.**  The dimension of an irreducible representation `W` of a
finite group `G` is the product of the common multiplicity `e` of the irreducible constituents of
`Res_N W`, the index of the inertia group of one such constituent `V`, and the dimension of `V`.

The three factors are exactly the three pieces of Clifford's theorem: `e` is the multiplicity, the
index counts the distinct conjugates `{}^g V` occurring, and `dim V` is the size of each. -/
theorem clifford_finrank [Finite G] [IsAlgClosed k] [CharZero k] (W : FDRep k G) [Simple W] :
    ∃ (V : FDRep k N) (_ : Simple V) (e : ℕ), e ≠ 0 ∧
      Module.finrank k W = e * (inertia V).index * Module.finrank k V := by
  have hG : IsUnit (Nat.card G : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨V, hV, e, reps, he, htrans, hchar⟩ := clifford_restrict_character (N := N) hG W
  refine ⟨V, hV, e, he, ?_⟩
  have hconj : ∀ g : G, (conjNormalFDRep g V).character (1 : N) = (Module.finrank k V : k) := by
    intro g
    rw [char_conjNormalFDRep, map_one, FDRep.char_one]
  have h1 := hchar 1
  rw [OneMemClass.coe_one, FDRep.char_one] at h1
  simp only [hconj, Finset.sum_const, nsmul_eq_mul,
    card_eq_index_of_forall_existsUnique htrans] at h1
  have hcast : ((Module.finrank k W : ℕ) : k) =
      ((e * (inertia V).index * Module.finrank k V : ℕ) : k) := by
    rw [h1]
    push_cast
    ring
  exact Nat.cast_injective hcast

/-- **The divisibilities in Clifford's theorem.**  For an irreducible constituent `V` of the
restriction of an irreducible `W` to a normal subgroup, both the index of the inertia group of `V`
and the dimension of `V` divide the dimension of `W`; the index divides `[G : N]` as well.

This is the form in which the dimension formula is used.  The number of distinct conjugates
occurring in the restriction is `[G : inertia V]`, and it is constrained from two sides at once:
by the degree of `W`, through the dimension formula, and by the index of `N`, through
`TauCeti.inertia_index_dvd_index`.  Neither constraint mentions the multiplicity `e`. -/
theorem clifford_dvd_finrank [Finite G] [IsAlgClosed k] [CharZero k] (W : FDRep k G) [Simple W] :
    ∃ (V : FDRep k N) (_ : Simple V),
      (inertia V).index ∣ Module.finrank k W ∧ Module.finrank k V ∣ Module.finrank k W ∧
        (inertia V).index ∣ N.index := by
  obtain ⟨V, hV, e, -, hEq⟩ := clifford_finrank (N := N) W
  exact ⟨V, hV, ⟨e * Module.finrank k V, by rw [hEq]; ring⟩,
    ⟨e * (inertia V).index, by rw [hEq]; ring⟩, inertia_index_dvd_index V⟩

/-- **A linear character restricts to an invariant linear character.**  If `W` is one-dimensional,
then an irreducible constituent of its restriction to a normal subgroup is one-dimensional and is
fixed by the conjugation action of the whole group, its inertia group being all of `G`.

The right-hand side of the dimension formula is a product of natural numbers, so its being `1`
forces each of the three factors to be `1`. -/
theorem clifford_inertia_eq_top_of_finrank_eq_one [Finite G] [IsAlgClosed k] [CharZero k]
    (W : FDRep k G) [Simple W] (hW : Module.finrank k W = 1) :
    ∃ (V : FDRep k N) (_ : Simple V), inertia V = ⊤ ∧ Module.finrank k V = 1 := by
  obtain ⟨V, hV, e, -, hEq⟩ := clifford_finrank (N := N) W
  rw [hW] at hEq
  obtain ⟨hleft, hright⟩ := mul_eq_one.mp hEq.symm
  exact ⟨V, hV, Subgroup.index_eq_one.mp (mul_eq_one.mp hleft).2, hright⟩

end TauCeti
