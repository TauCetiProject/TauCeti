/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.RepresentationTheory.Induction.Clifford.Decomposition
import Mathlib.GroupTheory.Complement

/-!
# The dimension form of Clifford's theorem

Let `N` be a normal subgroup of a finite group `G` and let `W` be an irreducible
finite-dimensional representation of `G` over a splitting field.  Clifford's theorem describes the
restriction of `W` to `N` as `e` copies of each of the `t` distinct conjugates of one irreducible
constituent `V`, where `t = [G : inertia V]`.  Evaluating that description at the identity turns it
into an identity of dimensions,

`dim W = e * [G : inertia V] * dim V`,

so in particular the index of the inertia group divides `dim W`.  This file proves that identity
from the character form `TauCeti.clifford_restrict_character`, and draws the arithmetic
consequence: `[G : inertia V]` divides `[G : N]` as well, so whenever `dim W` and `[G : N]` are
**coprime** the inertia group is everything and the restriction to `N` is isotypic on characters:
the character of `W` on `N` is `e` times that of `V`, and `dim W = e * dim V`.  The case
`[G : N] = 2` with `dim W` odd is recorded separately, since it is the one that arises for
`alternatingGroup α ◁ Equiv.Perm α`, complementary to the linear-character computation of
`TauCeti/RepresentationTheory/Induction/Clifford/Alternating.lean`, where the inertia group is as
*small* as Clifford theory allows.

## Main statements

* `TauCeti.finrank_eq_of_clifford_character`: **the dimension identity**, read off a Clifford
  character decomposition at the identity, over any splitting field.
* `TauCeti.clifford_restrict_finrank`: **Clifford's theorem, dimension form**, packaging the
  constituent, the multiplicity and the identity `dim W = e * [G : inertia V] * dim V` as natural
  numbers in characteristic zero.
* `TauCeti.clifford_restrict_isotypic_of_coprime`: when the dimension of `W` is **coprime** to
  `[G : N]`, the restriction of `W` to `N` has a `G`-stable irreducible constituent `V`, the
  character of `W` on `N` being `e` times that of `V` and `dim W = e * dim V`.
* `TauCeti.clifford_restrict_isotypic_of_index_two_of_odd_finrank`: the case of a subgroup of
  **index two** and an irreducible of odd dimension.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

variable {k : Type u} {G : Type v} [Field k] [Group G] {N : Subgroup G} [N.Normal]

/-- A finite set meeting every left coset of `H` exactly once has `H.index` elements.

This is Mathlib's `Subgroup.IsComplement.ncard_left` in the form in which
`TauCeti.clifford_restrict_character` delivers its transversal. -/
private theorem card_eq_index_of_forall_existsUnique {H : Subgroup G} {reps : Finset G}
    (h : ∀ g : G, ∃! r, r ∈ reps ∧ g⁻¹ * r ∈ H) : reps.card = H.index := by
  -- `g⁻¹ * r ∈ H` and `r⁻¹ * g ∈ H` are interchangeable, the two being mutually inverse.
  have hswap : ∀ a b : G, a⁻¹ * b ∈ H → b⁻¹ * a ∈ H := by
    intro a b hab
    simpa only [mul_inv_rev, inv_inv] using H.inv_mem hab
  have hc : Subgroup.IsComplement (reps : Set G) (H : Set G) := by
    rw [Subgroup.isComplement_iff_existsUnique_inv_mul_mem]
    intro g
    obtain ⟨r, ⟨hrmem, hrH⟩, huniq⟩ := h g
    refine ⟨⟨r, Finset.mem_coe.2 hrmem⟩, hswap g r hrH, ?_⟩
    rintro ⟨s, hs⟩ hsH
    exact Subtype.ext (huniq s ⟨Finset.mem_coe.1 hs, hswap s g hsH⟩)
  simpa only [Set.ncard_coe_finset] using hc.ncard_left

/-- **The dimension identity behind Clifford's theorem.**  If the character of `W` restricted to
`N` is `e` times the sum of the conjugates of `V` over a left transversal `reps` of `inertia V`,
then `dim W = e * [G : inertia V] * dim V` in the coefficient field.

This is the value of the character identity at the identity element, where every character is the
dimension of the space it comes from and the transversal contributes its cardinality
`[G : inertia V]`. -/
theorem finrank_eq_of_clifford_character {W : FDRep k G} {V : FDRep k N} {e : ℕ} {reps : Finset G}
    (htr : ∀ g : G, ∃! r, r ∈ reps ∧ g⁻¹ * r ∈ inertia V)
    (hchar : ∀ n : N, W.character (n : G) =
      (e : k) * ∑ g ∈ reps, (conjNormalFDRep g V).character n) :
    (Module.finrank k W : k) =
      (e : k) * ((inertia V).index : k) * (Module.finrank k V : k) := by
  have h1 := hchar 1
  rw [OneMemClass.coe_one, FDRep.char_one] at h1
  have hsum : ∀ g ∈ reps, (conjNormalFDRep g V).character 1 = (Module.finrank k V : k) := by
    intro g _
    rw [char_conjNormalFDRep, map_one, FDRep.char_one]
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, nsmul_eq_mul,
    card_eq_index_of_forall_existsUnique htr] at h1
  rw [h1, mul_assoc]

/-- **Clifford's theorem, dimension form.**  The dimension of an irreducible representation of `G`
is the common multiplicity `e` of the constituents of its restriction to `N`, times the number
`[G : inertia V]` of those constituents, times the dimension of one of them.

In particular the index of the inertia group of a constituent divides the dimension of `W`; that
is the arithmetic that `TauCeti.clifford_restrict_isotypic_of_coprime` exploits. -/
theorem clifford_restrict_finrank [Finite G] [IsAlgClosed k] [CharZero k] (W : FDRep k G)
    [Simple W] :
    ∃ (V : FDRep k N) (_ : Simple V) (e : ℕ), e ≠ 0 ∧
      Module.finrank k W = e * (inertia V).index * Module.finrank k V := by
  have hG : IsUnit (Nat.card G : k) :=
    isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Nat.card_pos (α := G)).ne')
  obtain ⟨V, hV, e, reps, he, htr, hchar⟩ := clifford_restrict_character (N := N) hG W
  refine ⟨V, hV, e, he, ?_⟩
  have h := finrank_eq_of_clifford_character htr hchar
  exact_mod_cast h

/-- **Clifford theory when the dimension is coprime to the index.**  If the dimension of an
irreducible `W : FDRep k G` is coprime to `[G : N]`, then `Res_N W` has an irreducible
constituent `V` that is `G`-stable, and the restriction is isotypic on characters: the character
of `W` on `N` is `e` times that of `V`, and `dim W = e * dim V`.

The number of constituents is the index `[G : inertia V]`, which divides `[G : N]` because
`N ≤ inertia V`, and divides `dim W` by the dimension identity that
`TauCeti.clifford_restrict_finrank` records.  Coprimality leaves it no value but `1`, so
`inertia V = ⊤` and there is a single constituent. -/
theorem clifford_restrict_isotypic_of_coprime [Finite G] [IsAlgClosed k] [CharZero k]
    (W : FDRep k G) [Simple W] (hcop : Nat.Coprime (Module.finrank k W) N.index) :
    ∃ (V : FDRep k N) (_ : Simple V) (e : ℕ), e ≠ 0 ∧ inertia V = ⊤ ∧
      Module.finrank k W = e * Module.finrank k V ∧
      ∀ n : N, W.character (n : G) = (e : k) * V.character n := by
  have hG : IsUnit (Nat.card G : k) :=
    isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Nat.card_pos (α := G)).ne')
  obtain ⟨V, hV, e, reps, he, htr, hchar⟩ := clifford_restrict_character (N := N) hG W
  have hdim : Module.finrank k W = e * (inertia V).index * Module.finrank k V := by
    exact_mod_cast finrank_eq_of_clifford_character htr hchar
  -- The index of the inertia group divides both the dimension and the index of `N`.
  have hdvdW : (inertia V).index ∣ Module.finrank k W :=
    ⟨e * Module.finrank k V, by rw [hdim]; ring⟩
  have hdvdN : (inertia V).index ∣ N.index := Subgroup.index_dvd_of_le (le_inertia V)
  have hone : (inertia V).index = 1 :=
    Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hdvdW hdvdN)
  have htop : inertia V = ⊤ := Subgroup.index_eq_one.1 hone
  -- A single coset means a single representative, whose conjugate of `V` is `V` again.
  have hcard : reps.card = 1 := by
    rw [card_eq_index_of_forall_existsUnique htr, hone]
  obtain ⟨r, hr⟩ := Finset.card_eq_one.1 hcard
  have hiso : conjNormalFDRep r V ≅ V :=
    (mem_inertia_iff.1 (htop ▸ Subgroup.mem_top r)).some
  refine ⟨V, hV, e, he, htop, by rw [hdim, hone, mul_one], fun n ↦ ?_⟩
  rw [hchar n, hr, Finset.sum_singleton, FDRep.char_iso hiso]

/-- **Clifford theory over a subgroup of index two, in odd dimension.**  The restriction of an
irreducible representation `W` of odd dimension to a subgroup of index two has a `G`-stable
irreducible constituent `V`: the character of `W` on `N` is `e` times that of `V`, and
`dim W = e * dim V`.

This is `TauCeti.clifford_restrict_isotypic_of_coprime` at `[G : N] = 2`, an odd natural number
being exactly one coprime to `2`.  For `alternatingGroup α ◁ Equiv.Perm α` it is the case of the
Clifford correspondence complementary to
`TauCeti.inertia_ofLinearCharacter_alternatingGroup`, where a linear character of the alternating
group has the *smallest* inertia group instead. -/
theorem clifford_restrict_isotypic_of_index_two_of_odd_finrank [Finite G] [IsAlgClosed k]
    [CharZero k] (hN : N.index = 2) (W : FDRep k G) [Simple W]
    (hodd : Odd (Module.finrank k W)) :
    ∃ (V : FDRep k N) (_ : Simple V) (e : ℕ), e ≠ 0 ∧ inertia V = ⊤ ∧
      Module.finrank k W = e * Module.finrank k V ∧
      ∀ n : N, W.character (n : G) = (e : k) * V.character n :=
  clifford_restrict_isotypic_of_coprime W (by rw [hN]; exact hodd.coprime_two_right)

end TauCeti
