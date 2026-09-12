/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IndexNormal
public import TauCeti.RepresentationTheory.Induction.LinearCharacter

/-!
# Inducing a linear character from an inverted subgroup of index two

Let `N` be a subgroup of index two in a finite group `G` -- so `N` is normal -- and suppose every
element outside `N` conjugates `N` by inversion, `s * x * s⁻¹ = x⁻¹`.  That is the shape of a
dihedral group over its rotations and of a dicyclic group over its cyclic subgroup, and it makes
the character of the representation induced from a linear character `ψ` of `N` completely explicit:
it vanishes off `N`, and on `N` it is `ψ + ψ⁻¹`.

The vanishing is general, and is recorded for an arbitrary representation of an arbitrary normal
subgroup: the coset formula `TauCeti.character_indFDRep_sum_quotient` keeps only the cosets that
`g` fixes by conjugation, and normality makes a conjugate `t⁻¹ g t` lie in `N` exactly when `g`
does, so an element outside `N` contributes nothing at all.

On `N` the average form `TauCeti.character_ind` of the induced character is the one to use.  A
linear character takes its values in the commutative group `kˣ`, so conjugating by an element of
`N` does not move it, while conjugating by an element outside `N` inverts it.  The two halves of
`G` are equally large, so each contributes `|N|` copies of one of the two values, and the factor
`|N|⁻¹` in front of the average cancels them.

## Main statements

* `TauCeti.character_indFDRep_eq_zero_of_notMem`: **an induced character vanishes off a normal
  subgroup**, for any representation of it.
* `TauCeti.character_indFDRep_ofLinearCharacter_of_conj_eq_inv`: **on the subgroup, the character
  induced from a linear character is `ψ + ψ⁻¹`.**

## References

* [Induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md),
  Layer 2, "induced characters".
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §5.3 and §7.2.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] {N : Subgroup G}

/-- **An induced character vanishes outside a normal subgroup.**  Each summand of the coset formula
`TauCeti.character_indFDRep_sum_quotient` asks whether a conjugate `t⁻¹ g t` lies in `N`, and for a
normal `N` that happens only when `g` itself does. -/
theorem character_indFDRep_eq_zero_of_notMem [N.Normal] [N.FiniteIndex] (A : FDRep k N) {g : G}
    (hg : g ∉ N) : (indFDRep (k := k) (G := G) A).character g = 0 := by
  classical
  rw [character_indFDRep_sum_quotient]
  refine Finset.sum_eq_zero fun t _ => dite_eq_right fun hmem => hg ?_
  simpa [mul_assoc] using ‹N.Normal›.conj_mem _ hmem (Quotient.out t)

variable [Finite G]

/-- **On an inverted subgroup of index two, the character induced from a linear character is
`ψ + ψ⁻¹`.**  In the average form of the induced character the conjugating elements of `N`
contribute `ψ g`, because `kˣ` is commutative, and those outside contribute `(ψ g)⁻¹`, because they
conjugate by inversion; the two halves of `G` have `|N|` elements each, which the factor `|N|⁻¹`
cancels. -/
theorem character_indFDRep_ofLinearCharacter_of_conj_eq_inv (hindex : N.index = 2)
    (hinv : ∀ s : G, s ∉ N → ∀ x : G, x ∈ N → s * x * s⁻¹ = x⁻¹) (hN : IsUnit (Nat.card N : k))
    (ψ : N →* kˣ) {g : G} (hg : g ∈ N) :
    (indFDRep (k := k) (G := G) (FDRep.ofLinearCharacter ψ)).character g =
      (ψ ⟨g, hg⟩ : k) + ((ψ ⟨g, hg⟩)⁻¹ : kˣ) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hnormal : N.Normal := Subgroup.normal_of_index_eq_two hindex
  have hconj : ∀ x : G, x⁻¹ * g * x ∈ N := fun x => by
    simpa using hnormal.conj_mem _ hg x⁻¹
  -- Each summand of the average takes one of two values, according to the half of `G` that the
  -- conjugating element lies in.
  have hterm : ∀ x : G,
      (if h : x⁻¹ * g * x ∈ N then
          (FDRep.ofLinearCharacter (k := k) ψ).character ⟨x⁻¹ * g * x, h⟩ else 0) =
        if x ∈ N then (ψ ⟨g, hg⟩ : k) else ((ψ ⟨g, hg⟩)⁻¹ : kˣ) := by
    intro x
    rw [dite_eq_left (hconj x), FDRep.char_ofLinearCharacter]
    by_cases hx : x ∈ N
    · have hsplit : (⟨x⁻¹ * g * x, hconj x⟩ : N) = (⟨x, hx⟩ : N)⁻¹ * ⟨g, hg⟩ * ⟨x, hx⟩ := rfl
      rw [ite_eq_left hx, hsplit, map_mul, map_mul, map_inv, inv_mul_cancel_comm]
    · have hxinv : x⁻¹ ∉ N := fun h => hx (by simpa using N.inv_mem h)
      have hsplit : (⟨x⁻¹ * g * x, hconj x⟩ : N) = (⟨g, hg⟩ : N)⁻¹ :=
        Subtype.ext (by simpa using hinv x⁻¹ hxinv g hg)
      rw [ite_eq_right hx, hsplit, map_inv]
  -- The two halves of `G` have `|N|` elements each.
  have hmemCard : (Finset.univ.filter (fun x : G => x ∈ N)).card = Nat.card N := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hnotMemCard : (Finset.univ.filter (fun x : G => ¬ x ∈ N)).card = Nat.card N := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
      (p := fun x : G => x ∈ N)
    have hcard : (Finset.univ : Finset G).card = Nat.card N * 2 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.card_mul_index N, hindex]
    omega
  rw [character_ind hN _ g, Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_ite,
    Finset.sum_const, Finset.sum_const, hmemCard, hnotMemCard, nsmul_eq_mul, nsmul_eq_mul,
    ← mul_add, ← mul_assoc, inv_mul_cancel₀ hN.ne_zero, one_mul]

end TauCeti
