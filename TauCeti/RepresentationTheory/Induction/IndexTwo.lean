/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index.Two
public import TauCeti.RepresentationTheory.Induction.LinearCharacter
import Mathlib.GroupTheory.IndexNormal

/-!
# Inducing a linear character from an inverted subgroup of index two

Let `N` be a subgroup of index two in a finite group `G` -- so `N` is normal -- and suppose a
single element `s` outside `N` conjugates `N` by inversion, `s * x * s⁻¹ = x⁻¹`.  That hypothesis
already forces every element outside `N` to conjugate by inversion as well
(`TauCeti.conj_eq_inv_of_notMem_of_index_two`).  It is the shape of a dihedral group over its
rotations and of a dicyclic group over its cyclic subgroup, and it makes the character of the
representation induced from a linear character `ψ` of `N` completely explicit: it vanishes off `N`
(`TauCeti.character_indFDRep_eq_zero_of_notMem`, which needs only normality), and on `N` it is
`ψ + ψ⁻¹` as soon as the order of `N` is invertible in the coefficient field, which the average
form of the induced character below asks for.

On `N` the average form `TauCeti.character_ind` of the induced character is the one to use.  A
linear character takes its values in the commutative group `kˣ`, so conjugating by an element of
`N` does not move it, while conjugating by an element outside `N` inverts it.  The two halves of
`G` are equally large, so each contributes `|N|` copies of one of the two values, and the factor
`|N|⁻¹` in front of the average cancels them.

## Main statements

* `TauCeti.character_indFDRep_ofLinearCharacter_eq_add_inv_of_mem_of_conj_eq_inv`: **on the
  subgroup, the character induced from a linear character is `ψ + ψ⁻¹`**, provided the order of
  the subgroup is invertible in the coefficient field.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §5.3 and §7.2.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] {N : Subgroup G} [Finite G]

/-- **On an inverted subgroup of index two, the character induced from a linear character `ψ` is
`ψ + ψ⁻¹`.**  Together with `TauCeti.character_indFDRep_eq_zero_of_notMem`, which gives the value
`0` off `N`, this determines the induced character on all of `G`.  The hypothesis `hN` asks that
the order of `N` be invertible in `k`. -/
theorem character_indFDRep_ofLinearCharacter_eq_add_inv_of_mem_of_conj_eq_inv
    (hindex : N.index = 2) {s : G} (hs : s ∉ N) (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹)
    (hN : IsUnit (Nat.card N : k)) (ψ : N →* kˣ) {g : G} (hg : g ∈ N) :
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
    · have hsplit : (⟨x⁻¹ * g * x, hconj x⟩ : N) = (⟨x, hx⟩ : N)⁻¹ * ⟨g, hg⟩ * ⟨x, hx⟩ :=
        Subtype.ext (by simp)
      rw [ite_eq_left hx, hsplit, map_mul, map_mul, map_inv, inv_mul_cancel_comm]
    · have hxinv : x⁻¹ ∉ N := fun h => hx (by simpa using N.inv_mem h)
      have hsplit : (⟨x⁻¹ * g * x, hconj x⟩ : N) = (⟨g, hg⟩ : N)⁻¹ :=
        Subtype.ext (by
          simpa using conj_eq_inv_of_notMem_of_index_two hindex hs hinv hxinv hg)
      rw [ite_eq_right hx, hsplit, map_inv]
  -- The two halves of `G` have `|N|` elements each.
  have hmemCard : (Finset.univ.filter (fun x : G => x ∈ N)).card = Nat.card N := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hnotMemCard : (Finset.univ.filter (fun x : G => ¬ x ∈ N)).card = Nat.card N := by
    simpa using card_filter_notMem_eq_card_of_index_two (N := N) hindex
  rw [character_ind hN _ g, Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_ite,
    Finset.sum_const, Finset.sum_const, hmemCard, hnotMemCard, nsmul_eq_mul, nsmul_eq_mul,
    ← mul_add, ← mul_assoc, inv_mul_cancel₀ hN.ne_zero, one_mul]

end TauCeti
