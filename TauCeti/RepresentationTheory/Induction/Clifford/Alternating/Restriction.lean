/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Alternating.Basic
public import TauCeti.RepresentationTheory.Induction.LiesOver
import TauCeti.RepresentationTheory.CharacterTable.Determined
import TauCeti.RepresentationTheory.Induction.IndexTwo
import TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity

/-!
# Restricting an induced alternating-group character

An odd permutation inverts every linear character of the alternating group. Consequently
the representation induced from a linear character `χ` has character `χ + χ⁻¹` on the
alternating group and vanishes on odd permutations. The character calculation uses the two
cosets directly, so it holds over every field, including fields of positive characteristic.

In characteristic zero, characters determine representations and the restriction is
isomorphic to `χ ⊕ χ⁻¹`. Inducing either character gives the same representation. For a
nontrivial linear character of `A₄`, this identifies the two constituents of the restriction
of the two-dimensional irreducible of `S₄`. Over an algebraically closed field of
characteristic zero, Frobenius reciprocity then shows that this is the unique irreducible
of `S₄` lying over either constituent.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
* J.-P. Serre, *Linear Representations of Finite Groups*, §7.2.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace MonoidHom

open TauCeti

universe u v

variable {k : Type u} {α : Type v} [Field k] [DecidableEq α] [Fintype α] [Nontrivial α]

/-- On the alternating subgroup, induction of a linear character has character `χ + χ⁻¹`.
This division-free formula holds over every field. -/
@[simp]
theorem character_indFDRep_ofLinearCharacter_alternatingGroup
    (χ : alternatingGroup α →* kˣ) (g : alternatingGroup α) :
    (indFDRep (FDRep.ofLinearCharacter χ)).character (g : Equiv.Perm α) =
      (χ g : k) + ((χ g)⁻¹ : kˣ) := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne α
  let s := Equiv.swap i j
  have hs : s ∉ alternatingGroup α := by
    simp [s, Equiv.Perm.mem_alternatingGroup, hij]
  have hsinv : s⁻¹ ∉ alternatingGroup α := by simpa using hs
  have hnormal : (alternatingGroup α).Normal := inferInstance
  have hconj : s⁻¹ * (g : Equiv.Perm α) * s ∈ alternatingGroup α := by
    simpa using hnormal.conj_mem g.val g.prop s⁻¹
  have heq : (⟨s⁻¹ * (g : Equiv.Perm α) * s, hconj⟩ : alternatingGroup α) =
      MulAut.conjNormal s⁻¹ g := Subtype.ext (by simp)
  rw [character_indFDRep_eq_add_of_index_two alternatingGroup.index_eq_two hs,
    Function.indTerm_one, dite_eq_left g.prop]
  simp only [Function.indTerm_apply, dite_eq_left hconj, FDRep.char_ofLinearCharacter, heq,
    χ.map_conjNormal_alternatingGroup_eq_inv hsinv]

/-- Inducing inverse linear characters of the alternating group gives the same character
on the entire symmetric group. -/
@[simp]
theorem character_indFDRep_ofLinearCharacter_alternatingGroup_inv
    (χ : alternatingGroup α →* kˣ) :
    (indFDRep (FDRep.ofLinearCharacter χ⁻¹)).character =
      (indFDRep (FDRep.ofLinearCharacter χ)).character := by
  funext g
  by_cases hg : g ∈ alternatingGroup α
  · rw [character_indFDRep_ofLinearCharacter_alternatingGroup χ⁻¹ ⟨g, hg⟩,
      character_indFDRep_ofLinearCharacter_alternatingGroup χ ⟨g, hg⟩]
    simp [add_comm]
  · simp [character_indFDRep_eq_zero_of_notMem _ hg]

variable [CharZero k]

/-- Restriction to the alternating group of the representation induced from `χ` is the
direct sum of the two linear characters `χ` and `χ⁻¹`. -/
theorem nonempty_iso_res_indFDRep_ofLinearCharacter_alternatingGroup
    (χ : alternatingGroup α →* kˣ) :
    Nonempty ((alternatingGroup α).resFDRep (indFDRep (FDRep.ofLinearCharacter χ)) ≅
      FDRep.ofLinearCharacter χ ⊞ FDRep.ofLinearCharacter χ⁻¹) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext g
  rw [FDRep.character_actionRes, FDRep.char_biprod]
  simp only [Pi.add_apply, FDRep.char_ofLinearCharacter, MonoidHom.inv_apply]
  exact character_indFDRep_ofLinearCharacter_alternatingGroup χ g

/-- In characteristic zero, either of the inverse alternating-group linear characters
induces to the same symmetric-group representation. -/
theorem nonempty_iso_indFDRep_ofLinearCharacter_alternatingGroup_inv
    (χ : alternatingGroup α →* kˣ) :
    Nonempty (indFDRep (FDRep.ofLinearCharacter χ⁻¹) ≅
      indFDRep (FDRep.ofLinearCharacter χ)) :=
  FDRep.nonempty_iso_of_character_eq _ _
    (character_indFDRep_ofLinearCharacter_alternatingGroup_inv χ)

end MonoidHom

namespace FDRep

open TauCeti

universe u

variable {k α : Type u} [Field k] [DecidableEq α] [Fintype α] [Nontrivial α]
  [CharZero k] [IsAlgClosed k]

/-- The irreducible induced from a nontrivial alternating-group linear character is the
unique symmetric-group irreducible lying over that character. For `A₄ ◁ S₄`, this recovers
the two-dimensional irreducible from either of the two nontrivial linear constituents. -/
theorem liesOver_alternatingGroup_iff_nonempty_iso_indFDRep
    (W : FDRep k (Equiv.Perm α)) [Simple W]
    {χ : alternatingGroup α →* kˣ} (hχ : χ ≠ 1) :
    W.LiesOver (alternatingGroup α).subtype (ofLinearCharacter χ) ↔
      Nonempty (indFDRep (ofLinearCharacter χ) ≅ W) := by
  have : Simple (indFDRep (ofLinearCharacter χ)) :=
    simple_indFDRep_ofLinearCharacter_alternatingGroup hχ
  constructor
  · intro h
    -- `finrank_hom_indFDRep` transports Mathlib's `Rep.indResHomEquiv`.
    have hpos : 0 < Module.finrank k (indFDRep (ofLinearCharacter χ) ⟶ W) := by
      rw [finrank_hom_indFDRep]
      exact Module.finrank_pos_iff_exists_ne_zero.mpr (liesOver_iff.mp h)
    apply (finrank_hom_simple_simple_eq_one_iff k _ _).mp
    exact Nat.le_antisymm (finrank_hom_simple_simple_le_one k _ _) hpos
  · rintro ⟨e⟩
    obtain ⟨r⟩ := χ.nonempty_iso_res_indFDRep_ofLinearCharacter_alternatingGroup
    have h : (indFDRep (ofLinearCharacter χ)).LiesOver
        (alternatingGroup α).subtype (ofLinearCharacter χ) := by
      rw [liesOver_iff]
      refine ⟨biprod.inl ≫ r.inv, ?_⟩
      intro hzero
      have hid := congrArg (fun f => f ≫ r.hom ≫ biprod.fst) hzero
      exact id_nonzero (ofLinearCharacter χ) (by simpa using hid)
    exact h.of_iso_left e

end FDRep
