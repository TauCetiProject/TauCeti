/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
import TauCeti.RepresentationTheory.BaseChange
import TauCeti.RepresentationTheory.FDRep

/-!
# Changing coefficients of virtual characters

Changing coefficients along a field homomorphism preserves virtual characters. Consequently,
field automorphisms act on the virtual-character lattice. This is the coefficient action used to
transport automorphisms of a splitting field to complex virtual characters.

The construction works over arbitrary fields and for representations of arbitrary monoids;
changing coefficients is additive and respects scalar extension.

The preservation of virtual characters uses `Representation.character_baseChange`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups* (1977), §12.4.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 9.
-/

public section

open Module

universe u v w

namespace RingHom

open TauCeti

section Virtual

variable {k : Type u} {k' : Type w} {G : Type v} [Field k] [Field k'] [Monoid G]

/-- Changing coefficients along a field homomorphism preserves virtual characters. -/
theorem comp_mem_virtualCharacters (σ : k →+* k') {f : G → k}
    (hf : f ∈ virtualCharacters k G) : σ ∘ f ∈ virtualCharacters k' G := by
  let : Algebra k k' := σ.toAlgebra
  obtain ⟨A, B, rfl⟩ := exists_eq_character_sub_character hf
  have hchar (V : FDRep k G) :
      (FDRep.ofShrink (Representation.baseChange k' V.ρ)).character = σ ∘ V.character := by
    funext g
    rw [FDRep.character_ofShrink, Representation.character_baseChange, FDRep.character_ρ]
    rfl
  have heq : σ ∘ (A.character - B.character) =
      (FDRep.ofShrink (Representation.baseChange k' A.ρ)).character -
        (FDRep.ofShrink (Representation.baseChange k' B.ρ)).character := by
    rw [hchar, hchar]
    ext g
    exact map_sub σ _ _
  rw [heq]
  exact sub_mem (character_mem_virtualCharacters _) (character_mem_virtualCharacters _)

end Virtual

end RingHom

namespace RingEquiv

open TauCeti

variable {k : Type u} {k' : Type w} {G : Type v} [Field k] [Field k'] [Monoid G]

/-- A coefficient-field equivalence induces an additive equivalence of virtual-character
lattices, by applying it to every value. -/
def virtualCharacterEquiv (σ : k ≃+* k') :
    virtualCharacters k G ≃+ virtualCharacters k' G where
  toFun f := ⟨σ ∘ f.1, σ.toRingHom.comp_mem_virtualCharacters f.2⟩
  invFun f := ⟨σ.symm ∘ f.1, σ.symm.toRingHom.comp_mem_virtualCharacters f.2⟩
  left_inv f := by ext g; simp
  right_inv f := by ext g; simp
  map_add' f h := by ext g; simp

/-- The induced equivalence applies the coefficient equivalence pointwise. -/
@[simp]
theorem virtualCharacterEquiv_apply (σ : k ≃+* k') (f : virtualCharacters k G) (g : G) :
    (σ.virtualCharacterEquiv f).1 g = σ (f.1 g) :=
  (rfl)

/-- Inverting the coefficient equivalence inverts its action on virtual characters. -/
@[simp]
theorem virtualCharacterEquiv_symm (σ : k ≃+* k') :
    (σ.virtualCharacterEquiv (G := G)).symm = σ.symm.virtualCharacterEquiv :=
  (rfl)

end RingEquiv
