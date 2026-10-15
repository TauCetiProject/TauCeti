/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.CharacterTable.Determined
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
import Mathlib.Algebra.CharP.Algebra

/-!
# Realizing a representation over a subfield from its character

Let `L / K` be an extension of fields of characteristic zero and `G` a finite group. A
representation `W` of `G` over `L` is *realized over `K`* by a representation `V` over `K` when the
scalar extension `L ⊗[K] V` is isomorphic to `W`. The character of `L ⊗[K] V` is the character of
`V` read in `L` (`FDRep.character_baseChange`), so the character of a representation realized
over `K` is a character of `G` over `K`.

For an absolutely irreducible `W`, one whose equivariant endomorphisms are the scalars, the
converse holds in the strongest form a character can give: if the character of `W` is merely an
*integer combination* of characters of representations over `K`, then `W` is realized over `K`
(`FDRep.exists_simple_nonempty_iso_baseChange_of_character_eq`). The character `χ` of `W` has
norm `⟨χ, χ⟩ = dim End(W) = 1`, the character pairing commutes with the change of coefficients
(`TauCeti.ClassFunction.characterPairing_map`), and `algebraMap K L` is injective, so the virtual
character over `K` with image `χ` also has norm `1` and degree `dim W`. By the norm-one criterion
`TauCeti.exists_simple_character_eq_of_characterPairing_self_eq_one` it is the character of an
absolutely irreducible representation `V` over `K`, and `L ⊗[K] V` has the same character as `W`,
so is isomorphic to it because representations of a finite group in characteristic zero are
determined by their characters.

Over an algebraically closed `L`, such as `ℂ`, every simple object of `FDRep L G` is absolutely
irreducible, so an irreducible complex representation is realized over a subfield `K` exactly when
its character lies in the image of the virtual characters over `K`
(`FDRep.exists_nonempty_iso_baseChange_iff_of_simple`). This is how a character identity proves a
field of definition: Brauer's theorem in its field-of-definition form writes every irreducible
complex character of `G` as an integer combination of characters of representations over the
cyclotomic field `ℚ(ζ_e)`, `e` the exponent of `G`, and the theorem here realizes the
representation itself over `ℚ(ζ_e)`.

The hypothesis is about integer combinations, and cannot be weakened to `K`-valued characters: the
two-dimensional irreducible complex representation of the quaternion group has rational character
but is not realized over `ℝ`, and only twice its character is the character of a representation
over `ℝ`.

## Main results

* `FDRep.exists_simple_nonempty_iso_baseChange_of_character_eq`: an absolutely irreducible
  representation over `L` whose character is the image of a virtual character over `K` is the
  scalar extension of an absolutely irreducible representation over `K`.
* `FDRep.exists_nonempty_iso_baseChange_iff`: an absolutely irreducible representation over `L`
  is realized over `K` exactly when its character is the image of a virtual character over `K`.
* `FDRep.exists_nonempty_iso_baseChange_iff_of_simple`: the same over an algebraically closed
  `L`, for simple objects of `FDRep L G`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups* (1977), Section 12.3.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 10.
-/

public section

open Module CategoryTheory

universe u v

namespace TauCeti

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
variable {G : Type v} [Group G] [Finite G]

/-- **An absolutely irreducible representation whose character is an integer combination of
characters over a subfield is realized over that subfield.** Let `L / K` be an extension of fields
of characteristic zero and `W` a representation of the finite group `G` over `L` whose equivariant
endomorphisms are the scalars. If the character of `W` is the image of a virtual character `f` of
`G` over `K`, then `W` is the scalar extension `L ⊗[K] V` of a simple representation `V` over `K`
whose equivariant endomorphisms are again the scalars. -/
theorem _root_.FDRep.exists_simple_nonempty_iso_baseChange_of_character_eq (W : FDRep L G)
    (hW : finrank L (W ⟶ W) = 1) {f : G → K} (hf : f ∈ virtualCharacters K G)
    (hχ : W.character = algebraMap K L ∘ f) :
    ∃ V : FDRep K G, Simple V ∧ finrank K (V ⟶ V) = 1 ∧
      Nonempty (FDRep.of (Representation.baseChange L V.ρ) ≅ W) := by
  have : Fintype G := Fintype.ofFinite G
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let _ : Invertible (Nat.card G : L) := invertibleOfNonzero (by simp)
  let F : ClassFunction K G := ⟨f, virtualCharacters_le_classFunction hf⟩
  have hF : ClassFunction.map (algebraMap K L) F = ClassFunction.ofFDRep W :=
    Subtype.ext (funext fun g => by simp [F, hχ])
  -- the virtual character `f` has norm `1`, because its image in `L` is the character of `W`
  have hnorm : ClassFunction.characterPairing F F = 1 := by
    apply (algebraMap K L).injective
    rw [← ClassFunction.characterPairing_map, hF, ClassFunction.characterPairing_ofFDRep_eq_finrank,
      hW, Nat.cast_one, map_one]
  -- and its degree is the dimension of `W`
  have hdeg : (F : G → K) 1 = finrank L W := by
    apply (algebraMap K L).injective
    have h1 := congrFun hχ 1
    rw [FDRep.char_one, Function.comp_apply] at h1
    rw [map_natCast, ← h1]
  obtain ⟨V, hV, hEnd, hVχ⟩ := exists_simple_character_eq_of_characterPairing_self_eq_one
    hf hnorm hdeg
  refine ⟨V, hV, hEnd, FDRep.nonempty_iso_of_character_eq _ _ ?_⟩
  rw [FDRep.character_baseChange, hVχ, hχ]

/-- **Realizability over a subfield is a property of the character.** For an extension `L / K` of
fields of characteristic zero, a representation `W` of a finite group over `L` whose equivariant
endomorphisms are the scalars is isomorphic to a scalar extension `L ⊗[K] V` exactly when its
character is the image of a virtual character of `G` over `K`. -/
theorem _root_.FDRep.exists_nonempty_iso_baseChange_iff (W : FDRep L G)
    (hW : finrank L (W ⟶ W) = 1) :
    (∃ V : FDRep K G, Nonempty (FDRep.of (Representation.baseChange L V.ρ) ≅ W)) ↔
      ∃ f ∈ virtualCharacters K G, W.character = algebraMap K L ∘ f := by
  refine ⟨fun ⟨V, ⟨e⟩⟩ => ⟨V.character, character_mem_virtualCharacters V, ?_⟩,
    fun ⟨f, hf, hχ⟩ => ?_⟩
  · rw [← FDRep.char_iso e, FDRep.character_baseChange]
  · obtain ⟨V, -, -, e⟩ := W.exists_simple_nonempty_iso_baseChange_of_character_eq hW hf hχ
    exact ⟨V, e⟩

/-- **An irreducible representation over an algebraically closed field is realized over a subfield
exactly when its character is the image of a virtual character over the subfield.** For instance,
an irreducible complex representation is realized over a subfield `K` of `ℂ` when its character
is an integer combination of characters of representations over `K`. -/
theorem _root_.FDRep.exists_nonempty_iso_baseChange_iff_of_simple [IsAlgClosed L]
    (W : FDRep L G) [Simple W] :
    (∃ V : FDRep K G, Nonempty (FDRep.of (Representation.baseChange L V.ρ) ≅ W)) ↔
      ∃ f ∈ virtualCharacters K G, W.character = algebraMap K L ∘ f :=
  W.exists_nonempty_iso_baseChange_iff (finrank_endomorphism_simple_eq_one L W)

end TauCeti
