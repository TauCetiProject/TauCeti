/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LinearCharacter.Descent
public import TauCeti.RepresentationTheory.Induction.LinearCharacter
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.CharacterTable.Determined
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Cyclotomic realization of induced linear characters

Let `G` be a finite group and `L / K` an extension of fields of characteristic zero. If `K`
contains a primitive root of unity of order the exponent of `G`, every representation induced
from a linear character of a subgroup is realized over `K`. More precisely, descend the linear
character to `K`, induce it there, and extend scalars to recover the original representation.

The character comparison is valid in every characteristic: induction commutes with the map of
coefficients because its coset formula has no division. Characteristic zero enters only when
turning equality of characters into an isomorphism of representations.

In particular, take `K = ℚ(ζ_e)` with `e` the exponent of `G` and `L = ℂ`. This realizes the
monomial representations used in Brauer's field-of-definition theorem. The statements here do
not assert that all representations are monomial.

## References

* J.-P. Serre, *Linear Representations of Finite Groups* (1977), Section 12.3.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {G : Type v} [Group G] {S : Subgroup G} [S.FiniteIndex]

/-- Changing the coefficients of a linear character and inducing it gives the image of its
induced character. This comparison uses no division by the subgroup order. -/
@[simp]
theorem character_indFDRep_ofLinearCharacter_map (ψ : S →* Kˣ) :
    (indFDRep
      (FDRep.ofLinearCharacter ((Units.map (algebraMap K L : K →* L)).comp ψ))).character =
      algebraMap K L ∘ (indFDRep (FDRep.ofLinearCharacter ψ)).character := by
  rw [← Subgroup.indClassFun_ofFDRep_character, ← Subgroup.indClassFun_ofFDRep_character]
  have hχ :
      (FDRep.ofLinearCharacter ((Units.map (algebraMap K L : K →* L)).comp ψ)).character =
      algebraMap K L ∘ (FDRep.ofLinearCharacter ψ).character := by
    funext g
    simp
  rw [hχ]
  exact Subgroup.indClassFun_comp S (algebraMap K L).toAddMonoidHom _

/-- In characteristic zero, extending scalars after inducing a linear character gives the
representation induced from the extended linear character. -/
theorem nonempty_iso_baseChange_indFDRep_ofLinearCharacter [CharZero K] [Finite G]
    (ψ : S →* Kˣ) :
    Nonempty (FDRep.of (Representation.baseChange L
      (indFDRep (FDRep.ofLinearCharacter ψ)).ρ) ≅
      indFDRep (FDRep.ofLinearCharacter ((Units.map (algebraMap K L : K →* L)).comp ψ))) := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  apply FDRep.nonempty_iso_of_character_eq
  rw [FDRep.character_baseChange, character_indFDRep_ofLinearCharacter_map]

/-- If the base field contains a primitive root of an order divisible by the exponent of `G`,
then a representation induced from a linear character is realized over that field. The realizing
representation is explicitly the induction of the descended linear character. -/
theorem exists_nonempty_iso_baseChange_indFDRep_of_isPrimitiveRoot [CharZero K] [Finite G]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hG : Monoid.exponent G ∣ n) (χ : S →* Lˣ) :
    ∃ ψ : S →* Kˣ,
      Nonempty (FDRep.of (Representation.baseChange L
        (indFDRep (FDRep.ofLinearCharacter ψ)).ρ) ≅ indFDRep (FDRep.ofLinearCharacter χ)) := by
  have hS : Monoid.exponent S ∣ n :=
    (Monoid.exponent_dvd_of_monoidHom S.subtype S.subtype_injective).trans hG
  obtain ⟨ψ, hψ, -⟩ := χ.existsUnique_unitsMap_comp_eq_of_isPrimitiveRoot hζ hS
  rw [← hψ]
  exact ⟨ψ, nonempty_iso_baseChange_indFDRep_ofLinearCharacter ψ⟩

/-- Every induced linear character over an extension is the image of a virtual character over
any base field containing the requisite primitive root. This is the coefficient input to the
field-of-definition form of Brauer induction, and is valid in every characteristic. -/
theorem exists_virtualCharacter_indFDRep_of_isPrimitiveRoot
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hG : Monoid.exponent G ∣ n) (χ : S →* Lˣ) :
    ∃ f ∈ virtualCharacters K G,
      (indFDRep (FDRep.ofLinearCharacter χ)).character = algebraMap K L ∘ f := by
  have hS : Monoid.exponent S ∣ n :=
    (Monoid.exponent_dvd_of_monoidHom S.subtype S.subtype_injective).trans hG
  obtain ⟨ψ, hψ, -⟩ := χ.existsUnique_unitsMap_comp_eq_of_isPrimitiveRoot hζ hS
  refine ⟨(indFDRep (FDRep.ofLinearCharacter ψ)).character,
    character_mem_virtualCharacters _, ?_⟩
  rw [← hψ, character_indFDRep_ofLinearCharacter_map]

/-- The exponent cyclotomic field realizes every representation induced from a linear character
of a subgroup of `G`. In particular the ambient extension can be the complex numbers. -/
theorem exists_nonempty_iso_baseChange_indFDRep_of_isCyclotomicExtension [CharZero K] [Finite G]
    [Algebra ℚ K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K] (χ : S →* Lˣ) :
    ∃ ψ : S →* Kˣ,
      Nonempty (FDRep.of (Representation.baseChange L
        (indFDRep (FDRep.ofLinearCharacter ψ)).ρ) ≅ indFDRep (FDRep.ofLinearCharacter χ)) :=
  exists_nonempty_iso_baseChange_indFDRep_of_isPrimitiveRoot
    (IsCyclotomicExtension.zeta_spec (Monoid.exponent G) ℚ K) (dvd_refl _) χ

end TauCeti
