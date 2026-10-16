/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Cyclotomic.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Realization
import TauCeti.RepresentationTheory.Induction.Brauer.Induction
import TauCeti.RepresentationTheory.Induction.Monomial
public import TauCeti.NumberTheory.Cyclotomic.Adjoin

/-!
# Cyclotomic splitting fields for finite groups

Let `G` be a finite group and `L / K` an extension of characteristic-zero fields with `L`
algebraically closed. If `K` contains a primitive root of unity of order divisible by the
exponent of `G`, every virtual character over `L` is the image of a virtual character over `K`.
Consequently every irreducible representation over `L` is the scalar extension of an absolutely
irreducible representation over `K`.

In particular, every irreducible complex representation is realized over `ℚ(ζ_e)`, where
`e = Monoid.exponent G` and `ζ_e` is any primitive `e`-th root in `ℂ`.

The character statement uses Brauer induction, the monomiality of irreducible representations
of finite elementary groups, and transitivity of induction. The induced linear characters
descend by `TauCeti.exists_virtualCharacter_indFDRep_of_isPrimitiveRoot`. Passing from that
integral character identity to an actual representation uses
`FDRep.exists_simple_nonempty_iso_baseChange_of_character_eq`; having values in `K` alone would
not suffice.

The fields and the group share a universe, as required by the existing nilpotent-group
monomiality theorem. No cyclotomic hypothesis on the whole ambient field `L` is needed.

## References

* J.-P. Serre, *Linear Representations of Finite Groups* (1977), Section 12.3.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

variable {K L G : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
variable [Group G] [Finite G] [IsAlgClosed L]

/-- **Brauer induction in its field-of-definition form.** If `K` contains a primitive root
whose order is divisible by the exponent of `G`, coefficient extension identifies its
virtual-character lattice with the entire virtual-character lattice over the algebraically
closed extension `L`. The coefficients in both lattices are integers. -/
theorem virtualCharacters_eq_map_of_isPrimitiveRoot {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hG : Monoid.exponent G ∣ n) :
    virtualCharacters L G =
      (virtualCharacters K G).map ((algebraMap K L).toAddMonoidHom.compLeft G) := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  apply le_antisymm
  · -- Brauer reduces the forward inclusion to elementary-group irreducibles.
    rw [← ClassFunction.indVirtualCharacters_eq_virtualCharacters_isElementary,
      ClassFunction.indVirtualCharacters_eq_indCharacterSpanInt
        (fun E _ => isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))]
    refine ClassFunction.indCharacterSpanInt_le_iff.mpr fun E hE d ρ hρ => ?_
    have : Group.IsNilpotent E := hE.isNilpotent
    have : Representation.IsIrreducible (FDRep.of ρ).ρ := by
      simpa only [FDRep.of_ρ'] using hρ
    have : Simple (FDRep.of ρ) := FDRep.simple_of_isIrreducible _
    obtain ⟨D, χ, hχ⟩ := (FDRep.of ρ).exists_character_eq_indClassFun_of_isNilpotent
    -- Read the subgroup of `E` as a subgroup of `G`, then induce in stages.
    obtain ⟨H, hHE, rfl⟩ : ∃ H ≤ E, H.subgroupOf E = D :=
      ⟨D.map E.subtype, Subgroup.map_subtype_le D,
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective D⟩
    let ψ : H →* Lˣ := χ.comp (Subgroup.subgroupOfEquivOfLe hHE).symm.toMonoidHom
    have hind : ((Subgroup.indClassFunction E (ClassFunction.ofCharacter ρ) : ClassFunction L G) :
        G → L) = (indFDRep (FDRep.ofLinearCharacter ψ)).character := by
      rw [← Subgroup.indClassFun_ofFDRep_character]
      have hψχ : (FDRep.ofLinearCharacter ψ).character = fun h => (ψ h : L) :=
        funext (FDRep.char_ofLinearCharacter ψ)
      rw [hψχ]
      have hρχ : ((ClassFunction.ofCharacter ρ : ClassFunction L E) : E → L) =
          (FDRep.of ρ).character := funext fun g => by simp
      have hInd : ((Subgroup.indClassFunction E (ClassFunction.ofCharacter ρ) : ClassFunction L G) :
          G → L) = Subgroup.indClassFun E (ClassFunction.ofCharacter ρ) :=
        funext (Subgroup.indClassFunction_apply E (ClassFunction.ofCharacter ρ))
      rw [hInd, hρχ, hχ]
      convert Subgroup.indClassFun_indClassFun_subgroupOf H hHE
        (ClassFunction.mem_iff.mp (MonoidHom.comp_mem_classFunction ψ Units.val)) using 1
      simp [ψ]
    obtain ⟨f, hf, hdescent⟩ := exists_virtualCharacter_indFDRep_of_isPrimitiveRoot hζ hG ψ
    rw [hind, hdescent]
    exact AddSubgroup.mem_map.mpr ⟨f, hf, rfl⟩
  · -- Genuine characters over `K` extend to genuine characters over `L`.
    apply AddSubgroup.map_le_iff_le_comap.mpr
    refine virtualCharacters_le fun V => ?_
    rw [AddSubgroup.mem_comap]
    convert character_mem_virtualCharacters (FDRep.of (Representation.baseChange L V.ρ))
      using 1
    rw [FDRep.character_baseChange]
    rfl

/-- **A field containing the requisite roots of unity realizes every irreducible
representation.** The realizing representation over `K` is simple and its endomorphisms are
exactly the scalars, so it is absolutely irreducible. -/
theorem _root_.FDRep.exists_simple_nonempty_iso_baseChange_of_isPrimitiveRoot
    (W : FDRep L G) [Simple W] {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hG : Monoid.exponent G ∣ n) :
    ∃ V : FDRep K G, Simple V ∧ Module.finrank K (V ⟶ V) = 1 ∧
      Nonempty (FDRep.of (Representation.baseChange L V.ρ) ≅ W) := by
  have hχ := character_mem_virtualCharacters W
  rw [virtualCharacters_eq_map_of_isPrimitiveRoot hζ hG] at hχ
  obtain ⟨f, hf, hχ⟩ := AddSubgroup.mem_map.mp hχ
  exact W.exists_simple_nonempty_iso_baseChange_of_character_eq
    (finrank_endomorphism_simple_eq_one L W) hf hχ.symm

/-- **The exponent cyclotomic field is a splitting field for `G`.** Every irreducible
representation over an algebraically closed extension is the scalar extension of an absolutely
irreducible representation over the cyclotomic field. -/
theorem _root_.FDRep.exists_simple_nonempty_iso_baseChange_of_isCyclotomicExtension
    [Algebra ℚ K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (W : FDRep L G) [Simple W] :
    ∃ V : FDRep K G, Simple V ∧ Module.finrank K (V ⟶ V) = 1 ∧
      Nonempty (FDRep.of (Representation.baseChange L V.ρ) ≅ W) :=
  W.exists_simple_nonempty_iso_baseChange_of_isPrimitiveRoot
    (IsCyclotomicExtension.zeta_spec (Monoid.exponent G) ℚ K) (dvd_refl _)

end TauCeti

namespace TauCeti

variable {G : Type} [Group G] [Finite G]

/-- **Every irreducible complex representation is defined over `ℚ(ζ_e)`.** Here `e` is the
exponent of `G` and the cyclotomic field is the actual intermediate field of `ℂ` generated by
any primitive `e`-th root `ζ`. -/
theorem _root_.FDRep.exists_simple_nonempty_iso_baseChange_adjoin_of_isPrimitiveRoot
    (W : FDRep ℂ G) [Simple W] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Monoid.exponent G)) :
    ∃ V : FDRep (IntermediateField.adjoin ℚ {ζ}) G,
      Simple V ∧ Module.finrank (IntermediateField.adjoin ℚ {ζ}) (V ⟶ V) = 1 ∧
        Nonempty (FDRep.of (Representation.baseChange ℂ V.ρ) ≅ W) := by
  have := hζ.isCyclotomicExtension_adjoin_singleton (K := ℚ)
  exact W.exists_simple_nonempty_iso_baseChange_of_isCyclotomicExtension

end TauCeti
