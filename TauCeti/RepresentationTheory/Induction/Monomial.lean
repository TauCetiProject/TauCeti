/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Character
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import Mathlib.GroupTheory.Nilpotent
import TauCeti.GroupTheory.Nilpotent
import TauCeti.RepresentationTheory.CharacterTable.Determined
import TauCeti.RepresentationTheory.Induction.Clifford.FullInertia
import TauCeti.RepresentationTheory.Induction.Clifford.Surjectivity

/-!
# Irreducible representations of nilpotent groups are monomial

Over an algebraically closed field of characteristic zero, every irreducible representation of a
finite nilpotent group `G` is induced from a one-dimensional representation of a subgroup: there
are a subgroup `H` and a linear character `χ : H →* kˣ` with

`W ≅ Ind_H^G χ`, equivalently `χ_W = Ind_H^G χ`.

In the classical language, finite nilpotent groups are *M-groups*.  The elementary groups of
Brauer's induction theorem are nilpotent (`TauCeti.IsElementary.isNilpotent`), so their irreducible
characters are induced from linear characters, whose values are roots of unity; this is how
Brauer's theorem is sharpened to a statement about fields of definition.

## The argument

The proof is by induction on `|G|`.  Let `W` be irreducible.

* If the operators `W.ρ g` commute pairwise, Schur's lemma makes each of them a scalar, `W` is a
  line, and its character is a linear character of `G = ⊤`
  (`FDRep.exists_character_eq_of_commute`).
* Otherwise let `K` be the kernel of `W` and `Z = upperCentralSeriesStep K` the elements acting
  centrally.  As `G` is nilpotent and `Z ≠ ⊤`, some `x` lies one step above `Z` but not in `Z`
  (`TauCeti.lt_upperCentralSeriesStep`), and the normal closure `A` of `x` acts through pairwise
  commuting operators (`TauCeti.commutator_normalClosure_singleton_le`).
* Choose an irreducible constituent `V` of `Res_A W`.  Schur's lemma makes `A` act on `V` by
  scalars.  If the inertia group of `V` were all of `G`, those scalars would be invariant under
  conjugation and `A` would act on all of `W` by them
  (`FDRep.commute_of_inertia_eq_top`); then `x` would act centrally, that is
  `x ∈ Z`.  So the inertia group `T` is proper.
* By the Clifford correspondence (`FDRep.exists_simple_liesOver_inertia_nonempty_iso_indFDRep`)
  `W ≅ Ind_T^G U` for an irreducible `U` of `T`, and `T` is nilpotent and smaller, so
  `χ_U = Ind_L^T χ` by induction.  Transitivity of induction
  (`TauCeti.indClassFun_indClassFun_subgroupOf`) finishes.

## Main statements

* `FDRep.exists_character_eq_indClassFun_of_isNilpotent`: the character of an irreducible
  representation of a finite nilpotent group is induced from a linear character of a subgroup.
* `FDRep.exists_nonempty_iso_indFDRep_ofLinearCharacter_of_isNilpotent`: the representation
  itself is induced from a one-dimensional representation of a subgroup.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §8.5.
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 6.
-/

public section

open CategoryTheory
open scoped commutatorElement

universe u

namespace FDRep

open TauCeti

variable {k G : Type u} [Field k] [Group G]

/-- **The character of an irreducible representation of a finite nilpotent group is monomial.**
Over an algebraically closed field of characteristic zero, for every irreducible representation
`W` of a finite nilpotent group `G` there are a subgroup `H` and a linear character `χ` of `H`
with `χ_W = Ind_H^G χ`. -/
theorem exists_character_eq_indClassFun_of_isNilpotent [IsAlgClosed k] [CharZero k] [Finite G]
    [Group.IsNilpotent G] (W : FDRep k G) [Simple W] :
    ∃ (H : Subgroup G) (χ : H →* kˣ), W.character = indClassFun H fun h => (χ h : k) := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.card G = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  by_cases hcomm : ∀ g h : G, Commute (W.ρ g) (W.ρ h)
  · obtain ⟨χ, hχ⟩ := exists_character_eq_of_commute W hcomm
    refine ⟨⊤, χ.comp (⊤ : Subgroup G).subtype, hχ.trans (funext fun g => ?_)⟩
    rw [indClassFun_top (MonoidHom.comp_mem_classFunction _ Units.val)]
    rfl
  have hW := FDRep.isIrreducible_of_simple W
  have : Nontrivial W := hW.nontrivial
  -- `Z`, the elements acting centrally, is proper; `x` lies one step above it.
  have hZ : Subgroup.upperCentralSeriesStep W.ρ.ker ≠ ⊤ := fun h =>
    hcomm fun g h' => W.ρ.commutatorElement_mem_ker_iff.mp <|
      (Subgroup.mem_upperCentralSeriesStep _ g).mp (h ▸ Subgroup.mem_top g) h'
  obtain ⟨x, hx, hxZ⟩ := IsConcreteLE.exists_of_lt (lt_upperCentralSeriesStep hZ)
  -- The normal closure `A` of `x` acts through commuting operators.
  let A := Subgroup.normalClosure ({x} : Set G)
  have hA (a b : A) : Commute (W.ρ a) (W.ρ b) :=
    W.ρ.commutatorElement_mem_ker_iff.mp <|
      commutator_normalClosure_singleton_le hx (Subgroup.commutator_mem_commutator a.2 b.2)
  obtain ⟨σ, hσ⟩ := Representation.exists_isAtom (W.ρ.comp A.subtype)
  let V : FDRep k A := FDRep.of σ.toRepresentation
  have hV : Representation.IsIrreducible V.ρ :=
    Representation.isIrreducible_toRepresentation_of_isAtom hσ
  have : Simple V := FDRep.simple_of_isIrreducible V
  -- The inertia group of `V` is proper, as otherwise `x` would act centrally.
  have hT : inertia V ≠ ⊤ := fun hT => hxZ fun g => W.ρ.commutatorElement_mem_ker_iff.mpr <|
    commute_of_inertia_eq_top W hA hσ hT ⟨x, Subgroup.subset_normalClosure rfl⟩ g
  -- Clifford: `W` is induced from an irreducible representation of the inertia group.
  obtain ⟨U, hU, -, ⟨e⟩⟩ := exists_simple_liesOver_inertia_nonempty_iso_indFDRep V W
    (liesOver_of_ne_bot W A.subtype hσ.1)
  have hcard : Nat.card (inertia V) < n :=
    hn ▸ (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hT)).trans_eq Subgroup.card_top
  obtain ⟨L₀, χ, hχ⟩ := ih _ hcard U rfl
  obtain ⟨L, hLT, rfl⟩ : ∃ L ≤ inertia V, L.subgroupOf (inertia V) = L₀ :=
    ⟨L₀.map (inertia V).subtype, Subgroup.map_subtype_le L₀,
      Subgroup.comap_map_eq_self_of_injective (inertia V).subtype_injective L₀⟩
  refine ⟨L, χ.comp (Subgroup.subgroupOfEquivOfLe hLT).symm.toMonoidHom, ?_⟩
  rw [← char_iso e, ← indClassFun_ofFDRep_character, hχ,
    ← indClassFun_indClassFun_subgroupOf hLT (MonoidHom.comp_mem_classFunction _ Units.val)]
  simp

/-- **Finite nilpotent groups are M-groups.**  Over an algebraically closed field of
characteristic zero, every irreducible representation of a finite nilpotent group is induced from
a one-dimensional representation of a subgroup. -/
theorem exists_nonempty_iso_indFDRep_ofLinearCharacter_of_isNilpotent [IsAlgClosed k] [CharZero k]
    [Finite G] [Group.IsNilpotent G] (W : FDRep k G) [Simple W] :
    ∃ (H : Subgroup G) (χ : H →* kˣ), Nonempty (W ≅ indFDRep (ofLinearCharacter χ)) := by
  obtain ⟨H, χ, hχ⟩ := exists_character_eq_indClassFun_of_isNilpotent W
  refine ⟨H, χ, nonempty_iso_of_character_eq _ _ ?_⟩
  rw [hχ, ← indClassFun_ofFDRep_character]
  exact congrArg (indClassFun H) (funext fun h => (char_ofLinearCharacter χ h).symm)

end FDRep
