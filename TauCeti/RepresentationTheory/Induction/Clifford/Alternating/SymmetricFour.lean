/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Alternating.Classification
public import TauCeti.RepresentationTheory.Induction.Clifford.Alternating.FixedConstituents
public import TauCeti.RepresentationTheory.Induction.Clifford.Alternating.Restriction
import TauCeti.RepresentationTheory.Irreducible
import Mathlib.Algebra.Group.Hom.Instances

/-!
# The five irreducible representations of `S₄` via `A₄`

Over an algebraically closed field of characteristic zero, every simple representation of `S₄`
is trivial, sign, induced from a nontrivial linear character of `A₄`, standard, or sign-twisted
standard. Any choice of the nontrivial linear character gives the same list up to isomorphism.

This assembles the classification of `A₄` with the recovery theorems for representations lying
above each of its constituents. A simple `S₄` representation has a simple constituent on
restriction to `A₄`; the three possible kinds of constituent recover the two one-dimensional
representations, the induced two-dimensional representation, and the two standard extensions.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
* J.-P. Serre, *Linear Representations of Finite Groups*, §5.2 and Chapter 8.
* The constituent classification `FDRep.simple_alternatingGroupFour_iff` and the recovery
  criteria `FDRep.liesOver_trivial_alternatingGroup_iff`,
  `FDRep.liesOver_alternatingGroup_iff_nonempty_iso_indFDRep`, and
  `FDRep.liesOver_alternatingGroupFourStandard_iff`.
-/

public section

open CategoryTheory

namespace FDRep

open TauCeti

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/-- A representation of `S₄` is simple exactly when it is isomorphic to the trivial or sign
representation, the representation induced from a nontrivial linear character `χ` of `A₄`,
the standard representation, or its sign twist. -/
theorem simple_symmetricGroupFour_iff (W : FDRep k (Equiv.Perm (Fin 4)))
    {χ : alternatingGroup (Fin 4) →* kˣ} (hχ : χ ≠ 1) :
    Simple W ↔
      Nonempty (ofLinearCharacter (1 : Equiv.Perm (Fin 4) →* kˣ) ≅ W) ∨
      Nonempty (ofLinearCharacter (signLinearCharacter k (Fin 4)) ≅ W) ∨
      Nonempty (indFDRep (ofLinearCharacter χ) ≅ W) ∨
      Nonempty (FDRep.of (standardRepresentation k (Fin 4)) ≅ W) ∨
      Nonempty (FDRep.of (Representation.charTwist (signLinearCharacter k (Fin 4))
        (standardRepresentation k (Fin 4))) ≅ W) := by
  have hstandard : Simple (FDRep.of (standardRepresentation k (Fin 4))) := by
    apply (simple_iff_isIrreducible _).mpr
    rw [of_ρ']
    exact isIrreducible_standardRepresentation (by norm_num) (Or.inr (by norm_num))
  have htwist : Simple (FDRep.of (Representation.charTwist (signLinearCharacter k (Fin 4))
      (standardRepresentation k (Fin 4)))) := by
    apply (simple_iff_isIrreducible _).mpr
    rw [of_ρ']
    exact (Representation.isIrreducible_charTwist_iff _ _).mpr
      (by simpa only [of_ρ'] using
        (isIrreducible_of_simple (FDRep.of (standardRepresentation k (Fin 4)))))
  have hind : Simple (indFDRep (ofLinearCharacter χ)) :=
    simple_indFDRep_ofLinearCharacter_alternatingGroup hχ
  constructor
  · intro hW
    have : Nontrivial W := (isIrreducible_of_simple W).nontrivial
    obtain ⟨σ, hσ, hirr⟩ := Representation.exists_isIrreducible_subrepresentation
      (W.ρ.comp (alternatingGroup (Fin 4)).subtype)
    have : Simple (FDRep.of σ.toRepresentation) := by
      apply (simple_iff_isIrreducible _).mpr
      rw [of_ρ']
      exact hirr
    have hlies := liesOver_of_ne_bot W (alternatingGroup (Fin 4)).subtype hσ
    rcases (simple_alternatingGroupFour_iff (FDRep.of σ.toRepresentation) hχ).mp
      inferInstance with h | h | h | h
    · rcases (liesOver_trivial_alternatingGroup_iff W).mp (hlies.of_iso_right h.some) with
        h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl
        ((liesOver_alternatingGroup_iff_nonempty_iso_indFDRep W hχ).mp
          (hlies.of_iso_right h.some))))
    · have hi := (liesOver_alternatingGroup_iff_nonempty_iso_indFDRep W
        ((inv_ne_one (a := χ)).mpr hχ)).mp (hlies.of_iso_right h.some)
      exact Or.inr (Or.inr (Or.inl ⟨
        (χ.nonempty_iso_indFDRep_ofLinearCharacter_alternatingGroup_inv.some).symm ≪≫ hi.some⟩))
    · rcases (liesOver_alternatingGroupFourStandard_iff W).mp
        (hlies.of_iso_right h.some) with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro (h | h | h | h | h)
    · exact Simple.of_iso h.some.symm
    · exact Simple.of_iso h.some.symm
    · exact Simple.of_iso h.some.symm
    · exact Simple.of_iso h.some.symm
    · exact Simple.of_iso h.some.symm

end FDRep
