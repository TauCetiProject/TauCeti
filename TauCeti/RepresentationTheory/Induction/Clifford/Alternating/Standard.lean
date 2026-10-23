/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Inertia
public import TauCeti.RepresentationTheory.Symmetric.Standard
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Alternating.Four
import Mathlib.RepresentationTheory.FinGroupCharZero
import TauCeti.RepresentationTheory.Induction.Permutation

/-!
# The three-dimensional constituent for `A₄ ◁ S₄`

Restrict the standard representation of `S₄` to `A₄`. Its character is the fixed-point
count minus one, with values `3, -1, 0, 0` on the four conjugacy classes. The character
has norm one, so the restriction is irreducible over an algebraically closed field of
characteristic zero. It has full inertia in `S₄`, since it extends to the standard
representation there. This supplies the nonlinear fixed constituent in Clifford theory
for `A₄ ◁ S₄`, complementary to the two conjugate nontrivial linear characters.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
* J.-P. Serre, *Linear Representations of Finite Groups*, §5.2.
* Mathlib's character-norm criterion: `FDRep.simple_iff_char_is_norm_one`.
* The standard representation's augmentation character formula:
  `TauCeti.char_standardRepresentation`.
-/

public section

namespace TauCeti

open CategoryTheory Matrix

variable (k : Type*)

section Ring

variable [CommRing k]

/-- The standard representation of `S₄`, restricted to `A₄`. -/
noncomputable def alternatingGroupFourStandard : FDRep k (alternatingGroup (Fin 4)) :=
  (alternatingGroup (Fin 4)).resFDRep (FDRep.of (standardRepresentation k (Fin 4)))

/-- Identify the restricted standard representation with restriction of the ambient standard one. -/
theorem alternatingGroupFourStandard_def :
    alternatingGroupFourStandard k =
      (alternatingGroup (Fin 4)).resFDRep (FDRep.of (standardRepresentation k (Fin 4))) :=
  (rfl)

end Ring

section Field

variable [Field k]

/-- The restricted standard character is the number of fixed points minus one. -/
@[simp]
theorem character_alternatingGroupFourStandard (g : alternatingGroup (Fin 4)) :
    (alternatingGroupFourStandard k).character g =
      (Fintype.card {x : Fin 4 // g.val x = x} : k) - 1 := by
  classical
  simp [alternatingGroupFourStandard, Subgroup.resFDRep, FDRep.character_actionRes,
    FDRep.character_of, char_standardRepresentation, char_ofMulAction,
    Equiv.Perm.smul_def, Nat.card_eq_fintype_card]

/-- The restricted standard representation is three-dimensional. -/
@[simp]
theorem finrank_alternatingGroupFourStandard :
    Module.finrank k (alternatingGroupFourStandard k) = 3 := by
  -- Restriction and `FDRep.of` preserve the carrier; there is no finrank restatement for them.
  change Module.finrank k
    (augmentationSubrepresentation k (Equiv.Perm (Fin 4)) (Fin 4)).toSubmodule = 3
  simp

private theorem standardCharacter_rep (i : Fin alternatingGroupFourClassData.numClasses) :
    (Fintype.card {x : Fin 4 // (alternatingGroupFourClassData.rep i).val x = x} : ℤ) - 1 =
      ![3, -1, 0, 0] i := by
  fin_cases i <;> decide

/-- On the identity, double transpositions, and the two classes of three-cycles,
the restricted standard character takes the values `3, -1, 0, 0`. -/
@[simp high]
theorem character_alternatingGroupFourStandard_rep
    (i : Fin alternatingGroupFourClassData.numClasses) :
    (alternatingGroupFourStandard k).character (alternatingGroupFourClassData.rep i) =
      ((![3, -1, 0, 0] i : ℤ) : k) := by
  rw [character_alternatingGroupFourStandard]
  simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_one] using
    congrArg (fun z : ℤ ↦ (z : k)) (standardCharacter_rep i)

private theorem standard_norm_sum :
    ∑ g : alternatingGroup (Fin 4),
      ((Fintype.card {x : Fin 4 // g.val x = x} : ℤ) - 1) *
        ((Fintype.card {x : Fin 4 // g⁻¹.val x = x} : ℤ) - 1) = 12 := by
  decide

/-- The restricted standard representation of `A₄` is irreducible over an algebraically
closed field of characteristic zero. -/
theorem simple_alternatingGroupFourStandard (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Simple (alternatingGroupFourStandard k) := by
  classical
  apply (FDRep.simple_iff_char_is_norm_one (alternatingGroupFourStandard k)).mpr
  simp only [character_alternatingGroupFourStandard, natCard_alternatingGroup_four]
  exact_mod_cast standard_norm_sum

end Field

variable [CommRing k]

/-- The restricted standard representation of `A₄` is fixed by every conjugation from `S₄`.
Its extension to `S₄` implements the conjugation isomorphisms. -/
@[simp]
theorem inertia_alternatingGroupFourStandard :
    inertia (alternatingGroupFourStandard k) = ⊤ := by
  rw [alternatingGroupFourStandard_def, FDRep.inertia_resFDRep]

end TauCeti
