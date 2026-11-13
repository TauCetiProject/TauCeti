/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Conj.OddOrder
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.RealCount
public import TauCeti.RepresentationTheory.FDRep.FrobeniusSchur

/-!
# Frobenius-Schur indicators of groups of odd order

In a group of odd order the identity class is the only real conjugacy class
(`TauCeti.card_realClasses_of_odd_card`). Over an algebraically closed field of characteristic
zero, the rows of the character table with nonzero Frobenius-Schur indicator are as many as the
real classes (`TauCeti.card_frobeniusSchurIndicatorRow_ne_zero_eq_card_realClasses`), so exactly
one row has nonzero indicator. The trivial character is such a row, with indicator `1`. Hence
**every nontrivial irreducible representation of a group of odd order has Frobenius-Schur indicator
`0`**: it is of complex type, carries no nonzero invariant bilinear form, and is not isomorphic to
its dual. Over `ℂ` the trivial character is the only real-valued irreducible character, a theorem
of Burnside.

The smallest example is the cyclic group `C₃`: its two nontrivial characters `χ` satisfy
`χ(g²) = χ(g)²`, and `∑_g χ(g)² = 1 + ω² + ω = 0` for a primitive cube root of unity `ω`. For a
group of odd order the unweighted sum `∑_χ ν₂(χ)` of the indicators and the degree-weighted sum
`∑_χ ν₂(χ) χ(1) = #{g : g² = 1}` are both `1`.

The categorical second Frobenius-Schur indicator of a simple object of `FDRep k G`, for the
standard pivotal structure, takes the same values (`FDRep.frobeniusSchurIndicator_fdRep_two`).

## Main statements

* `TauCeti.frobeniusSchurIndicatorRow_eq_zero_iff_of_odd_card`: a row of the character table of a
  group of odd order has indicator `0` exactly when its character is nontrivial.
* `TauCeti.sum_frobeniusSchurIndicatorRow_of_odd_card`: the unweighted sum of the row indicators of
  a group of odd order is `1`.
* `TauCeti.card_realValued_of_odd_card`: a group of odd order has exactly one real-valued
  irreducible complex character.
* `Representation.frobeniusSchurIndicator_eq_zero_iff_of_odd_card` and
  `FDRep.frobeniusSchurIndicator_fdRep_two_eq_zero_iff_of_odd_card`: the same criterion for an
  arbitrary irreducible representation, and for the categorical indicator of a simple object of
  `FDRep k G`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Problem 3.16 and Chapter 4.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2 and Exercise 13.9.
-/

public section

universe v w

namespace TauCeti

section Rows

variable (k : Type) {G : Type v} [Field k] [CharZero k] [IsAlgClosed k] [Group G] [Fintype G]
  [Invertible (Nat.card G : k)]

/-- **A row of the character table of a group of odd order has Frobenius-Schur indicator `0`
exactly when its character is nontrivial.** The trivial row has indicator `1`, and the rows with
nonzero indicator are as many as the real classes, of which a group of odd order has one. -/
theorem frobeniusSchurIndicatorRow_eq_zero_iff_of_odd_card (hG : Odd (Nat.card G))
    (i : Fin (Nat.card (ConjClasses G))) :
    frobeniusSchurIndicatorRow k i = 0 ↔ irreducibleCharacter k i ≠ fun _ => 1 := by
  refine ⟨fun h0 h1 => one_ne_zero
    ((frobeniusSchurIndicatorRow_eq_one_of_irreducibleCharacter_eq_one k h1).symm.trans h0),
    fun hne => by_contra fun h0 => hne ?_⟩
  obtain ⟨j, hj⟩ := exists_irreducibleCharacter_eq_one k G
  have hunique := card_frobeniusSchurIndicatorRow_ne_zero_eq_card_realClasses k G
  rw [card_realClasses_of_odd_card hG, Nat.card_eq_one_iff_unique] at hunique
  have hij : i = j := Subtype.ext_iff.mp (hunique.1.elim ⟨i, h0⟩ ⟨j, by
    rw [frobeniusSchurIndicatorRow_eq_one_of_irreducibleCharacter_eq_one k hj]
    exact one_ne_zero⟩)
  rw [hij]
  exact hj

/-- **The unweighted sum of the row indicators of a group of odd order is `1`**: the trivial row
contributes `1` and every other row `0`. This agrees with the degree-weighted sum
`∑ᵢ ν₂(χᵢ) χᵢ(1) = #{g : g² = 1} = 1` (`TauCeti.card_squareRoot_one_of_odd_card`). -/
theorem sum_frobeniusSchurIndicatorRow_of_odd_card (hG : Odd (Nat.card G)) :
    ∑ i : Fin (Nat.card (ConjClasses G)), frobeniusSchurIndicatorRow k i = 1 := by
  obtain ⟨j, hj⟩ := exists_irreducibleCharacter_eq_one k G
  rw [Finset.sum_eq_single j (fun i _ hij =>
      (frobeniusSchurIndicatorRow_eq_zero_iff_of_odd_card k hG i).mpr fun h =>
        hij (irreducibleCharacter_injective k (h.trans hj.symm)))
      (fun h => absurd (Finset.mem_univ j) h),
    frobeniusSchurIndicatorRow_eq_one_of_irreducibleCharacter_eq_one k hj]

end Rows

/-- **A group of odd order has exactly one real-valued irreducible complex character** (Burnside),
necessarily the trivial one: real-valued rows are as many as real classes. -/
theorem card_realValued_of_odd_card {G : Type v} [Group G] [Finite G] (hG : Odd (Nat.card G)) :
    Nat.card {i : Fin (Nat.card (ConjClasses G)) //
        ∀ C : ConjClasses G, (starRingEnd ℂ) (characterTable ℂ G i C) = characterTable ℂ G i C} =
      1 :=
  (card_realValued_eq_card_realClasses G).trans (card_realClasses_of_odd_card hG)

end TauCeti

namespace Representation

open TauCeti

variable {k : Type} {G : Type v} {V : Type w} [Field k] [CharZero k] [IsAlgClosed k] [Group G]
  [Fintype G] [Invertible (Nat.card G : k)] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **An irreducible representation of a group of odd order has Frobenius-Schur indicator `0`
exactly when its character is nontrivial.** So every nontrivial irreducible representation of a
group of odd order is of complex type. -/
theorem frobeniusSchurIndicator_eq_zero_iff_of_odd_card (ρ : Representation k G V)
    [ρ.IsIrreducible] (hG : Odd (Nat.card G)) :
    TauCeti.Representation.frobeniusSchurIndicator ρ = 0 ↔ ρ.character ≠ fun _ => 1 := by
  obtain ⟨i, hi⟩ := exists_irreducibleCharacter_eq k (character_mem_irreducibleCharacters ρ)
  have hrow :
      TauCeti.Representation.frobeniusSchurIndicator ρ = frobeniusSchurIndicatorRow k i := by
    rw [frobeniusSchurIndicatorRow_def, TauCeti.Representation.frobeniusSchurIndicator_def,
      TauCeti.Representation.frobeniusSchurIndicator_def, character_irreducibleRepresentation, hi]
  rw [hrow, frobeniusSchurIndicatorRow_eq_zero_iff_of_odd_card k hG, hi]

end Representation

namespace FDRep

variable {k : Type} {G : Type v} [Field k] [CharZero k] [IsAlgClosed k] [Group G] [Finite G]
  [Invertible (Nat.card G : k)]

/-- **The categorical second Frobenius-Schur indicator of a simple object of `FDRep k G`, for a
group `G` of odd order, is `0` exactly when its character is nontrivial.** For instance, each of
the two nontrivial one-dimensional representations of `C₃` has categorical indicator `0`. -/
theorem frobeniusSchurIndicator_fdRep_two_eq_zero_iff_of_odd_card (V : FDRep k G)
    [CategoryTheory.Simple V] (hG : Odd (Nat.card G)) :
    TauCeti.frobeniusSchurIndicator k V 2 = 0 ↔ V.character ≠ fun _ => 1 := by
  have := isIrreducible_of_simple V
  let _ : Fintype G := Fintype.ofFinite G
  rw [frobeniusSchurIndicator_fdRep_two, frobeniusSchurIndicator_def,
    Representation.frobeniusSchurIndicator_eq_zero_iff_of_odd_card V.ρ hG]
  -- The two spellings of the character of `V` agree pointwise by `FDRep.character_ρ`.
  rw [funext (character_ρ V)]

end FDRep
