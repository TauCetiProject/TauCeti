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

Squaring is a bijection of a group `G` of odd order (`Nat.Coprime.pow_left_bijective`), so the
Frobenius-Schur indicator `ν₂(χ) = |G|⁻¹ ∑_g χ(g²)` of an irreducible character `χ` equals the
average `|G|⁻¹ ∑_g χ(g)`, which is the pairing of `χ` with the trivial character. By row
orthogonality (`TauCeti.card_inv_mul_sum_characterTable_mul_characterTable_inv`) it is `1` for the
trivial character and `0` otherwise. This holds over any algebraically closed field in which `|G|`
is invertible. Hence **every nontrivial irreducible representation of a group of odd order has
Frobenius-Schur indicator `0`**: it carries no nonzero invariant bilinear form. In a group of odd
order the identity class is the only real conjugacy class (`TauCeti.card_realClasses_of_odd_card`),
so over `ℂ` the trivial character is the only real-valued irreducible character, a theorem of
Burnside.

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

variable (k : Type) {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [Invertible (Nat.card G : k)]

/-- **A row of the character table of a group of odd order has Frobenius-Schur indicator `0`
exactly when its character is nontrivial.** Squaring permutes the group, so the indicator of a row
is its average, which by row orthogonality is `1` on the trivial row and `0` on every other row. -/
theorem frobeniusSchurIndicatorRow_eq_zero_iff_of_odd_card (hG : Odd (Nat.card G))
    (i : Fin (Nat.card (ConjClasses G))) :
    frobeniusSchurIndicatorRow k i = 0 ↔ irreducibleCharacter k i ≠ fun _ => 1 := by
  obtain ⟨j, hj⟩ := exists_irreducibleCharacter_eq_one k G
  -- Squaring permutes `G`, so the indicator is the pairing of the row with the trivial row `j`.
  have hrow : frobeniusSchurIndicatorRow k i = if i = j then 1 else 0 := by
    rw [frobeniusSchurIndicatorRow_eq_inv_mul_sum_characterTable,
      ← card_inv_mul_sum_characterTable_mul_characterTable_inv i j]
    congr 1
    exact Fintype.sum_bijective _ hG.coprime_two_right.pow_left_bijective _ _ fun g => by
      simp only [characterTable_apply, hj, mul_one]
  rw [hrow, ← hj, (irreducibleCharacter_injective k).ne_iff]
  split_ifs with hij <;> simp [hij]

/-- **The unweighted sum of the row indicators of a group of odd order is `1`**: the trivial row
contributes `1` and every other row `0`. This agrees with the degree-weighted sum
`∑ᵢ ν₂(χᵢ) χᵢ(1) = #{g : g² = 1} = 1` (`TauCeti.card_squareRoot_of_odd_card`). -/
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

variable {k : Type} {G : Type v} {V : Type w} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [Invertible (Nat.card G : k)] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

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

variable {k : Type} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Invertible (Nat.card G : k)]

/-- **The categorical second Frobenius-Schur indicator of a simple object of `FDRep k G`, for a
group `G` of odd order, is `0` exactly when its character is nontrivial.** For instance, each of
the two nontrivial one-dimensional representations of `C₃` has categorical indicator `0`. -/
theorem frobeniusSchurIndicator_fdRep_two_eq_zero_iff_of_odd_card (V : FDRep k G)
    [CategoryTheory.Simple V] (hG : Odd (Nat.card G)) :
    TauCeti.frobeniusSchurIndicator k V 2 = 0 ↔ V.character ≠ fun _ => 1 := by
  have : Finite G := Nat.finite_of_card_ne_zero hG.pos.ne'
  let _ : Fintype G := Fintype.ofFinite G
  have := isIrreducible_of_simple V
  rw [frobeniusSchurIndicator_fdRep_two, frobeniusSchurIndicator_def,
    Representation.frobeniusSchurIndicator_eq_zero_iff_of_odd_card V.ρ hG]
  -- The two spellings of the character of `V` agree pointwise by `FDRep.character_ρ`.
  rw [funext (character_ρ V)]

end FDRep
