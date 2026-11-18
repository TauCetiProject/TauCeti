/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Character.Basic
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.InvolutionCount

/-!
# Frobenius-Schur indicators of groups of odd order

For an irreducible character `χ` and `n` coprime to `|G|`, the average `|G|⁻¹ ∑_g χ(gⁿ)` is `1`
for the trivial character and `0` otherwise, over any field in which `|G|` is invertible
(`Representation.card_inv_mul_sum_char_pow_eq_zero_iff_of_coprime`). For a group of odd order,
`n = 2` is coprime to `|G|`, so **every nontrivial irreducible representation of a
group of odd order has Frobenius-Schur indicator `ν₂(χ) = |G|⁻¹ ∑_g χ(g²) = 0`**. Over an
algebraically closed field this means it carries no nonzero invariant bilinear form, that is, it
is of complex type (`TauCeti.Representation.frobeniusSchurIndicator_eq_zero_iff`). In a group of
odd order the identity class is the only real conjugacy class
(`TauCeti.card_realClasses_of_odd_card`), so over `ℂ` the trivial character is the only
real-valued irreducible character, a theorem of Burnside (`TauCeti.card_realValued_of_odd_card`).

The smallest example is the cyclic group `C₃`: its two nontrivial characters `χ` satisfy
`χ(g²) = χ(g)²`, and `∑_g χ(g)² = 1 + ω² + ω = 0` for a primitive cube root of unity `ω`. For a
group of odd order the unweighted sum `∑_χ ν₂(χ)` of the indicators and the degree-weighted sum
`∑_χ ν₂(χ) χ(1) = #{g : g² = 1}` are both `1`.

The categorical `n`-th Frobenius-Schur indicator of a simple object of `FDRep k G`, for the
standard pivotal structure and `n` coprime to `|G|`, takes the same values
(`FDRep.frobeniusSchurIndicator_fdRep_eq_zero_iff_of_coprime`); for a group of odd order this
covers the second indicator.

## Main statements

* `Representation.frobeniusSchurIndicator_eq_zero_iff_of_odd_card`: an irreducible
  representation of a group of odd order has Frobenius-Schur indicator `0` exactly when its
  character is nontrivial.
* `TauCeti.frobeniusSchurIndicatorRow_eq_zero_iff_of_odd_card`: a row of the character table of a
  group of odd order has indicator `0` exactly when its character is nontrivial.
* `TauCeti.sum_frobeniusSchurIndicatorRow_of_odd_card`: the unweighted sum of the row indicators of
  a group of odd order is `1`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Problem 3.16 and Chapter 4.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2 and Exercise 13.9.
-/

public section

universe v w

namespace Representation

variable {k : Type} {G : Type v} {V : Type w} [Field k] [Group G] [Fintype G]
  [Invertible (Nat.card G : k)] [AddCommGroup V] [Module k V]

/-- **An irreducible representation of a group of odd order has Frobenius-Schur indicator `0`
exactly when its character is nontrivial.** Over an algebraically closed field, every nontrivial
irreducible representation of a group of odd order is therefore of complex type
(`TauCeti.Representation.frobeniusSchurIndicator_eq_zero_iff`). -/
theorem frobeniusSchurIndicator_eq_zero_iff_of_odd_card (ρ : Representation k G V)
    [ρ.IsIrreducible] (hG : Odd (Nat.card G)) :
    TauCeti.Representation.frobeniusSchurIndicator ρ = 0 ↔ ρ.character ≠ fun _ => 1 := by
  rw [TauCeti.Representation.frobeniusSchurIndicator_def]
  exact card_inv_mul_sum_char_pow_eq_zero_iff_of_coprime ρ hG.coprime_two_right

end Representation

namespace TauCeti

section Rows

variable (k : Type) {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [Invertible (Nat.card G : k)]

/-- **A row of the character table of a group of odd order has Frobenius-Schur indicator `0`
exactly when its character is nontrivial.** -/
theorem frobeniusSchurIndicatorRow_eq_zero_iff_of_odd_card (hG : Odd (Nat.card G))
    (i : Fin (Nat.card (ConjClasses G))) :
    frobeniusSchurIndicatorRow k i = 0 ↔ irreducibleCharacter k i ≠ fun _ => 1 := by
  rw [frobeniusSchurIndicatorRow_def,
    Representation.frobeniusSchurIndicator_eq_zero_iff_of_odd_card _ hG,
    character_irreducibleRepresentation]

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

end TauCeti
