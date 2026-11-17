/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.InvolutionCount
public import TauCeti.RepresentationTheory.FDRep.FrobeniusSchur

/-!
# Frobenius-Schur indicators of groups of odd order

The `n`-th power map is a bijection of a group `G` whenever `n` is coprime to `|G|`
(`Nat.Coprime.pow_left_bijective`), so the average `|G|⁻¹ ∑_g χ(gⁿ)` of an irreducible character
`χ` equals the average `|G|⁻¹ ∑_g χ(g)`, which is the dimension of the invariants
(`Representation.card_inv_mul_sum_char_eq_finrank`). An irreducible representation has a nonzero
invariant vector only when it is the trivial line, so the average is `1` for the trivial
character and `0` otherwise. This holds over any field in which `|G|` is invertible. For a group of
odd order, squaring is such a bijection, so **every nontrivial irreducible representation of a
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
(`FDRep.frobeniusSchurIndicator_fdRep`); for a group of odd order this covers the second indicator.

## Main statements

* `Representation.card_inv_mul_sum_char_pow_eq_zero_iff_of_coprime`: for an irreducible
  representation and `n` coprime to `|G|`, the average `|G|⁻¹ ∑_g χ(gⁿ)` is `0` exactly when the
  character is nontrivial.
* `Representation.frobeniusSchurIndicator_eq_zero_iff_of_odd_card`: the same criterion for the
  Frobenius-Schur indicator of an irreducible representation of a group of odd order.
* `FDRep.frobeniusSchurIndicator_fdRep_eq_zero_iff_of_coprime`: the same criterion for the
  categorical `n`-th indicator of a simple object of `FDRep k G`, for `n` coprime to `|G|`.
* `TauCeti.frobeniusSchurIndicatorRow_eq_zero_iff_of_odd_card`: a row of the character table of a
  group of odd order has indicator `0` exactly when its character is nontrivial.
* `TauCeti.sum_frobeniusSchurIndicatorRow_of_odd_card`: the unweighted sum of the row indicators of
  a group of odd order is `1`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Problem 3.16 and Chapter 4.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2 and Exercise 13.9.
-/

public section

universe u v w

namespace Representation

section Average

variable {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [Fintype G]
  [Invertible (Nat.card G : k)] [AddCommGroup V] [Module k V]

/-- **For an irreducible representation and `n` coprime to `|G|`, the average `|G|⁻¹ ∑_g χ(gⁿ)` is
`0` exactly when its character is nontrivial.** Over any field in which `|G|` is invertible. -/
theorem card_inv_mul_sum_char_pow_eq_zero_iff_of_coprime (ρ : Representation k G V)
    [ρ.IsIrreducible] {n : ℕ} (hn : (Nat.card G).Coprime n) :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character (g ^ n) = 0 ↔ ρ.character ≠ fun _ => 1 := by
  have : FiniteDimensional k V := ρ.asModuleEquiv.finiteDimensional
  -- The `n`-th power map permutes `G`, so the average of `χ(gⁿ)` is the dimension of the
  -- invariants.
  rw [Fintype.sum_bijective _ hn.pow_left_bijective _ (ρ.character ·)
    fun _ => rfl, card_inv_mul_sum_char_eq_finrank]
  refine ⟨fun h hχ => ?_, fun hχ => by_contra fun h => hχ ?_⟩
  · rw [← card_inv_mul_sum_char_eq_finrank, hχ, Finset.sum_const, Finset.card_univ,
      Fintype.card_eq_nat_card, nsmul_eq_mul, mul_one, inv_mul_cancel_of_invertible] at h
    exact one_ne_zero h
  · -- A nonzero invariant vector makes `ρ` the trivial line.
    have hne : ρ.invariants ≠ ⊥ := fun hb => h (by rw [hb, finrank_bot, Nat.cast_zero])
    funext g
    rw [‹ρ.IsIrreducible›.eq_trivial_of_invariants_ne_bot hne, char_trivial,
      ‹ρ.IsIrreducible›.finrank_eq_one_of_invariants_ne_bot hne, Nat.cast_one]

end Average

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

namespace FDRep

variable {k : Type u} {G : Type v} [Field k] [Group G] [Invertible (Nat.card G : k)]

/-- **The categorical `n`-th Frobenius-Schur indicator of a simple object of `FDRep k G`, for `n`
coprime to `|G|`, is `0` exactly when its character is nontrivial.** For a group of odd order this
applies to the second indicator (`n = 2`, via `Odd.coprime_two_right`); for instance, each of the
two nontrivial one-dimensional representations of `C₃` has categorical second indicator `0`. -/
theorem frobeniusSchurIndicator_fdRep_eq_zero_iff_of_coprime (V : FDRep k G)
    [CategoryTheory.Simple V] {n : ℕ+} (hn : (Nat.card G).Coprime n) :
    TauCeti.frobeniusSchurIndicator k V n = 0 ↔ V.character ≠ fun _ => 1 := by
  have : Finite G := Nat.finite_of_card_ne_zero fun h =>
    Invertible.ne_zero (Nat.card G : k) (by rw [h, Nat.cast_zero])
  let _ : Fintype G := Fintype.ofFinite G
  have := isIrreducible_of_simple V
  rw [frobeniusSchurIndicator_fdRep V n]
  simpa only [character_ρ, funext (character_ρ V)] using
    Representation.card_inv_mul_sum_char_pow_eq_zero_iff_of_coprime V.ρ hn

end FDRep
