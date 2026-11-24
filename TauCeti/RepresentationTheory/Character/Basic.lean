/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.LinearAlgebra.Trace.Basic
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.Invariants

/-!
# Basic facts about characters

The trace character vanishes when the representation space is not finite-dimensional.

The trace of the action is a class function for a representation over a commutative semiring on
any additive commutative monoid (`Representation.trace_conj`). `Representation.character` and
`Representation.char_conj` ask for an additive group structure on the carrier, so this form
applies to representations such as `Representation.symmetricPower`, which is built on the
additive monoid instance of the symmetric power rather than on the one underlying its additive
group.

The `n`-th power map is a bijection of a group `G` whenever `n` is coprime to `|G|`
(`Nat.Coprime.pow_left_bijective`), so the average `|G|⁻¹ ∑_g χ(gⁿ)` of an irreducible character
`χ` equals the average `|G|⁻¹ ∑_g χ(g)`, which is the dimension of the invariants
(`Representation.card_inv_mul_sum_char_eq_finrank`). An irreducible representation has a nonzero
invariant vector only when it is the trivial line, so the average is `1` for the trivial
character and `0` otherwise (`Representation.card_inv_mul_sum_char_pow_eq_zero_iff_of_coprime`).
-/

public section

universe u v w

namespace Representation

/-- The character vanishes on a representation space that is not finite-dimensional. -/
theorem character_eq_zero_of_not_finite {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ¬ FiniteDimensional k V) :
    ρ.character = 0 := by
  funext g
  simp [character, TauCeti.LinearMap.trace_eq_zero_of_not_finite h]

/-- The trace of the action is constant on conjugacy classes. This is `Representation.char_conj`
for a representation on an additive commutative monoid. -/
theorem trace_conj {R G M : Type*} [CommSemiring R] [Group G] [AddCommMonoid M] [Module R M]
    (ρ : Representation R G M) (g h : G) :
    LinearMap.trace R M (ρ (h * g * h⁻¹)) = LinearMap.trace R M (ρ g) := by
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]

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

end Representation
