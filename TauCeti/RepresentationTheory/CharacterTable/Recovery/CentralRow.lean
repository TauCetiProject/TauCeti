/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Eigenrow
public import TauCeti.RepresentationTheory.CharacterTable.Recovery

/-!
# The degree identity of a central character row

With `n = |G|` and `s_C = |C|`, a row `Ω = (C ↦ ωᵪ(K_C))` of the central character table satisfies
`T = ∑_C (n / s_C) Ω(C) Ω(C⁻¹) = (n / χ(1)) ^ 2`, where each quotient `n / s_C` is exact. This is
Dixon's degree formula `TauCeti.Representation.finrank_sq_mul_classRowNorm_eq_card` with the
denominators of the class sizes cleared. The equation `m ^ 2 * T = n ^ 2` has the degree as its only
natural-number solution, so the row determines the degree without reference to the ordinary
character table.

## Main statements

* `TauCeti.characterDegree_sq_mul_sum_centralCharacterTable_eq_card_sq`: the division-free degree
  identity.
* `TauCeti.sum_centralRow_eq_card_div_sq`: the degree identity for a descended row.
* `TauCeti.natCast_sq_mul_sum_centralRow_eq_iff`: the degree is the unique solution.

## References

* W. Fulton, J. Harris, *Representation Theory*, Theorem 2.12.
* J. D. Dixon, *High speed computation of group characters* (1967).
-/

public section

open Module

namespace TauCeti

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- **The division-free degree identity.** Over any algebraically closed field in which `|G|` is
invertible, `χ(1) ^ 2 * ∑_C (|G| / |C|) Ω(C) Ω(C⁻¹) = |G| ^ 2`, the quotients being exact natural
number divisions. -/
theorem characterDegree_sq_mul_sum_centralCharacterTable_eq_card_sq {k : Type*} [Field k]
    [IsAlgClosed k] [Invertible (Nat.card G : k)] (i : Fin (Nat.card (ConjClasses G))) :
    (characterDegree k i : k) ^ 2 * ∑ C : ConjClasses G,
        ((Nat.card G / Nat.card C.carrier : ℕ) : k) * centralCharacterTable k G i C *
          centralCharacterTable k G i C⁻¹ =
      (Nat.card G : k) ^ 2 := by
  have hG : (Nat.card G : k) ≠ 0 := Invertible.ne_zero _
  have hrow : centralCharacterTable k G i =
      classSumRow (Representation.centralCharacter (irreducibleRepresentation k i)) := by
    funext C
    rw [centralCharacterTable_apply, classSumRow_apply]
  have hsum : ∑ C : ConjClasses G,
      ((Nat.card G / Nat.card C.carrier : ℕ) : k) * centralCharacterTable k G i C *
        centralCharacterTable k G i C⁻¹ =
      (Nat.card G : k) * classRowNorm (centralCharacterTable k G i) := by
    rw [classRowNorm_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun C _ ↦ ?_
    rw [Nat.cast_div (ConjClasses.card_carrier_dvd_card C)
      (ConjClasses.card_carrier_cast_ne_zero C hG)]
    ring
  have hrec := Representation.finrank_sq_mul_classRowNorm_eq_card
    (irreducibleRepresentation k (G := G) i)
  rw [← hrow, finrank_fin_fun] at hrec
  rw [hsum, mul_left_comm, hrec, sq]

variable {K : Type*} [Field K] [Algebra K ℂ] {i : Fin (Nat.card (ConjClasses G))}
  {w : ConjClasses G → K}

/-- **The degree identity for a descended row.** In a field `K` embedded in `ℂ`, a row descending a
row of the central character table satisfies
`∑_C (|G| / |C|) w(C) w(C⁻¹) = (|G| / χ(1)) ^ 2`. -/
theorem sum_centralRow_eq_card_div_sq
    (hw : ∀ C, algebraMap K ℂ (w C) = centralCharacterTable ℂ G i C) :
    ∑ C : ConjClasses G, ((Nat.card G / Nat.card C.carrier : ℕ) : K) * w C * w C⁻¹ =
      ((Nat.card G : K) / (characterDegree ℂ i : K)) ^ 2 := by
  have hd : (characterDegree ℂ i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (characterDegree_pos ℂ i).ne'
  apply (algebraMap K ℂ).injective
  simp only [map_sum, map_mul, map_natCast, map_pow, map_div₀, hw]
  rw [div_pow, eq_div_iff (pow_ne_zero 2 hd), mul_comm]
  exact characterDegree_sq_mul_sum_centralCharacterTable_eq_card_sq i

/-- **The row determines the degree.** The degree `χ(1)` is the unique natural number `m` with
`m ^ 2 * ∑_C (|G| / |C|) w(C) w(C⁻¹) = |G| ^ 2`. -/
theorem natCast_sq_mul_sum_centralRow_eq_iff
    (hw : ∀ C, algebraMap K ℂ (w C) = centralCharacterTable ℂ G i C) (m : ℕ) :
    (m : K) ^ 2 *
        ∑ C : ConjClasses G, ((Nat.card G / Nat.card C.carrier : ℕ) : K) * w C * w C⁻¹ =
      (Nat.card G : K) ^ 2 ↔ m = characterDegree ℂ i := by
  have : CharZero K := (algebraMap K ℂ).charZero
  have hG : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hd : (characterDegree ℂ i : K) ≠ 0 := Nat.cast_ne_zero.mpr (characterDegree_pos ℂ i).ne'
  rw [sum_centralRow_eq_card_div_sq hw, div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero 2 hd),
    mul_comm, mul_right_inj' (pow_ne_zero 2 hG)]
  constructor
  · intro h
    exact (Nat.pow_left_injective (n := 2) (by norm_num)) (by exact_mod_cast h)
  · rintro rfl
    rfl

end TauCeti
