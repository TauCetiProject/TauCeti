/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Orthogonality of the Dirichlet characters modulo eight on the odd residues

Every unit modulo eight squares to one, so every Dirichlet character of level eight is its own
inverse. Writing the four odd residues modulo eight as `2 * a + 1` for `a : Fin 4`, the
orthogonality relations of the characters take an especially simple form:

* for each pair of characters, `∑ a, ψ (2 * a + 1) * ρ (2 * a + 1)` is `4` when `ψ = ρ` and `0`
  otherwise (valid with values in any integral domain);
* for each pair of odd residues, `∑ χ, χ (2 * a + 1) * χ (2 * b + 1)` is `4` when `a = b` and `0`
  otherwise (valid with values in an integral domain with enough roots of unity, such as `ℂ`).

Equivalently, the `4 × 4` matrix `H` with entries `χ (2 * a + 1)`, rows indexed by the characters
and columns by `Fin 4`, satisfies `H * Hᵀ = 4` and `Hᵀ * H = 4`. Thus `Hᵀ / 4` is the inverse
of `H`: it converts between functions of the odd residue class modulo eight and their expansions
in the characters of level eight. This is the change of coordinates used to split sums over odd
integers by their residue classes modulo eight, as in the quadratic reciprocity matrix of
`TauCeti.NumberTheory.DirichletCharacter.Dyadic.Reciprocity`.

When the coefficient ring has enough roots of unity there are four characters of level eight;
`DirichletCharacter.eq_one_or_eq_χ₄_or_eq_χ₈_or_eq_χ₈'_of_isQuadratic` lists them as the
principal character and the lifts of `ZMod.χ₄`, `ZMod.χ₈` and `ZMod.χ₈'`.

## Main results

* `DirichletCharacter.sq_eq_one_of_level_eight`: every character of level eight has order
  dividing two.
* `DirichletCharacter.sum_fin_four_apply_eq_sum`: a character of level eight summed over the
  four odd residues is its sum over all of `ZMod 8`.
* `DirichletCharacter.sum_fin_four_apply_mul_apply`: orthogonality of two characters over the
  odd residues.
* `DirichletCharacter.sum_apply_mul_apply_of_level_eight`,
  `DirichletCharacter.sum_apply_fin_four_mul_apply_fin_four`: orthogonality of two odd residues
  over the characters.
* `TauCeti.modEightCharacterMatrix_mul_transpose`,
  `TauCeti.modEightCharacterMatrix_transpose_mul`: the matrix form `H * Hᵀ = Hᵀ * H = 4`.
-/

public section

open Finset

namespace DirichletCharacter

/-- Every Dirichlet character of level eight has order dividing two, because every unit
modulo eight squares to one. -/
theorem sq_eq_one_of_level_eight {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R 8) : χ ^ 2 = 1 := by
  refine MulChar.ext fun u ↦ ?_
  rw [MulChar.pow_apply_coe, ← map_pow, MulChar.one_apply_coe, ← Units.val_pow_eq_pow_val,
    (by decide : ∀ u : (ZMod 8)ˣ, u ^ 2 = 1) u, Units.val_one, map_one]

/-- Every Dirichlet character of level eight is its own inverse. -/
theorem inv_eq_self_of_level_eight {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R 8) : χ⁻¹ = χ :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, sq_eq_one_of_level_eight])

/-- Two characters of level eight multiply to the principal character exactly when they are
equal. -/
theorem mul_eq_one_iff_eq_of_level_eight {R : Type*} [CommMonoidWithZero R]
    {ψ ρ : DirichletCharacter R 8} : ψ * ρ = 1 ↔ ψ = ρ := by
  rw [mul_eq_one_iff_eq_inv, inv_eq_self_of_level_eight]

/-- The odd residues `2 * a + 1`, for `a : Fin 4`, are units modulo eight. -/
theorem isUnit_two_mul_add_one_fin_four (a : Fin 4) : IsUnit (2 * (a : ℕ) + 1 : ZMod 8) := by
  fin_cases a <;> decide

/-- The odd residues `2 * a + 1`, for `a : Fin 4`, are distinct modulo eight. -/
theorem two_mul_add_one_fin_four_inj {a b : Fin 4} :
    (2 * (a : ℕ) + 1 : ZMod 8) = 2 * (b : ℕ) + 1 ↔ a = b := by
  fin_cases a <;> fin_cases b <;> decide

/-- A Dirichlet character of level eight vanishes at the even residues, so its sum over the four
odd residues `2 * a + 1` is its sum over all of `ZMod 8`. -/
theorem sum_fin_four_apply_eq_sum {R : Type*} [CommSemiring R] (χ : DirichletCharacter R 8) :
    ∑ a : Fin 4, χ (2 * (a : ℕ) + 1) = ∑ x : ZMod 8, χ x := by
  have h0 (x : ZMod 8) (hx : ¬IsUnit x) : χ x = 0 := MulChar.map_nonunit χ hx
  rw [Fin.sum_univ_four, show (univ : Finset (ZMod 8)) = {0, 1, 2, 3, 4, 5, 6, 7} by decide,
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton, h0 0 (by decide), h0 2 (by decide),
    h0 4 (by decide), h0 6 (by decide)]
  norm_num
  ring

/-- **Orthogonality of the characters of level eight on the odd residues.** For characters `ψ`
and `ρ` of level eight with values in an integral domain, `∑ a, ψ (2 * a + 1) * ρ (2 * a + 1)`
is `4` if `ψ = ρ` and `0` otherwise. -/
theorem sum_fin_four_apply_mul_apply {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq (DirichletCharacter R 8)] (ψ ρ : DirichletCharacter R 8) :
    ∑ a : Fin 4, ψ (2 * (a : ℕ) + 1) * ρ (2 * (a : ℕ) + 1) = if ψ = ρ then 4 else 0 := by
  simp_rw [← MulChar.mul_apply]
  split_ifs with h
  · subst h
    rw [← sq, sq_eq_one_of_level_eight, Fin.sum_univ_four]
    simp_rw [MulChar.one_apply (isUnit_two_mul_add_one_fin_four _)]
    norm_num
  · rw [sum_fin_four_apply_eq_sum]
    exact MulChar.sum_eq_zero_of_ne_one (mul_eq_one_iff_eq_of_level_eight.not.mpr h)

variable (R : Type*) [CommRing R] [IsDomain R]
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod 8)ˣ)]

/-- **Orthogonality of the units modulo eight over the characters.** For a unit `a` modulo eight
and any `b`, with values in an integral domain with enough roots of unity,
`∑ χ, χ a * χ b` is `4` if `a = b` and `0` otherwise. -/
theorem sum_apply_mul_apply_of_level_eight {a : ZMod 8} (ha : IsUnit a) (b : ZMod 8) :
    ∑ χ : DirichletCharacter R 8, χ a * χ b = if a = b then 4 else 0 := by
  obtain ⟨u, rfl⟩ := ha
  have hinv : (u : ZMod 8)⁻¹ = u := by
    rw [ZMod.inv_coe_unit, (by decide : ∀ u : (ZMod 8)ˣ, u⁻¹ = u) u]
  have h := sum_char_inv_mul_char_eq R u.isUnit b
  rw [hinv, show Nat.totient 8 = 4 by decide, Nat.cast_ofNat] at h
  exact h

/-- **Orthogonality of the odd residues modulo eight over the characters.** With values in an
integral domain with enough roots of unity, `∑ χ, χ (2 * a + 1) * χ (2 * b + 1)` is `4` if
`a = b` and `0` otherwise. -/
theorem sum_apply_fin_four_mul_apply_fin_four (a b : Fin 4) :
    ∑ χ : DirichletCharacter R 8, χ (2 * (a : ℕ) + 1) * χ (2 * (b : ℕ) + 1) =
      if a = b then 4 else 0 := by
  rw [sum_apply_mul_apply_of_level_eight R (isUnit_two_mul_add_one_fin_four a)]
  exact if_congr two_mul_add_one_fin_four_inj rfl rfl

end DirichletCharacter

namespace TauCeti

open DirichletCharacter

variable (R : Type*) [CommRing R]

/-- The character table of level eight on the odd residues: the matrix whose row `χ` and
column `a : Fin 4` is the value `χ (2 * a + 1)` at the odd residue `2 * a + 1` modulo eight. -/
noncomputable def modEightCharacterMatrix : Matrix (DirichletCharacter R 8) (Fin 4) R :=
  Matrix.of fun χ a ↦ χ (2 * (a : ℕ) + 1)

/-- The entries of the character table of level eight. -/
@[simp]
theorem modEightCharacterMatrix_apply (χ : DirichletCharacter R 8) (a : Fin 4) :
    modEightCharacterMatrix R χ a = χ (2 * (a : ℕ) + 1) :=
  (rfl)

/-- The rows of the character table of level eight are orthogonal of squared length four:
`H * Hᵀ = 4`. -/
theorem modEightCharacterMatrix_mul_transpose [IsDomain R]
    [DecidableEq (DirichletCharacter R 8)] :
    modEightCharacterMatrix R * (modEightCharacterMatrix R).transpose = 4 := by
  ext ψ ρ
  rw [Matrix.mul_apply]
  simp only [modEightCharacterMatrix_apply, Matrix.transpose_apply]
  rw [sum_fin_four_apply_mul_apply, Matrix.ofNat_apply]
  split_ifs <;> simp_all

/-- The columns of the character table of level eight are orthogonal of squared length four:
`Hᵀ * H = 4`. -/
theorem modEightCharacterMatrix_transpose_mul [IsDomain R]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod 8)ˣ)] :
    (modEightCharacterMatrix R).transpose * modEightCharacterMatrix R = 4 := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [modEightCharacterMatrix_apply, Matrix.transpose_apply]
  rw [sum_apply_fin_four_mul_apply_fin_four, Matrix.ofNat_apply]
  split_ifs <;> simp_all

end TauCeti
