/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Burau.Normalization
import TauCeti.LinearAlgebra.Matrix.Determinant.RankOne
import Mathlib.Tactic.LinearCombination

/-!
# The Alexander skein identity for braid closures

Inserting a positive crossing, a negative crossing, or no crossing between two braids
gives the three oriented resolutions of a braid skein triple. The exactly normalized
Burau invariant satisfies `Δ₊ - Δ₋ = (s⁻¹ - s) Δ₀`, where the Alexander parameter is
`s²`. The sign agrees with the existing Seifert Conway substitution `s⁻¹ - s`.

The corner determinants satisfy the unnormalized identity over every commutative ring,
including when they vanish. The normalization supplies the exponent-sum correction;
no division by a geometric sum, a determinant, or `s⁻¹ - s` is used. These formulas
provide the braid side of comparison with an invariant characterized by the oriented
Conway skein relation. They do not assert a geometric presentation correspondence.

The calculation uses the rank-one formulas for the existing Burau generator and its
inverse, and `Matrix.det_add_smul_vecMulVec`.

Reference: J. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 3;
W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapters 6 and 8,
especially Theorem 8.6 (the Conway-normalized skein characterization).
-/

public section

namespace TauCeti.MarkovBraid

open Matrix KnotTheory BraidGroup

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Changing one crossing gives the unnormalized Burau corner-minor skein
identity. Smoothing the crossing joins the prefix `b` to the suffix `c`. -/
theorem burauAlexander_skein (b c : BraidGroup (n + 1)) (i : Fin n) (t : Rˣ) :
    burauAlexander ⟨n, b * sigma (n := n + 1) i * c⟩ t -
      (t : R) * burauAlexander ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ t =
      (1 - (t : R)) * burauAlexander ⟨n, b * c⟩ t := by
  let A := (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  let C := (burau (n + 1) t c : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  let u := A *ᵥ burauCol (t : R) i
  let v := burauRow R (n := n + 1) i ᵥ* C
  let B := (A * C - 1).submatrix Fin.castSucc Fin.castSucc
  let U := u ∘ Fin.castSucc
  let V := v ∘ Fin.castSucc
  have hplus : ((burau (n + 1) t (b * sigma (n := n + 1) i * c) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1).submatrix Fin.castSucc Fin.castSucc =
      B + (-1 : R) • vecMulVec U V := by
    simp only [map_mul, burau_sigma, Matrix.GeneralLinearGroup.coe_mul, coe_burauGL,
      burauMatrix_def, mul_sub, mul_one, sub_mul, mul_vecMulVec, vecMulVec_mul]
    ext j k
    simp [A, C, B, U, V, u, v, submatrix_apply, vecMulVec_apply]
    ring
  have hminus : ((burau (n + 1) t (b * (sigma (n := n + 1) i)⁻¹ * c) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1).submatrix Fin.castSucc Fin.castSucc =
      B + (-((t⁻¹ : Rˣ) : R)) • vecMulVec U V := by
    simp only [map_mul, map_inv, burau_sigma, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv, coe_burauGL, inv_burauMatrix, mul_sub, mul_one,
      mul_smul_comm, sub_mul, smul_mul_assoc, mul_vecMulVec, vecMulVec_mul]
    ext j k
    simp [A, C, B, U, V, u, v, submatrix_apply, vecMulVec_apply]
    ring
  rw [burauAlexander_def, burauAlexander_def, burauAlexander_def, hplus, hminus, map_mul,
    Matrix.GeneralLinearGroup.coe_mul]
  have hp := det_add_smul_vecMulVec B U V (-1)
  have hm := det_add_smul_vecMulVec B U V (-((t⁻¹ : Rˣ) : R))
  have ht := Units.mul_inv t
  linear_combination hp - (t : R) * hm +
    ((B + vecMulVec U V).det - B.det) * ht

/-- The exactly normalized Burau invariant satisfies the oriented Alexander skein relation
with Conway variable `s⁻¹ - s`. The three braids differ only at the indicated crossing. -/
theorem normalizedBurauAlexander_skein
    (b c : BraidGroup (n + 1)) (i : Fin n) (s : Rˣ) :
    normalizedBurauAlexander ⟨n, b * sigma (n := n + 1) i * c⟩ s -
      normalizedBurauAlexander ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ s =
      (((s⁻¹ : Rˣ) : R) - (s : R)) * normalizedBurauAlexander ⟨n, b * c⟩ s := by
  rw [normalizedBurauAlexander_def, normalizedBurauAlexander_def,
    normalizedBurauAlexander_def]
  simp only [map_mul, map_inv, exponentSum_sigma, toAdd_mul,
    toAdd_inv, toAdd_ofAdd]
  let w := Multiplicative.toAdd (ArtinGroup.exponentSum _ b) +
    Multiplicative.toAdd (ArtinGroup.exponentSum _ c)
  have hplus : -(Multiplicative.toAdd (ArtinGroup.exponentSum _ b) + 1 +
      Multiplicative.toAdd (ArtinGroup.exponentSum _ c) + (n : ℤ)) =
      -(w + (n : ℤ)) + -1 := by dsimp only [w]; omega
  have hminus : -(Multiplicative.toAdd (ArtinGroup.exponentSum _ b) + -1 +
      Multiplicative.toAdd (ArtinGroup.exponentSum _ c) + (n : ℤ)) =
      -(w + (n : ℤ)) + 1 := by dsimp only [w]; omega
  rw [hplus, hminus, zpow_add, zpow_add]
  simp only [Units.val_mul, zpow_neg_one, zpow_one]
  have hskein := burauAlexander_skein b c i (s ^ 2)
  have hcancel : ((s⁻¹ : Rˣ) : R) * (s ^ 2 : Rˣ).val = (s : R) := by
    rw [Units.val_pow_eq_pow_val, pow_two, ← mul_assoc, Units.inv_mul, one_mul]
  linear_combination (-1 : R) ^ n * (s ^ (-(w + (n : ℤ))) : Rˣ).val *
    ((s⁻¹ : Rˣ) : R) * hskein +
    (-1 : R) ^ n * (s ^ (-(w + (n : ℤ))) : Rˣ).val *
      ((MarkovBraid.mk n (b * (sigma (n := n + 1) i)⁻¹ * c)).burauAlexander (s ^ 2) -
        (MarkovBraid.mk n (b * c)).burauAlexander (s ^ 2)) * hcancel

end TauCeti.MarkovBraid
