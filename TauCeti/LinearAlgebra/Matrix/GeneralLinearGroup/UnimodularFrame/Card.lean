/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Affine
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SubspaceOrbit
public import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Indices of frame and subspace stabilizers over finite fields

For an `r`-frame in dimension `t + r`, the pointwise stabilizer has index
`∏ (q^(t+r) - q^i)`, `0 ≤ i < r`. Dividing by the number of rectangular matrices gives the
proportion of full-rank matrices. The same count is the index of the setwise stabilizer of an
`r`-plane times the number of ordered bases of that plane.
-/

public section

open Finset Matrix
open scoped Pointwise

namespace TauCeti

/-- The order of the pointwise stabilizer of the standard `m`-frame in `Rⁿ ⊕ Rᵐ`: the projection
onto `GL n R` has kernel the additive group of `m × n` matrices. -/
theorem natCard_affineGroup (R n m : Type*) [Ring R] [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] :
    Nat.card (affineGroup R n m) = Nat.card (GL n R) * Nat.card R ^ (Nat.card n * Nat.card m) := by
  rw [← Subgroup.card_ker_mul_card_of_surjective (affineProjection_surjective R n m),
    ← Nat.card_congr (affineTranslationEquivKer R n m).toEquiv,
    Nat.card_congr Multiplicative.toAdd, card_matrix, mul_comm]

/-- The index of the pointwise stabilizer of a standard `r`-frame over a finite field, in the
form that counts independent ordered `r`-tuples. -/
theorem index_affineGroup_fin (F : Type*) [Field F] [Fintype F] (t r : ℕ) :
    (affineGroup F (Fin t) (Fin r)).index =
      ∏ i ∈ range r, (Fintype.card F ^ (t + r) - Fintype.card F ^ i) := by
  set q := Fintype.card F
  have hsplit (i : ℕ) : q ^ (t + r) - q ^ (r + i) = q ^ r * (q ^ t - q ^ i) := by
    rw [add_comm t r, pow_add, pow_add, Nat.mul_sub_left_distrib]
  have hgl : Nat.card (GL (Fin t ⊕ Fin r) F) =
      (∏ i ∈ range r, (q ^ (t + r) - q ^ i)) * Nat.card (affineGroup F (Fin t) (Fin r)) := by
    rw [Nat.card_congr (finSumFinEquiv.reindexGL F).toEquiv, card_GL_field,
      Fin.prod_univ_eq_prod_range (fun i ↦ q ^ (t + r) - q ^ i)]
    have hprod := prod_range_add (fun i ↦ q ^ (t + r) - q ^ i) r t
    rw [add_comm r t] at hprod
    rw [hprod, prod_congr rfl (fun i _ ↦ hsplit i), prod_mul_distrib, prod_const, card_range,
      ← pow_mul, natCard_affineGroup, card_GL_field,
      Fin.prod_univ_eq_prod_range (fun i ↦ q ^ t - q ^ i)]
    simp [q, Nat.card_eq_fintype_card, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos ((Subgroup.index_mul_card _).trans hgl)

/-- The index of the pointwise stabilizer divided by the number of all rectangular matrices
is the full-rank proportion `∏ (1 - q⁻ⁱ)`, `t < i ≤ t + r`. -/
theorem index_affineGroup_div (F : Type*) [Field F] [Fintype F] (t r : ℕ) :
    ((affineGroup F (Fin t) (Fin r)).index : ℝ) /
      (Fintype.card F : ℝ) ^ ((t + r) * r) =
      ∏ i ∈ range r, (1 - (Fintype.card F : ℝ)⁻¹ ^ (t + i + 1)) := by
  set q := Fintype.card F
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hle (i : ℕ) (hi : i ∈ range r) : q ^ i ≤ q ^ (t + r) :=
    Nat.pow_le_pow_right Fintype.one_lt_card.le (by rw [mem_range] at hi; omega)
  rw [index_affineGroup_fin, Nat.cast_prod, show (t + r) * r = (t + r) * (range r).card by simp,
    pow_mul, ← prod_const, ← prod_div_distrib]
  calc
    _ = ∏ i ∈ range r, (1 - (q : ℝ)⁻¹ ^ (t + r - i)) := by
      refine prod_congr rfl fun i hi ↦ ?_
      rw [Nat.cast_sub (hle i hi), Nat.cast_pow, Nat.cast_pow, inv_pow,
        ← pow_sub_mul_pow (q : ℝ) (by rw [mem_range] at hi; omega : i ≤ t + r)]
      field_simp
    _ = _ := prod_range_add_sub_eq (fun i ↦ 1 - (q : ℝ)⁻¹ ^ i) t r

end TauCeti

namespace Submodule

/-- The index of the stabilizer of an `r`-plane, times the order of `GL_r`, counts the ordered
`r`-frames in the ambient space. The two factors count choices of the span and of an ordered
basis in the span, respectively. -/
theorem index_stabilizer_mul_natCard_GL_eq_prod {F ι : Type*} [Field F] [Fintype F]
    [Fintype ι] [DecidableEq ι] (W : Submodule F (ι → F)) :
    (MulAction.stabilizer (GL ι F) W).index * Nat.card (GL (Fin (Module.finrank F W)) F) =
      ∏ i ∈ range (Module.finrank F W), (Fintype.card F ^ Fintype.card ι - Fintype.card F ^ i) := by
  set r := Module.finrank F W
  set n := Fintype.card ι
  set q := Fintype.card F
  have hrn : r ≤ n := by simpa [r, n] using W.finrank_le
  rw [GeneralLinearGroup.index_stabilizer_submodule_eq_gaussianBinomial, card_GL_field,
    Fin.prod_univ_eq_prod_range (fun i ↦ q ^ r - q ^ i)]
  have hle (i : ℕ) (hi : i ∈ range r) : q ^ i ≤ q ^ r :=
    Nat.pow_le_pow_right Fintype.one_lt_card.le (mem_range.mp hi).le
  have hle' (i : ℕ) (hi : i ∈ range r) : q ^ i ≤ q ^ n :=
    (hle i hi).trans (Nat.pow_le_pow_right Fintype.one_lt_card.le hrn)
  have hprod (m : ℕ) (hm : ∀ i ∈ range r, q ^ i ≤ q ^ m) :
      ((∏ i ∈ range r, (q ^ m - q ^ i) : ℕ) : ℤ) =
        ∏ i ∈ range r, ((q : ℤ) ^ m - (q : ℤ) ^ i) := by
    rw [Nat.cast_prod]
    exact prod_congr rfl fun i hi ↦ by rw [Nat.cast_sub (hm i hi), Nat.cast_pow, Nat.cast_pow]
  have hcast : ((TauCeti.gaussianBinomial q n r : ℕ) : ℤ) =
      TauCeti.gaussianBinomial (q : ℤ) n r :=
    TauCeti.map_gaussianBinomial (Nat.castRingHom ℤ) q n r
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_mul, hcast, hprod r hle, hprod n hle']
  exact TauCeti.gaussianBinomial_mul_prod_pow_sub_pow (q : ℤ) n r

end Submodule
