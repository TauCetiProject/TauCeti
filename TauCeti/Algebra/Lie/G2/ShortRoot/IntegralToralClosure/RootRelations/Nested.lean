/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A highest-root commutator in the short-root G₂ carrier

Write `x(t) = x_{α₁}(t)` and `y(t) = x_{α₂}(t)`, where `α₁` is short. The nested
commutator `[y(b), [y(c), x(a)]]` belongs to the highest-root subgroup, with parameter
`-a³bc` in the parametrization obtained by conjugating `y` by `n₂ n₁`. Here
`nᵢ = x_{αᵢ}(1) x_{-αᵢ}(-1) x_{αᵢ}(1)`; the minus sign is fixed by these actual
root words rather than by an arbitrary choice of highest-root vector.

The identity is integral and therefore retains the cubic parameter in characteristic three
and over nonreduced rings. It is a rank-two relation for recognizing the numbered root
subgroups. The carrier is not identified with the pinned simply connected group scheme of
its diagram; transfer to that group requires such an identification.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2 (Chevalley commutator relations).
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.

The calculation uses the integral divided-power matrices of
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`.
-/

public section

universe v

open scoped Matrix commutatorElement

namespace TauCeti.G2ShortRoot.IntegralToralClosure

variable (A : Type v) [CommRing A]

local notation "x" => rootSubgroupPoints (Sum.inl 0) A
local notation "y" => rootSubgroupPoints (Sum.inl 1) A
local notation "n₀" =>
  (x (Multiplicative.ofAdd 1) * rootSubgroupPoints (Sum.inr 0) A (Multiplicative.ofAdd (-1)) *
    x (Multiplicative.ofAdd 1))
local notation "n₁" =>
  (y (Multiplicative.ofAdd 1) * rootSubgroupPoints (Sum.inr 1) A (Multiplicative.ofAdd (-1)) *
    y (Multiplicative.ofAdd 1))

-- Sparse column formulas avoid expanding repeated seven-term matrix sums in root words.
private theorem mul_short_apply (M : Matrix (Fin 7) (Fin 7) A) (t : A) (i j : Fin 7) :
    (M * ((x (Multiplicative.ofAdd t) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A)) i j =
      ![M i 0, M i 1 + t * M i 0, M i 2, M i 3 + 2*t*M i 2,
        M i 4 + t*M i 3 + t^2*M i 2, M i 5, M i 6 + t*M i 5] j := by
  rw [coe_rootSubgroupPoints_inl_zero]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem mul_long_apply (M : Matrix (Fin 7) (Fin 7) A) (t : A) (i j : Fin 7) :
    (M * ((y (Multiplicative.ofAdd t) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A)) i j =
      ![M i 0, M i 1, M i 2 + t*M i 1, M i 3, M i 4,
        M i 5 + t*M i 4, M i 6] j := by
  rw [coe_rootSubgroupPoints_inl_one]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem long_mul_apply (M : Matrix (Fin 7) (Fin 7) A) (t : A) (i j : Fin 7) :
    (((y (Multiplicative.ofAdd t) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) * M) i j =
      ![M 0 j, M 1 j + t*M 2 j, M 2 j, M 3 j,
        M 4 j + t*M 5 j, M 5 j, M 6 j] i := by
  rw [coe_rootSubgroupPoints_inl_one]
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem mul_negative_short_apply (M : Matrix (Fin 7) (Fin 7) A) (t : A)
    (i j : Fin 7) :
    (M * ((rootSubgroupPoints (.inr 0) A (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) i j =
      ![M i 0 + t*M i 1, M i 1, M i 2 + t*M i 3 + t^2*M i 4,
        M i 3 + 2*t*M i 4, M i 4, M i 5 + t*M i 6, M i 6] j := by
  rw [coe_rootSubgroupPoints_inr_zero]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem mul_negative_long_apply (M : Matrix (Fin 7) (Fin 7) A) (t : A)
    (i j : Fin 7) :
    (M * ((rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) i j =
      ![M i 0, M i 1 + t*M i 2, M i 2, M i 3,
        M i 4 + t*M i 5, M i 5, M i 6] j := by
  rw [coe_rootSubgroupPoints_inr_one]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem weyl_word_matrix :
    (((n₁ * n₀ : points A) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) =
      !![0, 1, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0;
         1, 0, 0, 0, 0, 0, 0;
         0, 0, 0, -1, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 1;
         0, 0, -1, 0, 0, 0, 0;
         0, 0, 0, 0, 0, -1, 0] := by
  simp only [← mul_assoc, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_short_apply, mul_long_apply, mul_negative_short_apply,
      mul_negative_long_apply, Matrix.cons_val_zero] <;> simp <;> ring

private def highestMatrix (t : A) : Matrix (Fin 7) (Fin 7) A :=
  !![1, 0, 0, 0, 0, -t, 0;
     0, 1, 0, 0, 0, 0, -t;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

private theorem highest_mul_apply (M : Matrix (Fin 7) (Fin 7) A) (t : A) (i j : Fin 7) :
    (highestMatrix A t * M) i j =
      ![M 0 j - t*M 5 j, M 1 j - t*M 6 j, M 2 j, M 3 j, M 4 j, M 5 j, M 6 j] i := by
  fin_cases i <;> simp [highestMatrix, Matrix.mul_apply, Fin.sum_univ_succ, sub_eq_add_neg]

private theorem highest_conjugate_matrix (t : A) :
    ((((n₁ * n₀) * y (Multiplicative.ofAdd t) * (n₁ * n₀)⁻¹ : points A) :
      Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      highestMatrix A t := by
  -- Freeze the word before reassociating, retaining its already computed matrix.
  have hwmat := weyl_word_matrix A
  generalize hw : (n₁ * n₀ : points A) = w at hwmat ⊢
  apply (Units.isUnit (w : Matrix.GeneralLinearGroup (Fin 7) A)).mul_right_cancel
  simp only [← Matrix.GeneralLinearGroup.coe_mul, ← Subgroup.coe_mul,
    mul_assoc, inv_mul_cancel, mul_one]
  simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hwmat]
  rw [coe_rootSubgroupPoints_inl_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [highestMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem inner_commutator_matrix (a c : A) :
    (((⁅y (Multiplicative.ofAdd c), x (Multiplicative.ofAdd a)⁆ : points A) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      !![1, 0, -a*c, 2*a^2*c, -a^3*c, 0, 0;
         0, 1, 0, 2*a*c, -a^2*c, -a^2*c^2, a^3*c^2;
         0, 0, 1, 0, 0, -a^2*c, a^3*c;
         0, 0, 0, 1, 0, -a*c, a^2*c;
         0, 0, 0, 0, 1, 0, a*c;
         0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, 0, 0, 1] := by
  simp only [commutatorElement_def, ← (rootSubgroupPoints (Sum.inl 0) A).map_inv,
    ← (rootSubgroupPoints (Sum.inl 1) A).map_inv, ← ofAdd_neg,
    Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_short_apply, mul_long_apply, Matrix.cons_val_zero] <;> simp <;> ring

/-- The nested long-long-short commutator is a highest-root point. The highest-root
parametrization is the conjugate of the long simple-root parametrization by the pinned
root word `n₂ n₁`, and its parameter is `-a³bc`. -/
theorem commutatorElement_long_commutatorElement_long_short (a b c : A) :
    ⁅y (Multiplicative.ofAdd b),
      ⁅y (Multiplicative.ofAdd c), x (Multiplicative.ofAdd a)⁆⁆ =
      (n₁ * n₀) * y (Multiplicative.ofAdd (-(a ^ 3 * b * c))) * (n₁ * n₀)⁻¹ := by
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul]
  -- Retain the two computed matrices instead of re-expanding their root words.
  have hh := highest_conjugate_matrix A (-(a ^ 3 * b * c))
  generalize hhdef : ((n₁ * n₀) * y (Multiplicative.ofAdd (-(a ^ 3 * b * c))) *
    (n₁ * n₀)⁻¹ : points A) = h at hh ⊢
  have hk := inner_commutator_matrix A a c
  generalize hkdef : ⁅y (Multiplicative.ofAdd c), x (Multiplicative.ofAdd a)⁆ = k at hk ⊢
  apply Subtype.ext
  apply Units.ext
  simp only [← (rootSubgroupPoints (Sum.inl 1) A).map_inv, ← ofAdd_neg,
    Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hh, hk]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_long_apply, long_mul_apply, highest_mul_apply] <;>
    simp <;> ring

end TauCeti.G2ShortRoot.IntegralToralClosure
