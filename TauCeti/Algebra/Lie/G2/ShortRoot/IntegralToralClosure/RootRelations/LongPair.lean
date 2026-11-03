/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.RankOneWord
import TauCeti.Algebra.Ring.Commutator

/-!
# The long-root A₂ commutator in the short-root G₂ carrier

The positive long roots of G₂ form an A₂ subsystem. Write `y` for the numbered long
simple-root parametrization, and `nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1)` for the pinned rank-one words.
This file proves

```text
[y(a), n₁ y(b) n₁⁻¹] = (n₂ n₁) y(ab) (n₂ n₁)⁻¹.
```

Thus the root at `3α₁ + α₂` and the highest root at `3α₁ + 2α₂` are normalized by actual
words in the simple pinning, not independently chosen matrix signs. The identity holds over
arbitrary commutative rings, including characteristics two and three and nonreduced rings.
It concerns the integral toral closure, without identifying it with an independently
constructed pinned simply connected group scheme.

The construction uses the root matrices of
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic` and the square-zero
commutator identity `Units.val_commutatorElement_eq_one_add_lie`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

open scoped Matrix commutatorElement

namespace TauCeti.G2ShortRoot.IntegralToralClosure

universe v

noncomputable section

-- Constant signed permutation matrices of the two pinned words.
private abbrev W : Fin 2 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 1, 0, 0, 0, 0, 0;
       -1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, -1, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 0, -1, 0],
    !![1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, -1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, -1, 0, 0;
       0, 0, 0, 0, 0, 0, 1]]

-- The three positive long-root vectors, with the Weyl-word signs.
private def L : Fin 3 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![raisingMatrix 1, Matrix.single 0 4 1 - Matrix.single 2 6 1,
    -Matrix.single 0 5 1 - Matrix.single 1 6 1]

private theorem W_orthogonal (i : Fin 2) : W i * (W i).transpose = 1 := by
  fin_cases i <;> decide +kernel

private theorem W_conj_L_zero : W 0 * L 0 * (W 0).transpose = L 1 := by decide +kernel

private theorem W_conj_L_one : W 1 * L 1 * (W 1).transpose = L 2 := by decide +kernel

private theorem L_square (i : Fin 3) : L i * L i = 0 := by
  fin_cases i <;> decide +kernel

private theorem L_triple : L 0 * L 1 * L 0 = 0 ∧ L 1 * L 0 * L 1 = 0 := by
  decide +kernel

private theorem L_bracket : L 0 * L 1 - L 1 * L 0 = L 2 := by decide +kernel

private theorem coe_long (A : Type v) [CommRing A] (a : A) :
    ((rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a) :
      Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      1 + a • (L 0).map (Int.castRingHom A) := by
  simp [coe_rootSubgroupPoints, rootMatrix_inl, rootDividedSquareMatrix_inl, L]

private theorem coe_conj_long (A : Type v) [CommRing A] (a : A) :
    (((rankOneWord 0 A * rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a) *
      (rankOneWord 0 A)⁻¹ : points A) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = 1 + a • (L 1).map (Int.castRingHom A) := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_rankOneWord_inv,
    coe_rankOneWord, ← Matrix.transpose_map, coe_long, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, W_orthogonal,
    W_conj_L_zero, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem coe_conj_conj_long (A : Type v) [CommRing A] (a : A) :
    (((rankOneWord 1 A * (rankOneWord 0 A *
      rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a) * (rankOneWord 0 A)⁻¹) *
      (rankOneWord 1 A)⁻¹ : points A) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = 1 + a • (L 2).map (Int.castRingHom A) := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_rankOneWord_inv,
    coe_rankOneWord, ← Matrix.transpose_map, coe_long, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, W_orthogonal,
    W_conj_L_zero, W_conj_L_one, Matrix.map_one _ (map_zero _) (map_one _)]

/-- The long-root A₂ Chevalley commutator, with the nonsimple root parameters normalized by
pinned rank-one words. The first node is short and the second long (Bourbaki numbering). -/
theorem commutatorElement_rootSubgroupPoints_rankOneWord_conj_rootSubgroupPoints
    (A : Type v) [CommRing A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a),
      rankOneWord 0 A * rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd b) *
        (rankOneWord 0 A)⁻¹⁆ =
      (rankOneWord 1 A * rankOneWord 0 A) *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd (a * b)) *
        (rankOneWord 1 A * rankOneWord 0 A)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  have hcomm := map_commutatorElement (points A).subtype
    (rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a))
    (rankOneWord 0 A * rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd b) *
      (rankOneWord 0 A)⁻¹)
  simp only [Subgroup.subtype_apply] at hcomm
  rw [hcomm]
  rw [Units.val_commutatorElement_eq_one_add_lie _ _
    (a • (L 0).map (Int.castRingHom A)) (b • (L 1).map (Int.castRingHom A))
    (coe_long A a) (coe_conj_long A b)]
  · have h := coe_conj_conj_long A (a * b)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
      mul_inv_rev] at h ⊢
    simp only [← mul_assoc] at h ⊢
    rw [h]
    simp only [Ring.lie_def, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_comm b a, ← smul_sub, ← Matrix.map_mul,
      ← Matrix.map_sub _ (map_sub _), L_bracket]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul,
      L_square, Matrix.map_zero _ (map_zero _), smul_zero]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul,
      L_square, Matrix.map_zero _ (map_zero _), smul_zero]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.map_mul,
      L_triple.1, Matrix.map_zero _ (map_zero _), smul_zero]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.map_mul,
      L_triple.2, Matrix.map_zero _ (map_zero _), smul_zero]

end

end TauCeti.G2ShortRoot.IntegralToralClosure
