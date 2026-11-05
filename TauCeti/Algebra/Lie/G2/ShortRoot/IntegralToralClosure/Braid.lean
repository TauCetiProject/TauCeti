/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic

/-!
# The six-term braid relation in the short-root G₂ carrier

The pinned root words `nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the seven-dimensional short-root
module satisfy `(n₀ n₁)³ = (n₁ n₀)³`. This is the type-G₂ braid relation, with six
alternating factors, not the three-factor relation for a single bond.

The identity holds in the integral toral-closure carrier over every commutative ring,
including rings with nilpotents and rings of characteristics two and three. The proof
computes the two integral signed permutation matrices and then changes coefficients.
It does not identify the carrier with an independently pinned group scheme.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Section 3.
* R. W. Carter, *Simple Groups of Lie Type*, Section 7.2.

The root parametrizations and their integral matrix formulas are those of
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot.IntegralToralClosure

private def reflectionMatrix : Fin 2 → Matrix (Fin 7) (Fin 7) ℤ
  | 0 => !![0, 1, 0, 0, 0, 0, 0;
           -1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 1, 0, 0;
           0, 0, 0, -1, 0, 0, 0;
           0, 0, 1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1;
           0, 0, 0, 0, 0, -1, 0]
  | 1 => !![1, 0, 0, 0, 0, 0, 0;
           0, 0, 1, 0, 0, 0, 0;
           0, -1, 0, 0, 0, 0, 0;
           0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0;
           0, 0, 0, 0, -1, 0, 0;
           0, 0, 0, 0, 0, 0, 1]

private theorem reflectionMatrix_braid :
    (reflectionMatrix 0 * reflectionMatrix 1) ^ 3 =
      (reflectionMatrix 1 * reflectionMatrix 0) ^ 3 := by
  norm_num [reflectionMatrix, pow_succ, Matrix.cons_mul, Matrix.cons_vecMul]

private theorem coe_root_word (A : Type*) [CommRing A] (i : Fin 2) :
    ((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) :
          Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
      ((rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) :
          Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
      ((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) :
          Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      (reflectionMatrix i).map (Int.castRingHom A) := by
  fin_cases i
  · simp only [Fin.zero_eta, coe_rootSubgroupPoints_inl_zero A,
      coe_rootSubgroupPoints_inr_zero A]
    norm_num [reflectionMatrix, Matrix.cons_mul, Matrix.cons_vecMul,
      ← Matrix.ext_iff, Fin.forall_fin_succ]
  · simp only [Fin.mk_one, coe_rootSubgroupPoints_inl_one A,
      coe_rootSubgroupPoints_inr_one A]
    norm_num [reflectionMatrix, Matrix.cons_mul, Matrix.cons_vecMul,
      ← Matrix.ext_iff, Fin.forall_fin_succ]

/-- The pinned simple-root words satisfy the six-term type-G₂ braid relation over every
commutative ring. Node `0` is short and node `1` is long in Bourbaki numbering. -/
theorem rootSubgroupPoints_braid (A : Type*) [CommRing A] :
    let n := fun i : Fin 2 =>
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)
    (n 0 * n 1) ^ 3 = (n 1 * n 0) ^ 3 := by
  dsimp only
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Units.val_pow_eq_pow_val, Units.val_mul]
  rw [coe_root_word, coe_root_word]
  simpa only [Matrix.map_mul, Matrix.map_pow] using
    congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.castRingHom A))
      reflectionMatrix_braid

end TauCeti.G2ShortRoot.IntegralToralClosure
