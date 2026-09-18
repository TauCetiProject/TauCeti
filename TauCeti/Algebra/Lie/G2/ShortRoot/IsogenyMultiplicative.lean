/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct
public import TauCeti.Algebra.Lie.G2.ShortRoot.SpecialIsogeny

/-!
# Multiplicativity of the type-G2 special isogeny

The `(i, j)` entry of `Matrix.g2SpecialIsogeny g` is a fixed linear functional applied to the
congruence transform `g W gᵀ` of a fixed alternating matrix. Multiplicativity of the minor formula
therefore asks that the seven alternating matrices `isogenySource` and the seven functionals
`isogenyProjection` split a `g`-stable subspace of the alternating matrices.

That subspace is the copy of the Lie algebra: the kernel of the contraction
`Matrix.g2CrossMap` against the cross product, which is stable exactly because `g` preserves the
cross product. Inside it, the kernel of the seven functionals is the short-root ideal, spanned by
the matrices `crossBivector`, which in characteristic three is again stable, because `g` fixes the
invariant dual form as well. The splitting is
`TauCeti.G2ShortRoot.eq_sum_isogenySource_add_sum_crossBivector`, and it holds only in
characteristic three: that is where the short-root vectors span an ideal and where the seven
matrices `crossBivector` fall into the kernel of the contraction.

Multiplicativity fails on the whole of `GL₇`, so the two preservation hypotheses cannot be
dropped. Nothing below verifies them for any particular matrix, and no group of matrix-valued
points is formed on which the formula would restrict to an endomorphism.

## Main definitions

* `TauCeti.G2ShortRoot.isogenySource` and `TauCeti.G2ShortRoot.isogenyProjection`: the alternating
  matrices and the functionals through which the minor formula is read, with
  `TauCeti.G2ShortRoot.isogenySource_eq` writing the former through single unit matrices.
* `TauCeti.G2ShortRoot.isogenyKernelCoeff`: the coordinates along the short-root matrices.

## Main results

* `Matrix.g2SpecialIsogeny_apply_eq`: the minor formula as a functional of a congruence transform.
* `TauCeti.G2ShortRoot.eq_sum_isogenySource_add_sum_crossBivector`: the splitting in
  characteristic three.
* `Matrix.g2SpecialIsogeny_mul`: multiplicativity of the special isogeny.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §6, for the cross product and the short-root ideal in characteristic three.
-/

public section

open Matrix

universe u

namespace TauCeti.G2ShortRoot

variable {R : Type u} [CommRing R]

/-- The seven alternating matrices whose congruence transforms the special isogeny reads: the
alternating matrix of the `j`-th distinguished index pair, joined at the middle index by the
alternating matrix of the pair `(2, 4)`. -/
def isogenySource : Fin 7 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 1, 0, 0, 0, 0, 0;
      -1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      -1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, -1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 0;
      0, -1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, -1, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, -1, 0]]

/-- **The alternating matrices read by the special isogeny**: the `j`-th is the alternating matrix
`e_p ∧ e_q` of the distinguished index pair `(p, q) = TauCeti.g2SpecialIsogenyPair j`, joined at
the middle index `3` by the alternating matrix of the pair `(2, 4)`. -/
theorem isogenySource_eq (j : Fin 7) :
    isogenySource j =
      Matrix.single (g2SpecialIsogenyPair j).1 (g2SpecialIsogenyPair j).2 1 -
        Matrix.single (g2SpecialIsogenyPair j).2 (g2SpecialIsogenyPair j).1 1 +
          if j = 3 then Matrix.single 2 4 1 - Matrix.single 4 2 1 else 0 := by
  ext a b
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp [isogenySource]

/-- The alternating matrices read by the special isogeny lie in the kernel of the contraction, so
they lie in the Lie algebra. -/
@[simp]
theorem _root_.Matrix.g2CrossMap_isogenySource (j m : Fin 7) :
    g2CrossMap ((isogenySource j).map (Int.cast : ℤ → R)) m = 0 := by
  have key : ∀ j m : Fin 7,
      ∑ k, ((crossOperator k).map (Int.cast : ℤ → ℤ) * (isogenySource j)ᵀ) m k = 0 := by
    rw [crossOperator_eq]
    decide +kernel
  rw [g2CrossMap_map, g2CrossMap_def, key j m, Int.cast_zero]

/-- The linear functional the special isogeny reads on the `i`-th distinguished index pair: the
entry there, diminished at the middle index by the entry at the pair `(0, 6)`. -/
def isogenyProjection (i : Fin 7) : Matrix (Fin 7) (Fin 7) R →ₗ[R] R where
  toFun W := W (g2SpecialIsogenyPair i).1 (g2SpecialIsogenyPair i).2 - if i = 3 then W 0 6 else 0
  map_add' W V := by
    split_ifs <;> simp
    ring
  map_smul' c W := by
    split_ifs <;> simp [smul_eq_mul]
    ring

/-- The entrywise formula for the functional. -/
theorem isogenyProjection_apply (i : Fin 7) (W : Matrix (Fin 7) (Fin 7) R) :
    isogenyProjection i W =
      W (g2SpecialIsogenyPair i).1 (g2SpecialIsogenyPair i).2 -
        if i = 3 then W 0 6 else 0 := (rfl)

/-- The functionals and the alternating matrices `isogenySource` are dual to one another. -/
@[simp]
theorem isogenyProjection_isogenySource (i j : Fin 7) :
    isogenyProjection i ((isogenySource j).map (Int.cast : ℤ → R)) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [isogenyProjection_apply, isogenySource]

/-- The functionals kill the alternating matrices spanning the short-root ideal. -/
@[simp]
theorem isogenyProjection_crossBivector (i a : Fin 7) :
    isogenyProjection i ((crossBivector a).map (Int.cast : ℤ → R)) = 0 := by
  fin_cases i <;> fin_cases a <;> simp [isogenyProjection_apply, crossBivector_eq]

private theorem _root_.Matrix.apply_mul_isogenySource_mul_transpose
    (g : Matrix (Fin 7) (Fin 7) R) (j a b : Fin 7) :
    (g * (isogenySource j).map (Int.cast : ℤ → R) * gᵀ) a b =
      g2SpecialIsogenyColumn g (a, b) j := by
  fin_cases j <;>
    simp [g2SpecialIsogenyColumn_def, pairMinor_eq, Matrix.mul_apply, Fin.sum_univ_seven,
      isogenySource, Matrix.transpose_apply] <;> ring

/-- **The minor formula read by congruence.** The `(i, j)` entry of the special isogeny of `g` is
the `i`-th functional applied to the congruence transform by `g` of the `j`-th alternating
matrix. -/
theorem _root_.Matrix.g2SpecialIsogeny_apply_eq (g : Matrix (Fin 7) (Fin 7) R) (i j : Fin 7) :
    g2SpecialIsogeny g i j =
      isogenyProjection i (g * (isogenySource j).map (Int.cast : ℤ → R) * gᵀ) := by
  rw [isogenyProjection_apply, apply_mul_isogenySource_mul_transpose, g2SpecialIsogeny_apply]
  split_ifs with h
  · rw [apply_mul_isogenySource_mul_transpose]
  · rfl

/-- Seven signed entries of a matrix, one for each matrix `crossBivector`. On an alternating
matrix killed by the cross-product contraction in characteristic three these are its coordinates
along the matrices `crossBivector`, which is the content of
`TauCeti.G2ShortRoot.eq_sum_isogenySource_add_sum_crossBivector`; nothing is claimed of them
otherwise. -/
def isogenyKernelCoeff (a : Fin 7) : Matrix (Fin 7) (Fin 7) R →ₗ[R] R where
  toFun W := ![-W 1 2, W 1 3, W 2 3, W 0 6, W 3 4, W 3 5, -W 4 5] a
  map_add' W V := by fin_cases a <;> simp <;> ring
  map_smul' c W := by fin_cases a <;> simp [smul_eq_mul]

/-- The entrywise formula for the coordinates. -/
theorem isogenyKernelCoeff_apply (a : Fin 7) (W : Matrix (Fin 7) (Fin 7) R) :
    isogenyKernelCoeff a W = ![-W 1 2, W 1 3, W 2 3, W 0 6, W 3 4, W 3 5, -W 4 5] a := (rfl)

/-- **The alternating matrices read by the special isogeny are alternating** over any commutative
ring. -/
@[simp]
theorem transpose_isogenySource_map (l : Fin 7) :
    ((isogenySource l).map (Int.cast : ℤ → R))ᵀ = -(isogenySource l).map (Int.cast : ℤ → R) :=
  Matrix.transpose_map_of_transpose_eq_neg (Int.castRingHom R)
    (by revert l; decide +kernel)

/-- **The splitting of the Lie algebra in characteristic three.** An alternating matrix killed by
the cross-product contraction is the sum of its `isogenySource` part, read by the functionals
`isogenyProjection`, and its short-root part, read by the coordinates `isogenyKernelCoeff`. So in
characteristic three the alternating matrices killed by the contraction are spanned by the seven
matrices `isogenySource` together with the seven matrices `crossBivector`. -/
theorem eq_sum_isogenySource_add_sum_crossBivector [CharP R 3] {W : Matrix (Fin 7) (Fin 7) R}
    (hW : Wᵀ = -W) (hc : ∀ m, g2CrossMap W m = 0) :
    W = (∑ k, isogenyProjection k W • (isogenySource k).map (Int.cast : ℤ → R)) +
      ∑ a, isogenyKernelCoeff a W • (crossBivector a).map (Int.cast : ℤ → R) := by
  have h3 : (3 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 3
  have hA : ∀ a b, W a b + W b a = 0 := fun a b => by
    have h := congrFun (congrFun hW b) a
    rw [Matrix.transpose_apply, Matrix.neg_apply] at h
    rw [h]
    ring
  have e0 := (g2CrossMap_apply W 0).symm.trans (hc 0)
  have e1 := (g2CrossMap_apply W 1).symm.trans (hc 1)
  have e2 := (g2CrossMap_apply W 2).symm.trans (hc 2)
  have e3 := (g2CrossMap_apply W 3).symm.trans (hc 3)
  have e4 := (g2CrossMap_apply W 4).symm.trans (hc 4)
  have e5 := (g2CrossMap_apply W 5).symm.trans (hc 5)
  have e6 := (g2CrossMap_apply W 6).symm.trans (hc 6)
  simp [Fin.sum_univ_seven, crossOperator_eq] at e0 e1 e2 e3 e4 e5 e6
  have hsum : ((∑ k, isogenyProjection k W • (isogenySource k).map (Int.cast : ℤ → R)) +
      ∑ a, isogenyKernelCoeff a W • (crossBivector a).map (Int.cast : ℤ → R))ᵀ =
      -((∑ k, isogenyProjection k W • (isogenySource k).map (Int.cast : ℤ → R)) +
        ∑ a, isogenyKernelCoeff a W • (crossBivector a).map (Int.cast : ℤ → R)) := by
    simp only [Matrix.transpose_add, Matrix.transpose_sum, Matrix.transpose_smul,
      transpose_isogenySource_map, transpose_crossBivector_map, smul_neg,
      Finset.sum_neg_distrib, neg_add]
  have hodd : Odd 3 := by decide
  refine Matrix.ext_of_lt_of_transpose_eq_neg hW hsum
    (Matrix.diag_eq_zero_of_transpose_eq_neg_of_charP 3 hodd hW)
    (Matrix.diag_eq_zero_of_transpose_eq_neg_of_charP 3 hodd hsum) fun m n hmn => ?_
  fin_cases m <;> fin_cases n <;>
    first
      | exact absurd hmn (by decide)
      | simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          Fin.sum_univ_seven, isogenyProjection_apply, isogenyKernelCoeff_apply, isogenySource,
          crossBivector_eq, Matrix.map_apply, g2SpecialIsogenyPair_zero, g2SpecialIsogenyPair_one,
          g2SpecialIsogenyPair_two, g2SpecialIsogenyPair_three, g2SpecialIsogenyPair_four,
          g2SpecialIsogenyPair_five, g2SpecialIsogenyPair_six, Matrix.cons_val',
          Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Matrix.of_apply, Fin.isValue]
  all_goals push_cast
  -- The twenty-one entries above the diagonal fall into three families. At six of them the two
  -- sides agree outright after expansion. At eight the difference is carried by a short-root
  -- coordinate and is a multiple of three, discharged by `h3`. The remaining seven are the
  -- entries the contraction equations `e0`--`e6` control, one each, together with the
  -- skew-symmetry relations `hA` and again `h3`.
  · ring -- (0, 1)
  · ring -- (0, 2)
  · linear_combination -e0 - hA 0 3 + hA 1 2 + (W 1 2 - W 2 1 + W 3 0) * h3 -- (0, 3)
  · linear_combination -e1 - hA 0 4 + hA 1 3 + (-W 1 3 - W 3 1 + W 4 0) * h3 -- (0, 4)
  · linear_combination -e2 - hA 0 5 + hA 2 3 + (-W 2 3 - W 3 2 + W 5 0) * h3 -- (0, 5)
  · linear_combination (-W 0 6) * h3 -- (0, 6)
  · linear_combination (-W 1 2) * h3 -- (1, 2)
  · linear_combination (W 1 3) * h3 -- (1, 3)
  · ring -- (1, 4)
  · linear_combination (-W 0 6) * h3 -- (1, 5)
  · linear_combination -e4 - hA 1 6 + hA 3 4 + (-W 3 4 - W 4 3 + W 6 1) * h3 -- (1, 6)
  · linear_combination (W 2 3) * h3 -- (2, 3)
  · linear_combination -e3 + hA 0 6 + hA 1 5 - hA 2 4 + (W 0 6 - W 1 5 + W 2 4) * h3 -- (2, 4)
  · ring -- (2, 5)
  · linear_combination -e5 - hA 2 6 + hA 3 5 + (-W 3 5 - W 5 3 + W 6 2) * h3 -- (2, 6)
  · linear_combination (W 3 4) * h3 -- (3, 4)
  · linear_combination (W 3 5) * h3 -- (3, 5)
  · linear_combination -e6 - hA 3 6 + hA 4 5 + (W 4 5 - W 5 4 + W 6 3) * h3 -- (3, 6)
  · linear_combination (-W 4 5) * h3 -- (4, 5)
  · ring -- (4, 6)
  · ring -- (5, 6)

/-- **The special isogeny is multiplicative in characteristic three** on matrices preserving the
cross product, the left factor fixing the invariant dual form by congruence as well.
Multiplicativity fails on the whole of `GL₇`: it is the two preservation hypotheses that make the
quotient by the short-root ideal an invariant subquotient and so turn the minor formula into a
homomorphism. Nothing here verifies those hypotheses for any particular matrix. -/
theorem _root_.Matrix.g2SpecialIsogeny_mul [CharP R 3] {g h : Matrix (Fin 7) (Fin 7) R}
    (hg : PreservesG2Cross g)
    (hgB : g * invariantDualForm.map (Int.cast : ℤ → R) * gᵀ =
      invariantDualForm.map (Int.cast : ℤ → R))
    (hh : PreservesG2Cross h) :
    g2SpecialIsogeny (g * h) = g2SpecialIsogeny g * g2SpecialIsogeny h := by
  have expand : ∀ (c : Fin 7 → R) (M : Fin 7 → Matrix (Fin 7) (Fin 7) R),
      g * (∑ k, c k • M k) * gᵀ = ∑ k, c k • (g * M k * gᵀ) := fun c M => by
    rw [Matrix.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_smul, Matrix.smul_mul]
  ext i j
  set W : Matrix (Fin 7) (Fin 7) R := h * (isogenySource j).map (Int.cast : ℤ → R) * hᵀ
    with hWdef
  have hWanti : Wᵀ = -W := by
    rw [hWdef, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      transpose_isogenySource_map]
    simp [Matrix.mul_assoc]
  have hWcross : ∀ m, g2CrossMap W m = 0 := fun m => by
    rw [hWdef, g2CrossMap_mul_mul_transpose hh]
    simp [g2CrossMap_isogenySource]
  have hY : ∀ a : Fin 7,
      isogenyProjection i (g * (crossBivector a).map (Int.cast : ℤ → R) * gᵀ) = 0 := fun a => by
    rw [mul_crossBivector_mul_transpose hg hgB a, map_sum]
    exact Finset.sum_eq_zero fun b _ => by
      rw [map_smul, isogenyProjection_crossBivector, smul_zero]
  have h1 : g2SpecialIsogeny (g * h) i j = isogenyProjection i (g * W * gᵀ) := by
    rw [g2SpecialIsogeny_apply_eq, hWdef, Matrix.transpose_mul]
    congr 1
    noncomm_ring
  rw [h1, eq_sum_isogenySource_add_sum_crossBivector hWanti hWcross, Matrix.mul_add,
    Matrix.add_mul, map_add, expand, expand, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul, hY, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← g2SpecialIsogeny_apply_eq, ← g2SpecialIsogeny_apply_eq, mul_comm]

end TauCeti.G2ShortRoot
