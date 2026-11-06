/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Rank-one representations on a minuscule weight basis

At a fixed simple node, the weights split into pairs of weights `1, -1` and fixed weights of
coordinate zero. A two-by-two matrix acts on every pair in that order and fixes the remaining
basis vectors. This gives a multiplicative representation of the two-by-two matrices, hence of
`GL₂` and `SL₂`: the upper and lower transvections with parameter `t` act by the root unipotents
`1 + t • E_i` and `1 + t • F_i` built from the table's raising and lowering matrices, and a
diagonal matrix acts diagonally through the weights. The resulting rank-one copies of `SL₂`
supply a Weyl representative for each simple reflection (Carter's `n_i(-1) = n_i⁻¹`, the image
of `ModularGroup.S`) and the rank-one Bruhat calculus used for root and torus computations in a
carrier built on the table.

## Main definitions

* `TauCeti.MinusculeWeightTable.sl2BlockMatrix`: the two-by-two block action at a node.
* `TauCeti.MinusculeWeightTable.sl2BlockMatrixHom`, `sl2BlockGL`, `sl2BlockSL`: the resulting
  homomorphisms from the two-by-two matrices, from `GL₂` and from `SL₂`.

## Main results

* `TauCeti.MinusculeWeightTable.sl2BlockMatrix_upper_transvection`,
  `sl2BlockMatrix_lower_transvection`, `sl2BlockMatrix_diagonal`: the values on transvections and
  on diagonal matrices.
* `TauCeti.MinusculeWeightTable.sl2BlockSL_injective`: the representation is faithful as soon as
  the node has a weight of coordinate `-1`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.4.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, Chapter 6.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

variable {B ι : Type*} (T : MinusculeWeightTable B ι)
variable [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- The two-by-two block action at a simple node: `g` acts on each pair of basis vectors whose
coordinates at the node are `1` and `-1`, in that order, and fixes the weight-zero basis
vectors. -/
def sl2BlockMatrix (i : B) (g : Matrix (Fin 2) (Fin 2) R) : Matrix ι ι R :=
  fun a b ↦
    if T.weight b i = 1 then
      g 0 0 * (1 : Matrix ι ι R) a b + g 1 0 * (1 : Matrix ι ι R) a (T.reflection i b)
    else if T.weight b i = -1 then
      g 0 1 * (1 : Matrix ι ι R) a (T.reflection i b) + g 1 1 * (1 : Matrix ι ι R) a b
    else (1 : Matrix ι ι R) a b

omit [Fintype ι] in
/-- The entries of the block action: a column of weight `1` or `-1` carries the matching column
of `g` on the weight pair, and a column of weight zero is the identity column. -/
theorem sl2BlockMatrix_apply (i : B) (g : Matrix (Fin 2) (Fin 2) R) (a b : ι) :
    T.sl2BlockMatrix i g a b =
      if T.weight b i = 1 then
        g 0 0 * (1 : Matrix ι ι R) a b + g 1 0 * (1 : Matrix ι ι R) a (T.reflection i b)
      else if T.weight b i = -1 then
        g 0 1 * (1 : Matrix ι ι R) a (T.reflection i b) + g 1 1 * (1 : Matrix ι ι R) a b
      else (1 : Matrix ι ι R) a b :=
  (rfl)

omit [Fintype ι] in
/-- The block matrix action commutes with homomorphisms of coefficient rings. -/
@[simp]
theorem map_sl2BlockMatrix {S : Type*} [CommRing S]
    (f : R →+* S) (i : B) (g : Matrix (Fin 2) (Fin 2) R) :
    (T.sl2BlockMatrix i g).map f = T.sl2BlockMatrix i (g.map f) := by
  have hone (a b : ι) :
      f ((1 : Matrix ι ι R) a b) = (1 : Matrix ι ι S) a b :=
    congrFun (congrFun (Matrix.map_one f (map_zero f) (map_one f)) a) b
  ext a b
  simp only [Matrix.map_apply, sl2BlockMatrix_apply]
  split_ifs <;> simp only [map_add, map_mul, hone]

private theorem mul_sl2BlockMatrix_apply (i : B) (g : Matrix (Fin 2) (Fin 2) R)
    (M : Matrix ι ι R) (a b : ι) :
    (M * T.sl2BlockMatrix i g) a b =
      if T.weight b i = 1 then g 0 0 * M a b + g 1 0 * M a (T.reflection i b)
      else if T.weight b i = -1 then g 0 1 * M a (T.reflection i b) + g 1 1 * M a b
      else M a b := by
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with h | h | h
  all_goals simp [sl2BlockMatrix_apply, h, Matrix.mul_apply, Matrix.one_apply,
    mul_add, mul_ite, Finset.sum_add_distrib, mul_comm]

omit [Fintype ι] in
/-- The block action preserves the identity matrix. -/
@[simp]
theorem sl2BlockMatrix_one (i : B) : T.sl2BlockMatrix i (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext a b
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with h | h | h
  all_goals simp [sl2BlockMatrix_apply, h]

/-- The block action preserves multiplication. -/
@[simp]
theorem sl2BlockMatrix_mul (i : B) (g h : Matrix (Fin 2) (Fin 2) R) :
    T.sl2BlockMatrix i (g * h) = T.sl2BlockMatrix i g * T.sl2BlockMatrix i h := by
  ext a b
  rw [mul_sl2BlockMatrix_apply]
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with hb | hb | hb
  all_goals simp only [sl2BlockMatrix_apply, hb, T.weight_reflection_self, neg_neg, neg_zero,
    Matrix.mul_apply, Fin.sum_univ_two, Int.reduceNeg, Int.reduceEq, ite_true, ite_false]
  all_goals rw [T.reflection_apply_apply]
  all_goals ring

/-- The multiplicative two-by-two block representation at a simple node. -/
def sl2BlockMatrixHom (i : B) : Matrix (Fin 2) (Fin 2) R →* Matrix ι ι R where
  toFun := T.sl2BlockMatrix i
  map_one' := T.sl2BlockMatrix_one i
  map_mul' := T.sl2BlockMatrix_mul i

/-- The block representation evaluates to the block action. -/
@[simp]
theorem sl2BlockMatrixHom_apply (i : B) (g : Matrix (Fin 2) (Fin 2) R) :
    T.sl2BlockMatrixHom i g = T.sl2BlockMatrix i g :=
  (rfl)

omit [Fintype ι] in
/-- A weight of coordinate `-1` at the node makes the block action faithful. -/
theorem sl2BlockMatrix_injective (i : B) (hi : ∃ a, T.weight a i = -1) :
    Function.Injective (T.sl2BlockMatrix i : Matrix (Fin 2) (Fin 2) R → Matrix ι ι R) := by
  obtain ⟨a, ha⟩ := hi
  have hs : T.weight (T.reflection i a) i = 1 := by simp [ha]
  have hne : T.reflection i a ≠ a := by
    intro h
    rw [h, ha] at hs
    omega
  intro g h hgh
  ext j k
  have he := congrFun (congrFun hgh (if j = 0 then T.reflection i a else a))
    (if k = 0 then T.reflection i a else a)
  fin_cases j <;> fin_cases k <;>
    simpa [sl2BlockMatrix_apply, ha, hs, Matrix.one_apply, hne, hne.symm] using he

/-- Restriction of the block representation to invertible matrices. -/
def sl2BlockGL (i : B) : GL (Fin 2) R →* GL ι R :=
  Units.map (T.sl2BlockMatrixHom i)

/-- The matrix underlying the block representation of an invertible matrix. -/
@[simp]
theorem coe_sl2BlockGL (i : B) (g : GL (Fin 2) R) :
    (T.sl2BlockGL i g : Matrix ι ι R) = T.sl2BlockMatrix i (g : Matrix (Fin 2) (Fin 2) R) := by
  simp only [sl2BlockGL, Units.coe_map, sl2BlockMatrixHom_apply]

/-- A weight of coordinate `-1` at the node makes the general-linear block representation
faithful. -/
theorem sl2BlockGL_injective (i : B) (hi : ∃ a, T.weight a i = -1) :
    Function.Injective (T.sl2BlockGL i : GL (Fin 2) R → GL ι R) :=
  Units.map_injective (T.sl2BlockMatrix_injective i hi)

/-- Restriction of the block representation to the special linear group. -/
def sl2BlockSL (i : B) : Matrix.SpecialLinearGroup (Fin 2) R →* GL ι R :=
  (T.sl2BlockGL i).comp Matrix.SpecialLinearGroup.toGL

/-- The matrix underlying the special-linear block representation. -/
@[simp]
theorem coe_sl2BlockSL (i : B) (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    (T.sl2BlockSL i g : Matrix ι ι R) = T.sl2BlockMatrix i (g : Matrix (Fin 2) (Fin 2) R) := by
  simp only [sl2BlockSL, MonoidHom.comp_apply, coe_sl2BlockGL,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

/-- The special-linear block action is natural in its coefficient ring. -/
@[simp]
theorem map_sl2BlockSL {S : Type*} [CommRing S]
    (f : R →+* S) (i : B) (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    Matrix.GeneralLinearGroup.map f (T.sl2BlockSL i g) =
      T.sl2BlockSL i (Matrix.SpecialLinearGroup.map f g) := by
  apply Units.ext
  ext a b
  simp only [Matrix.GeneralLinearGroup.map_apply, coe_sl2BlockSL,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  exact congrFun (congrFun (T.map_sl2BlockMatrix f i g.val) a) b

/-- A weight of coordinate `-1` at the node makes the special-linear block representation
faithful. -/
theorem sl2BlockSL_injective (i : B) (hi : ∃ a, T.weight a i = -1) :
    Function.Injective (T.sl2BlockSL i : Matrix.SpecialLinearGroup (Fin 2) R → GL ι R) := by
  rw [sl2BlockSL, MonoidHom.coe_comp]
  exact (T.sl2BlockGL_injective i hi).comp Matrix.SpecialLinearGroup.toGL_injective

omit [Fintype ι] in
/-- The upper transvection of `SL₂` acts by the parameterized raising unipotent. -/
theorem sl2BlockMatrix_upper_transvection (i : B) (t : R) :
    T.sl2BlockMatrix i
        (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t :
          Matrix (Fin 2) (Fin 2) R) =
      1 + t • (T.raisingMatrix i).map (Int.cast : ℤ → R) := by
  ext a b
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with hb | hb | hb
  all_goals simp [sl2BlockMatrix_apply, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.one_apply, hb, Matrix.smul_apply, smul_eq_mul, add_comm]

omit [Fintype ι] in
/-- The lower transvection of `SL₂` acts by the parameterized lowering unipotent. -/
theorem sl2BlockMatrix_lower_transvection (i : B) (t : R) :
    T.sl2BlockMatrix i
        (Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t :
          Matrix (Fin 2) (Fin 2) R) =
      1 + t • (T.loweringMatrix i).map (Int.cast : ℤ → R) := by
  ext a b
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with hb | hb | hb
  all_goals simp [sl2BlockMatrix_apply, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.one_apply, hb, Matrix.smul_apply, smul_eq_mul]

omit [Fintype ι] in
/-- A diagonal two-by-two matrix acts diagonally according to the three weights. -/
theorem sl2BlockMatrix_diagonal (i : B) (d : Fin 2 → R) :
    T.sl2BlockMatrix i (Matrix.diagonal d) = Matrix.diagonal (fun a ↦
      if T.weight a i = 1 then d 0 else if T.weight a i = -1 then d 1 else 1) := by
  ext a b
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with hb | hb | hb
  all_goals by_cases hab : a = b
  all_goals simp [sl2BlockMatrix_apply, Matrix.one_apply, hb, hab]

end TauCeti.MinusculeWeightTable
