/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation

/-!
# Matrices of colour-class involutions and bipartite Coxeter elements

Given a two-colouring `col` of the Coxeter graph of a base `b`, we construct the integer matrices
`b.colorClassMatrix col s` and `b.bipartiteCoxeterMatrix col` and prove their `ActsBy` relations.

## Main definitions and results
* `RootPairing.Base.colorClassMatrix`, `RootPairing.Base.bipartiteCoxeterMatrix`: integer matrices
  for the colour-class involutions and bipartite Coxeter element, with entries
  (`colorClassMatrix_apply`), involutivity (`colorClassMatrix_mul_self`), colour-part actions
  (`corootEval_ite_color`, `colorClassMatrix_mulVec_ite_color`,
  `bipartiteCoxeterMatrix_mulVec_ite_color_true`, `bipartiteCoxeterMatrix_mulVec_ite_color_false`),
  and `ActsBy` relations (`actsBy_colorClassProd`, `actsBy_bipartiteCoxeterElement`,
  `actsBy_bipartiteCoxeterElement_inv`).

## References
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2;
  J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §§ 3.16–3.17.
-/

public section

open Matrix TauCeti

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [DecidableEq ι]
  (b : P.Base) (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)

/-- Integer matrix of `colorClassProd col s` in the simple-root basis. -/
noncomputable def colorClassMatrix (s : Bool) : Matrix b.support b.support ℤ :=
  (((Finset.univ.filter fun i : b.support ↦ col i = s).toList).map (reflMatrix b.cartanMatrix)).prod

/-- Explicit entries of `b.colorClassMatrix col s` in terms of `b.cartanMatrix`. -/
@[simp] theorem colorClassMatrix_apply (s : Bool) (k j : b.support) :
    b.colorClassMatrix col s k j =
      (if k = j then 1 else 0) - (if col k = s then b.cartanMatrix j k else 0) := by
  rw [colorClassMatrix, prod_map_reflMatrix_apply_of_orthogonal b.cartanMatrix
    (Finset.nodup_toList _) (fun p hp q hq hpq ↦
      b.cartanMatrix_eq_zero_of_color_eq col hpq (by simp_all)) k j]; simp

/-- `b.colorClassMatrix col s` is an involution (`M * M = 1`). -/
@[simp] theorem colorClassMatrix_mul_self (s : Bool) :
    b.colorClassMatrix col s * b.colorClassMatrix col s = 1 := by
  ext k j; simp only [Matrix.mul_apply, colorClassMatrix_apply, Matrix.one_apply]
  by_cases hck : col k = s
  · simp only [hck, ↓reduceIte, sub_mul, mul_sub, ite_mul, mul_ite, one_mul, mul_one, zero_mul,
      mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
    rw [Finset.sum_eq_single k (fun x _ hxk ↦ by
      by_cases hcx : col x = s
      · simp [hcx, hxk.symm, b.cartanMatrix_eq_zero_of_color_eq col hxk (hcx.trans hck.symm)]
      · simp [hcx]) (by simp)]
    simp [hck]; ring
  · simp [hck]

/-- Integer matrix of the bipartite Coxeter element in the simple-root basis. -/
noncomputable def bipartiteCoxeterMatrix : Matrix b.support b.support ℤ :=
  b.colorClassMatrix col true * b.colorClassMatrix col false

omit [CharZero R] [IsDomain R] [Finite ι] in
/-- Explicit factorization of `b.bipartiteCoxeterMatrix col` into the two colour-class matrices. -/
theorem bipartiteCoxeterMatrix_def :
    b.bipartiteCoxeterMatrix col = b.colorClassMatrix col true * b.colorClassMatrix col false :=
  (rfl)

omit [DecidableEq ι] in
/-- On a left `κ`-eigenvector `y` of `b.cartanMatrix`, a simple coroot `k` evaluates on the
colour-`z` part of `y` to `2 * y k` when `col k = z` and `(κ - 2) * y k` otherwise. -/
theorem corootEval_ite_color {S : Type*} [CommRing S] {y : b.support → S} {κ : S}
    (hy : y ᵥ* b.cartanMatrix.map (Int.castRingHom S) = κ • y) (z : Bool) (k : b.support) :
    b.corootEval S (k : ι) (fun i ↦ if col i = z then y i else 0) =
      (if col k = z then 2 else κ - 2) * y k := by
  classical
  have hsame (t : Bool) (ht : col k = t) :
      b.corootEval S (k : ι) (fun i ↦ if col i = t then y i else 0) = 2 * y k := by
    rw [corootEval_coe_support, Finset.sum_eq_single k (fun i _ hik ↦ by
      split_ifs with hi
      · simp [b.cartanMatrix_eq_zero_of_color_eq col hik (hi.trans ht.symm)]
      · simp) (by simp)]
    simp [ht]
  split_ifs with hkz
  · exact hsame z hkz
  · have hsum_z : (fun i ↦ if col i = z then y i else 0) +
        (fun i ↦ if col i = !z then y i else 0) = y :=
      funext fun i ↦ by by_cases hci : col i = z <;> simp [hci]
    have htot : b.corootEval S (k : ι) (fun i ↦ if col i = z then y i else 0) +
        b.corootEval S (k : ι) (fun i ↦ if col i = !z then y i else 0) = κ * y k := by
      rw [← map_add, hsum_z, corootEval_coe_support]
      simpa [vecMul, dotProduct, mul_comm] using congrFun hy k
    rw [hsame (!z) (by cases hck : col k <;> cases z <;> simp_all)] at htot
    exact (eq_sub_of_add_eq htot).trans (by ring)

/-- On a left `κ`-eigenvector `y` of `b.cartanMatrix`, the colour-`s` matrix
`b.colorClassMatrix col s` sends the colour-`z` part of `y` to itself minus
`(if z = s then 2 else κ - 2)` times the colour-`s` part of `y`. -/
theorem colorClassMatrix_mulVec_ite_color {S : Type*} [CommRing S] {y : b.support → S} {κ : S}
    (hy : y ᵥ* b.cartanMatrix.map (Int.castRingHom S) = κ • y) (s z : Bool) :
    (b.colorClassMatrix col s).map (Int.castRingHom S) *ᵥ
        (fun i ↦ if col i = z then y i else 0) =
      (fun i ↦ if col i = z then y i else 0) -
        (if z = s then 2 else κ - 2) • (fun i ↦ if col i = s then y i else 0) := by
  ext k; simp only [mulVec, dotProduct, map_apply, Int.coe_castRingHom, colorClassMatrix_apply,
    Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  by_cases hck : col k = s
  · have hsum : (∑ x, if col k = s then (b.cartanMatrix x k : S) * if col x = z then y x else 0
        else 0) = (if col k = z then 2 else κ - 2) * y k := by
      rw [← b.corootEval_ite_color col hy z k, b.corootEval_coe_support]; simp [hck]
    rw [hsum]
    rcases eq_or_ne z s with rfl | hzs <;> [simp [hck]; simp [hck, hzs, hzs.symm]]
  · rcases eq_or_ne z s with rfl | hzs <;> simp [*]

/-- On a left `κ`-eigenvector `y` of `b.cartanMatrix`, `b.bipartiteCoxeterMatrix col` sends the
`true`-colour part `u₀` of `y` to `((2 - κ) ^ 2 - 1) • u₀ + (2 - κ) • u₁`. -/
theorem bipartiteCoxeterMatrix_mulVec_ite_color_true {S : Type*} [CommRing S] {y : b.support → S}
    {κ : S} (hy : y ᵥ* b.cartanMatrix.map (Int.castRingHom S) = κ • y) :
    (b.bipartiteCoxeterMatrix col).map (Int.castRingHom S) *ᵥ
        (fun i ↦ if col i = true then y i else 0) =
      ((2 - κ) ^ 2 - 1) • (fun i ↦ if col i = true then y i else 0) +
        (2 - κ) • (fun i ↦ if col i = false then y i else 0) := by
  rw [b.bipartiteCoxeterMatrix_def, Matrix.map_mul, ← mulVec_mulVec,
    b.colorClassMatrix_mulVec_ite_color col hy false true]
  simp only [Bool.true_eq_false, ↓reduceIte, mulVec_sub, mulVec_smul,
    b.colorClassMatrix_mulVec_ite_color col hy true true,
    b.colorClassMatrix_mulVec_ite_color col hy true false, Bool.false_eq_true]
  ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- On a left `κ`-eigenvector `y` of `b.cartanMatrix`, `b.bipartiteCoxeterMatrix col` sends the
`false`-colour part `u₁` of `y` to `-u₁ - (2 - κ) • u₀`. -/
theorem bipartiteCoxeterMatrix_mulVec_ite_color_false {S : Type*} [CommRing S] {y : b.support → S}
    {κ : S} (hy : y ᵥ* b.cartanMatrix.map (Int.castRingHom S) = κ • y) :
    (b.bipartiteCoxeterMatrix col).map (Int.castRingHom S) *ᵥ
        (fun i ↦ if col i = false then y i else 0) =
      -(fun i ↦ if col i = false then y i else 0) -
        (2 - κ) • (fun i ↦ if col i = true then y i else 0) := by
  rw [b.bipartiteCoxeterMatrix_def, Matrix.map_mul, ← mulVec_mulVec,
    b.colorClassMatrix_mulVec_ite_color col hy false false]
  simp only [↓reduceIte, mulVec_sub, mulVec_smul,
    b.colorClassMatrix_mulVec_ite_color col hy true false, Bool.false_eq_true]
  ext i; simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring

variable [P.IsReduced]

/-- The colour-class involution `colorClassProd col s` acts by `b.colorClassMatrix col s`. -/
theorem actsBy_colorClassProd (s : Bool) :
    b.ActsBy ((weylCoxeterSystem P b).colorClassProd col s) (b.colorClassMatrix col s) := by
  let fs := Finset.univ.filter fun i : b.support ↦ col i = s
  rw [← (weylCoxeterSystem P b).wordProd_eq_colorClassProd col (Finset.nodup_toList fs)
    (by simp [fs]), weylCoxeterSystem_wordProd]
  exact b.actsBy_wordProd fs.toList

/-- The bipartite Coxeter element acts on the simple roots by `b.bipartiteCoxeterMatrix col`. -/
theorem actsBy_bipartiteCoxeterElement :
    b.ActsBy ((weylCoxeterSystem P b).bipartiteCoxeterElement col)
      (b.bipartiteCoxeterMatrix col) := by
  rw [CoxeterSystem.bipartiteCoxeterElement_def, b.bipartiteCoxeterMatrix_def]
  exact (b.actsBy_colorClassProd col true).mul (b.actsBy_colorClassProd col false)

/-- The inverse bipartite Coxeter element acts by swapping the two colour-class matrices. -/
theorem actsBy_bipartiteCoxeterElement_inv :
    b.ActsBy ((weylCoxeterSystem P b).bipartiteCoxeterElement col)⁻¹
      (b.colorClassMatrix col false * b.colorClassMatrix col true) := by
  rw [CoxeterSystem.bipartiteCoxeterElement_def, _root_.mul_inv_rev,
    CoxeterSystem.colorClassProd_inv, CoxeterSystem.colorClassProd_inv]
  exact (b.actsBy_colorClassProd col false).mul (b.actsBy_colorClassProd col true)

end RootPairing.Base
