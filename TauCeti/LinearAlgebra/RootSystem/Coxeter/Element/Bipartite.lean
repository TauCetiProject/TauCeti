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

## Main definitions
* `RootPairing.Base.colorClassMatrix`, `RootPairing.Base.bipartiteCoxeterMatrix`: integer matrices
  for the colour-class involutions and bipartite Coxeter element.

## Main results
* `RootPairing.Base.colorClassMatrix_apply`, `RootPairing.Base.colorClassMatrix_mul_self`:
  explicit entries and involutivity of `b.colorClassMatrix col s`.
* `RootPairing.Base.actsBy_colorClassProd`, `RootPairing.Base.actsBy_bipartiteCoxeterElement`,
  `RootPairing.Base.actsBy_bipartiteCoxeterElement_inv`: `ActsBy` relations for colour-class
  involutions and the bipartite Coxeter element and its inverse.

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
@[simp]
theorem colorClassMatrix_apply (s : Bool) (k j : b.support) :
    b.colorClassMatrix col s k j =
      (if k = j then 1 else 0) - (if col k = s then b.cartanMatrix j k else 0) := by
  let fs := Finset.univ.filter fun i : b.support ↦ col i = s
  simpa [colorClassMatrix, fs] using
    prod_map_reflMatrix_apply_of_orthogonal b.cartanMatrix (Finset.nodup_toList fs)
      (fun p hp q hq hpq ↦ b.cartanMatrix_eq_zero_of_color_eq col hpq
        ((Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2.trans
          (Finset.mem_filter.mp (Finset.mem_toList.mp hq)).2.symm)) k j

/-- `b.colorClassMatrix col s` is an involution (`M * M = 1`). -/
@[simp]
theorem colorClassMatrix_mul_self (s : Bool) :
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
