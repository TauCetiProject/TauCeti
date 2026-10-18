/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import TauCeti.Algebra.Bigraded.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic

/-!
# Ext Poincaré series

For objects `X` and `Y` of a `k`-linear abelian category with a grading-shift autoequivalence
`e`, the **bigraded Ext Poincaré series** records every finite dimension `dim_k Extⁿ(X,Y{j})` in
bidegree `(n,j)`.  It is truncated below a cohomological degree `b`; when `b` is a vanishing
bound, it records the complete bigraded Ext space.  Its support is diagonal exactly when all
off-diagonal groups `Extⁿ(X,Y{j})`, `n ≠ j`, vanish.

For graded modules `M` and `N`, the **diagonal Ext Poincaré polynomial**
`TauCeti.diagonalExtPoincarePolynomial` is `∑ n < b, finrank_k Extⁿ(M,N{n}) tⁿ`, truncated below
a cohomological degree `b`. It records only the diagonal bigraded pieces `Ext^{n,n}(M,N)`. The
coefficients use the `Module.finrank` convention: they are the dimensions `dim_k Extⁿ(M,N{n})`
when these Ext spaces are finite-dimensional, and an infinite-dimensional Ext group contributes
`0`. For a family `S` of graded modules, `TauCeti.diagonalExtPoincareMatrix` collects these
polynomials into a matrix with `(i, j)` entry the polynomial of `(Sᵢ, Sⱼ)`.

The bigraded series takes the finite-internal-support witness needed to make every coefficient
finite and every slice finitely supported.  It is independent of `b` past a cohomological
vanishing bound (`TauCeti.bigradedExtPoincareSeries_eq_of_le`).  The diagonal polynomial and
matrix are defined for arbitrary graded modules and are likewise independent of a sufficiently
large `b` (`TauCeti.diagonalExtPoincarePolynomial_eq_of_le` and
`TauCeti.diagonalExtPoincareMatrix_eq_of_le`).

## Main definitions and results

* `TauCeti.bigradedExtPoincareSeries`: the complete truncated bigraded dimension of Ext, with
  its defining double sum `TauCeti.bigradedExtPoincareSeries_def`.
* `TauCeti.bigradedExtPoincareMatrix`: the full bigraded Ext Poincaré matrix of a family.
* `TauCeti.isDiagonal_bigradedExtPoincareSeries_iff`: diagonal support is equivalent to
  off-diagonal Ext-vanishing when the truncation is a vanishing bound.
* `TauCeti.diagonalExtPoincarePolynomial` and `TauCeti.diagonalExtPoincareMatrix`: the
  one-variable diagonal series and its matrix for a family of modules.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Sections 1.2 and 2.11, for bigraded Ext, its diagonal, and the Poincaré series of diagonal Ext.
-/

public section

namespace TauCeti

open AddMonoidAlgebra CategoryTheory CategoryTheory.Abelian

universe w v uk uA u v' t

section Bigraded

variable {C : Type u} [Category.{v'} C] [Abelian C]
  {k : Type t} [Field k] [Linear k C] [HasExt.{w} C] {e : C ≌ C} {X Y : C} {I : Type*}

variable (k e) in
/-- The **bigraded Ext Poincaré series** of two objects, truncated below cohomological
degree `b`.  Its coefficient in bidegree `(n,j)` is `dim_k Extⁿ(X,Y{j})` for `n < b` and zero
otherwise, where `{j}` is the `j`-fold power of the grading-shift autoequivalence `e`.  The
finite internal support hypothesis makes every cohomological slice a genuine finite sum. -/
noncomputable def bigradedExtPoincareSeries (h : IsGradedExtInternallyFinite.{w} k e X Y)
    (b : ℕ) : Bigraded.Series :=
  ∑ n ∈ Finset.range b,
    ∑ j ∈ (h.finiteLaurentSupport n).finite_finrankSupport.toFinset,
      single ((n : ℤ), j) (Module.finrank k (GradedExt.{w} e X Y n j))

variable (k e) in
/-- The bigraded Ext Poincaré series is the truncated double sum of the monomials
`dim_k Extⁿ(X,Y{j}) · (n,j)` over the finite internal support of each cohomological degree. -/
theorem bigradedExtPoincareSeries_def (h : IsGradedExtInternallyFinite.{w} k e X Y) (b : ℕ) :
    bigradedExtPoincareSeries.{w} k e h b =
      ∑ n ∈ Finset.range b,
        ∑ j ∈ (h.finiteLaurentSupport n).finite_finrankSupport.toFinset,
          single ((n : ℤ), j) (Module.finrank k (GradedExt.{w} e X Y n j)) := by
  rw [bigradedExtPoincareSeries]

variable (k e) in
/-- The coefficient of the bigraded Ext Poincaré series in bidegree `(n,j)` is
`dim_k Extⁿ(X,Y{j})` below the truncation degree and zero from it on. -/
@[simp]
theorem coeff_bigradedExtPoincareSeries (h : IsGradedExtInternallyFinite.{w} k e X Y)
    (b n : ℕ) (j : ℤ) :
    (bigradedExtPoincareSeries.{w} k e h b).coeff ((n : ℤ), j) =
      if n < b then Module.finrank k (GradedExt.{w} e X Y n j) else 0 := by
  classical
  simp only [bigradedExtPoincareSeries_def, coeff_sum, Finsupp.finsetSum_apply, coeff_single,
    Finsupp.single_apply, Prod.mk.injEq, Nat.cast_inj, ite_and, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_range, Set.Finite.mem_toFinset,
    Function.mem_support]
  split_ifs <;> simp_all

variable (k e) in
/-- The bigraded Ext Poincaré series has no negative cohomological degrees. -/
@[simp]
theorem coeff_bigradedExtPoincareSeries_negSucc (h : IsGradedExtInternallyFinite.{w} k e X Y)
    (b n : ℕ) (j : ℤ) :
    (bigradedExtPoincareSeries.{w} k e h b).coeff (Int.negSucc n, j) = 0 := by
  classical
  simp [bigradedExtPoincareSeries]

/-- Raising the truncation degree past a cohomological vanishing bound does not change the
bigraded Ext Poincaré series. -/
theorem bigradedExtPoincareSeries_eq_of_le (h : IsGradedExtInternallyFinite.{w} k e X Y)
    {b b' : ℕ} (hb : IsGradedExtBoundedBy.{w} e X Y b) (hbb' : b ≤ b') :
    bigradedExtPoincareSeries.{w} k e h b' = bigradedExtPoincareSeries.{w} k e h b := by
  ext g
  obtain ⟨m, j⟩ := g
  by_cases hm : 0 ≤ m
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [coeff_bigradedExtPoincareSeries k e h b' n j,
      coeff_bigradedExtPoincareSeries k e h b n j]
    by_cases hn : n < b
    · simp [hn, hn.trans_le hbb']
    · have hbn : b ≤ n := Nat.le_of_not_gt hn
      let _ := hb.subsingleton hbn j
      simp [hn, Module.finrank_zero_of_subsingleton]
  · cases m with
    | ofNat n => exact (hm (Int.natCast_nonneg n)).elim
    | negSucc n =>
        rw [coeff_bigradedExtPoincareSeries_negSucc,
          coeff_bigradedExtPoincareSeries_negSucc]

/-- With a genuine cohomological vanishing bound, the bigraded Ext Poincaré series is diagonal
exactly when every off-diagonal bigraded Ext group vanishes. -/
theorem isDiagonal_bigradedExtPoincareSeries_iff (h : IsGradedExtInternallyFinite.{w} k e X Y)
    {b : ℕ} (hb : IsGradedExtBoundedBy.{w} e X Y b) :
    Bigraded.IsDiagonal (bigradedExtPoincareSeries.{w} k e h b) ↔
      ∀ (n : ℕ) (j : ℤ), (n : ℤ) ≠ j → Subsingleton (GradedExt.{w} e X Y n j) := by
  constructor
  · intro hdiag n j hnj
    by_cases hn : n < b
    · let _ := (h.finiteLaurentSupport n).finiteDimensional j
      rw [← Module.finrank_zero_iff (R := k) (M := GradedExt.{w} e X Y n j)]
      have := (Bigraded.isDiagonal_iff _).1 hdiag (n : ℤ) j hnj
      simpa [hn] using this
    · exact hb.subsingleton (Nat.le_of_not_gt hn) j
  · intro hoff
    rw [Bigraded.isDiagonal_iff]
    intro m j hmj
    by_cases hm : 0 ≤ m
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      rw [coeff_bigradedExtPoincareSeries k e h b n j]
      split
      · let _ := hoff n j hmj
        exact Module.finrank_zero_of_subsingleton (R := k) (M := GradedExt.{w} e X Y n j)
      · rfl
    · cases m with
      | ofNat n => exact (hm (Int.natCast_nonneg n)).elim
      | negSucc n =>
          rw [coeff_bigradedExtPoincareSeries_negSucc]

variable (S : I → C) in
/-- The **full bigraded Ext Poincaré matrix** of a family, truncated below a common
cohomological degree `b`. Its `(i,j)` entry records all dimensions
`dim_k Ext^n(S_i,S_j{p})`, not only the diagonal terms `n = p`. -/
noncomputable def bigradedExtPoincareMatrix
    (h : ∀ i j, IsGradedExtInternallyFinite.{w} k e (S i) (S j))
    (b : ℕ) : Matrix I I Bigraded.Series :=
  fun i j ↦ bigradedExtPoincareSeries.{w} k e (h i j) b

/-- An entry of the full bigraded Ext Poincaré matrix is the bigraded Ext Poincaré series of the
corresponding pair. -/
@[simp]
theorem bigradedExtPoincareMatrix_apply
    (S : I → C) (h : ∀ i j, IsGradedExtInternallyFinite.{w} k e (S i) (S j))
    (b : ℕ) (i j : I) :
    bigradedExtPoincareMatrix S h b i j = bigradedExtPoincareSeries.{w} k e (h i j) b :=
  (rfl)

/-- Raising the common truncation degree past a common cohomological vanishing bound does not
change the full bigraded Ext Poincaré matrix. -/
theorem bigradedExtPoincareMatrix_eq_of_le
    (S : I → C) (h : ∀ i j, IsGradedExtInternallyFinite.{w} k e (S i) (S j)) {b b' : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{w} e (S i) (S j) b) (hbb' : b ≤ b') :
    bigradedExtPoincareMatrix S h b' = bigradedExtPoincareMatrix S h b :=
  Matrix.ext fun i j ↦ bigradedExtPoincareSeries_eq_of_le (h i j) (hb i j) hbb'

end Bigraded

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {M N : GradedModuleCat.{v} 𝒜} [HasExt.{w} (GradedModuleCat.{v} 𝒜)]
  {I : Type*}

variable (k) in
/-- The **diagonal Ext Poincaré polynomial** `∑ n < b, finrank_k Extⁿ(M,N{n}) tⁿ` of two graded
modules, truncated below the cohomological degree `b`. Its coefficients are `Module.finrank`, so
they are the dimensions `dim_k Extⁿ(M,N{n})` when these are finite-dimensional and `0` otherwise.
It records only the diagonal bigraded pieces `Ext^{n,n}(M,N)`; when `M` has a linear resolution
and `N` is concentrated in degree zero, these are the only nonzero pieces. -/
noncomputable def diagonalExtPoincarePolynomial (M N : GradedModuleCat.{v} 𝒜) (b : ℕ) :
    Polynomial ℤ :=
  ∑ n ∈ Finset.range b, Polynomial.monomial n (Module.finrank k (Ext.{w} M (N.shiftObj n) n) : ℤ)

variable (k) in
/-- The diagonal Ext Poincaré polynomial is the truncated sum of the monomials
`finrank_k Extⁿ(M,N{n}) tⁿ`. -/
theorem diagonalExtPoincarePolynomial_def (M N : GradedModuleCat.{v} 𝒜) (b : ℕ) :
    diagonalExtPoincarePolynomial.{w} k M N b =
      ∑ n ∈ Finset.range b,
        Polynomial.monomial n (Module.finrank k (Ext.{w} M (N.shiftObj n) n) : ℤ) := by
  rw [diagonalExtPoincarePolynomial]

variable (k) in
/-- The coefficient of `tⁿ` in the diagonal Ext Poincaré polynomial is `finrank_k Extⁿ(M,N{n})`
(the dimension when this Ext space is finite-dimensional, `0` otherwise) below the truncation
degree, and zero from it on. -/
@[simp]
theorem coeff_diagonalExtPoincarePolynomial (M N : GradedModuleCat.{v} 𝒜) (b n : ℕ) :
    (diagonalExtPoincarePolynomial.{w} k M N b).coeff n =
      if n < b then (Module.finrank k (Ext.{w} M (N.shiftObj n) n) : ℤ) else 0 := by
  simp [diagonalExtPoincarePolynomial_def, Polynomial.coeff_monomial]

/-- The diagonal Ext Poincaré polynomial is unchanged by raising its truncation degree past a
cohomological vanishing bound. -/
theorem diagonalExtPoincarePolynomial_eq_of_le {b b' : ℕ}
    (hb : IsGradedExtBoundedBy.{w} (GradedModuleCat.shift 𝒜) M N b) (hbb' : b ≤ b') :
    diagonalExtPoincarePolynomial.{w} k M N b' = diagonalExtPoincarePolynomial.{w} k M N b := by
  refine (Finset.sum_subset (Finset.range_subset_range.2 hbb') fun n _ hn ↦ ?_).symm
  have : Subsingleton (Ext.{w} M (N.shiftObj n) n) := by
    have := hb.subsingleton (by simpa using hn) n
    rw [← GradedModuleCat.shiftFunctor_obj]
    exact (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 n).app N) n).symm.injective.subsingleton
  simp [Module.finrank_zero_of_subsingleton]

variable (k) in
/-- The **diagonal Ext Poincaré matrix** of a family `S` of graded modules, truncated below the
cohomological degree `b`: its `(i, j)` entry is the diagonal Ext Poincaré polynomial
`∑ n < b, finrank_k Extⁿ(Sᵢ, Sⱼ{n}) tⁿ`, whose coefficients are Ext dimensions when these are
finite-dimensional (`Module.finrank` convention). -/
noncomputable def diagonalExtPoincareMatrix (S : I → GradedModuleCat.{v} 𝒜) (b : ℕ) :
    Matrix I I (Polynomial ℤ) :=
  Matrix.of fun i j ↦ diagonalExtPoincarePolynomial.{w} k (S i) (S j) b

variable (k) in
/-- An entry of the diagonal Ext Poincaré matrix is the diagonal Ext Poincaré polynomial of the
corresponding pair. -/
@[simp]
theorem diagonalExtPoincareMatrix_apply (S : I → GradedModuleCat.{v} 𝒜) (b : ℕ)
    (i j : I) :
    diagonalExtPoincareMatrix.{w} k S b i j =
      diagonalExtPoincarePolynomial.{w} k (S i) (S j) b := by
  rw [diagonalExtPoincareMatrix, Matrix.of_apply]

/-- The diagonal Ext Poincaré matrix is unchanged by raising its truncation degree past a common
cohomological vanishing bound of all pairs in the family. -/
theorem diagonalExtPoincareMatrix_eq_of_le {S : I → GradedModuleCat.{v} 𝒜}
    {b b' : ℕ} (hb : ∀ i j, IsGradedExtBoundedBy.{w} (GradedModuleCat.shift 𝒜) (S i) (S j) b)
    (hbb' : b ≤ b') :
    diagonalExtPoincareMatrix.{w} k S b' = diagonalExtPoincareMatrix.{w} k S b :=
  Matrix.ext fun i j ↦ diagonalExtPoincarePolynomial_eq_of_le (hb i j) hbb'

end TauCeti
