/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.LinearAlgebra.ExteriorPower.Plucker
public import TauCeti.LinearAlgebra.Matrix.Minor

import TauCeti.Order.Hom.PowersetCard

/-!
# Compound matrices

For a matrix `A` with rows indexed by a linearly ordered type `ι` and columns indexed by a linearly
ordered type `κ`, the `r`-th compound matrix `Matrix.compound r A` is the matrix of all `r × r`
minors of `A`. It is indexed by the `r`-element subsets `S` of `ι` and `T` of `κ`, given as
elements of Mathlib's `Set.powersetCard`, and its `(S, T)` entry is the minor `det A[S, T]` on the
rows in `S` and the columns in `T`, each listed in increasing order through
`Set.powersetCard.ofFinEmbEquiv`.

The compound matrix is the matrix of the `r`-th exterior power `⋀^r A : ⋀^r R^κ → ⋀^r R^ι` in the
bases `e_{t_1} ∧ ⋯ ∧ e_{t_r}` (`t_1 < ⋯ < t_r`) induced by the standard bases, which are Mathlib's
`Module.Basis.exteriorPower`. Since `⋀^r` is a functor, compound matrices are multiplicative:
`C_r(A B) = C_r(A) C_r(B)` is the Cauchy–Binet formula for all `r × r` minors of a product. It is
deduced here from the Cauchy–Binet formula `TauCeti.det_mul_transpose_eq_sum_plucker_mul` for the
determinant of a product of an `r × κ` and a `κ × r` matrix, so the outer index types need not be
finite.

Compound matrices organise the `r × r` minors of a matrix, which generate the Fitting ideals of
the module it presents and enter the generalised Laplace expansion of a determinant.

## Main definitions

* `Matrix.compound r A`: the `r`-th compound matrix of `A`, the matrix of its `r × r` minors.

## Main results

* `Matrix.compound_eq_toMatrix_exteriorPower_map`: `C_r(A)` is the matrix of
  `exteriorPower.map r (Matrix.toLin' A)` in the exterior-power bases of the standard bases.
* `Matrix.compound_mul`: the Cauchy–Binet formula `C_r(A B) = C_r(A) C_r(B)`.
* `Matrix.compound_one`, `Matrix.compound_transpose`, `Matrix.compound_smul` and
  `Matrix.compound_map`: the identity, transposition, scaling and ring homomorphisms.
* `Matrix.compound_zero_apply`, `Matrix.compound_one_apply_ofSingleton` and
  `Matrix.compound_two_apply`: the zeroth, first and second compounds, the last one through the
  `2 × 2` minors `Matrix.pairMinor`.

## References

* S. Dasgupta and M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. 197 (2023), proof of
  Lemma 3.9.
* N. Bourbaki, *Algebra I*, Chapter III, §8, no. 6.
-/

public section

open Set Set.powersetCard exteriorPower

namespace Matrix

variable {R S : Type*} [CommRing R] [CommRing S]
  {ι κ μ : Type*} [LinearOrder ι] [LinearOrder κ] [LinearOrder μ]

/-- The `r`-th **compound matrix** of `A`: its entry at the `r`-element subsets `S` of the rows and
`T` of the columns is the minor of `A` on the rows in `S` and the columns in `T`, both listed in
increasing order. -/
noncomputable def compound (r : ℕ) (A : Matrix ι κ R) :
    Matrix (powersetCard ι r) (powersetCard κ r) R :=
  of fun S T ↦ (A.submatrix (ofFinEmbEquiv.symm S) (ofFinEmbEquiv.symm T)).det

/-- The entries of the compound matrix are the minors on increasingly listed rows and columns. -/
theorem compound_apply (r : ℕ) (A : Matrix ι κ R) (S : powersetCard ι r) (T : powersetCard κ r) :
    compound r A S T = (A.submatrix (ofFinEmbEquiv.symm S) (ofFinEmbEquiv.symm T)).det :=
  (rfl)

/-- The `0`-th compound matrix has every entry equal to `1`, the empty minor. -/
@[simp]
theorem compound_zero_apply (A : Matrix ι κ R) (S : powersetCard ι 0) (T : powersetCard κ 0) :
    compound 0 A S T = 1 :=
  (compound_apply 0 A S T).trans det_isEmpty

/-- The first compound matrix is the matrix itself, indexed by singletons. -/
@[simp]
theorem compound_one_apply_ofSingleton (A : Matrix ι κ R) (i : ι) (k : κ) :
    compound 1 A (ofSingleton i) (ofSingleton k) = A i k := by
  simp [compound_apply, det_unique, ofFinEmbEquiv_symm_apply, ofSingleton,
    Finset.orderEmbOfFin_singleton]

/-- The entries of the second compound matrix are the `2 × 2` minors `Matrix.pairMinor`, on
increasing pairs of rows and columns. -/
theorem compound_two_apply (A : Matrix ι κ R) {S : powersetCard ι 2} {T : powersetCard κ 2}
    {i j : ι} {k l : κ} (hij : i < j) (hS : (S : Finset ι) = {i, j}) (hkl : k < l)
    (hT : (T : Finset κ) = {k, l}) :
    compound 2 A S T = pairMinor A (i, j) (k, l) := by
  rw [compound_apply, coe_ofFinEmbEquiv_symm_eq_of_val_eq_pair hij hS,
    coe_ofFinEmbEquiv_symm_eq_of_val_eq_pair hkl hT, pairMinor_eq, det_fin_two]
  simp

/-- The compound matrix of the transpose is the transpose of the compound matrix. -/
@[simp]
theorem compound_transpose (r : ℕ) (A : Matrix ι κ R) :
    compound r Aᵀ = (compound r A)ᵀ := by
  ext T S
  rw [transpose_apply, compound_apply, compound_apply, ← det_transpose, transpose_submatrix,
    transpose_transpose]

/-- The compound matrix of the identity matrix is the identity matrix. -/
@[simp]
theorem compound_one (r : ℕ) : compound r (1 : Matrix ι ι R) = 1 := by
  ext S T
  rw [compound_apply]
  by_cases hST : S = T
  · subst hST
    rw [submatrix_one _ (ofFinEmbEquiv.symm S).injective, det_one, one_apply_eq]
  · rw [one_apply_ne hST]
    -- Some element `i` of `S` is not in `T`, and the row of the minor at `i` vanishes.
    obtain ⟨i, hiS, hiT⟩ := (exists_mem_notMem_iff_ne S T).1 hST
    obtain ⟨a, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem S i).2 hiS
    refine det_eq_zero_of_row_eq_zero a fun b ↦ one_apply_ne fun h ↦ hiT ?_
    exact h ▸ (mem_range_ofFinEmbEquiv_symm_iff_mem T _).1 ⟨b, rfl⟩

/-- Scaling a matrix by `c` scales its `r`-th compound matrix by `c ^ r`. -/
@[simp]
theorem compound_smul (r : ℕ) (c : R) (A : Matrix ι κ R) :
    compound r (c • A) = c ^ r • compound r A := by
  ext S T
  simp only [Matrix.smul_apply, compound_apply, submatrix_smul, Pi.smul_apply, det_smul,
    Fintype.card_fin, smul_eq_mul]

/-- A ring homomorphism applied to all entries commutes with taking compound matrices. -/
@[simp]
theorem compound_map (r : ℕ) (f : R →+* S) (A : Matrix ι κ R) :
    compound r (A.map f) = (compound r A).map f := by
  ext S T
  rw [map_apply, compound_apply, compound_apply, submatrix_map, RingHom.map_det,
    RingHom.mapMatrix_apply]

/-- **The Cauchy–Binet formula.** The `r`-th compound matrix of a product is the product of the
`r`-th compound matrices: every `r × r` minor of `A * B` is the sum, over the `r`-element subsets
`T` of the middle index type, of the products of the minors of `A` and of `B` on `T`. -/
@[simp]
theorem compound_mul [Fintype κ] (r : ℕ) (A : Matrix ι κ R) (B : Matrix κ μ R) :
    compound r (A * B) = compound r A * compound r B := by
  ext S U
  -- The minor of `A * B` is the determinant of the product of the rows of `A` in `S` with the
  -- columns of `B` in `U`, which the Plücker form of Cauchy–Binet expands over `r`-subsets of `κ`.
  have h := TauCeti.det_mul_transpose_eq_sum_plucker_mul (fun a k ↦ A (ofFinEmbEquiv.symm S a) k)
    (fun b k ↦ B k (ofFinEmbEquiv.symm U b))
  rw [compound_apply, Matrix.mul_apply]
  convert h using 2
  · ext a b
    simp [Matrix.mul_apply]
  · rw [TauCeti.plucker_apply, TauCeti.plucker_apply, compound_apply, compound_apply,
      ← det_transpose (B.submatrix _ _)]
    refine congrArg₂ (· * ·) (congrArg det (Matrix.ext fun i j ↦ ?_))
      (congrArg det (Matrix.ext fun i j ↦ ?_)) <;>
    simp only [transpose_apply, submatrix_apply, of_apply]

/-- The compound matrix `C_r(A)` is the matrix of the `r`-th exterior power of the linear map
`Matrix.toLin' A : (κ → R) → (ι → R)`, in the bases of `⋀[R]^r (κ → R)` and `⋀[R]^r (ι → R)`
induced by the standard bases. -/
theorem compound_eq_toMatrix_exteriorPower_map [Finite ι] [Fintype κ] (r : ℕ)
    (A : Matrix ι κ R) :
    compound r A = LinearMap.toMatrix ((Pi.basisFun R κ).exteriorPower r)
      ((Pi.basisFun R ι).exteriorPower r) (exteriorPower.map r (toLin' A)) := by
  ext S T
  rw [Module.Basis.toMatrix_exteriorPower_map, ← toLin_eq_toLin', LinearMap.toMatrix_toLin,
    compound_apply, ← det_transpose]
  refine congrArg det (Matrix.ext fun i j ↦ ?_)
  simp only [transpose_apply, submatrix_apply, of_apply]

/-- The second compound of a `2 × 2` matrix is its determinant `a d - b c`, its only entry. -/
example (a b c d : R) (S T : powersetCard (Fin 2) 2) :
    compound 2 !![a, b; c, d] S T = a * d - b * c := by
  have h (U : powersetCard (Fin 2) 2) : (U : Finset (Fin 2)) = {0, 1} :=
    (Finset.eq_univ_of_card _ (mem_iff.1 U.prop)).trans (by decide)
  rw [compound_two_apply _ Fin.zero_lt_one (h S) Fin.zero_lt_one (h T), pairMinor_eq]
  simp

end Matrix
