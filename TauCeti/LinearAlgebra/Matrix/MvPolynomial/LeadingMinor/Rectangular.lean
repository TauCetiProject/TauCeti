/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.MvPolynomial.LeadingMinor.Basic
import TauCeti.LinearAlgebra.Matrix.Block

/-!
# Leading-minor weight vectors on rectangular matrices

A partition supported on the first `min m n` coordinates gives a product of leading minors
of the generic `m × n` matrix. It is a nonzero homogeneous polynomial over a nontrivial
coefficient ring. Under the substitution `X ↦ gᵀ * X * h` with upper triangular `g` and `h`,
it transforms by the two diagonal characters of the partition, padded by zeros in the
larger factor. In particular both upper unitriangular groups fix it. These are the explicit
joint highest weight vectors in the Cauchy decomposition of rectangular matrix forms.

The weight calculation is the leading-minor construction of R. Howe, *Perspectives on
invariant theory*, Israel Math. Conf. Proc. 8 (1995), §2.1. We use the square weight calculation
on the largest common leading block.
-/

public section

open Finset Matrix MvPolynomial

namespace TauCeti

variable {m n : ℕ} {R S : Type*} [CommRing R]

/-- The product of leading minors of a generic `m × n` matrix. For `a : Fin (min m n)`,
`e a` is the exponent of the minor on the first `a + 1` rows and columns. -/
noncomputable def rectangularLeadingMinorProd (R : Type*) [CommRing R]
    (e : Fin (min m n) → ℕ) : MvPolynomial (Fin m × Fin n) R :=
  rename (Prod.map (Fin.castLE (min_le_left m n)) (Fin.castLE (min_le_right m n)))
    (leadingMinorProd R e)

/-- The largest square leading block supplies all the factors of the rectangular product. -/
theorem rectangularLeadingMinorProd_eq_rename (e : Fin (min m n) → ℕ) :
    rectangularLeadingMinorProd R e =
      rename (Prod.map (Fin.castLE (min_le_left m n)) (Fin.castLE (min_le_right m n)))
        (leadingMinorProd R e) := (rfl)

/-- The defining product of generic minors on the common initial segments. -/
theorem rectangularLeadingMinorProd_def (e : Fin (min m n) → ℕ) :
    rectangularLeadingMinorProd R e = ∏ a, (mvPolynomialMinor R
      (fun j : {j : Fin (min m n) // j ≤ a} ↦ Fin.castLE (min_le_left m n) j.val)
      (fun j : {j : Fin (min m n) // j ≤ a} ↦ Fin.castLE (min_le_right m n) j.val)) ^ e a := by
  rw [rectangularLeadingMinorProd_eq_rename, leadingMinorProd_def, map_prod]
  refine prod_congr rfl fun a _ ↦ ?_
  rw [map_pow]
  congr 1
  simp only [mvPolynomialMinor_eq_det_submatrix, AlgHom.map_det]
  congr 1
  ext i j
  simp [Prod.map_apply]

/-- With all exponents zero the rectangular product is `1`. -/
@[simp]
theorem rectangularLeadingMinorProd_zero :
    rectangularLeadingMinorProd R (0 : Fin (min m n) → ℕ) = 1 := by
  simp [rectangularLeadingMinorProd_eq_rename]

/-- Adding the exponent vectors multiplies the rectangular products. -/
theorem rectangularLeadingMinorProd_add (e f : Fin (min m n) → ℕ) :
    rectangularLeadingMinorProd R (e + f) =
      rectangularLeadingMinorProd R e * rectangularLeadingMinorProd R f := by
  simp [rectangularLeadingMinorProd_eq_rename, leadingMinorProd_add]

/-- The rectangular product is homogeneous of degree the sum of the partition coordinates. -/
theorem isHomogeneous_rectangularLeadingMinorProd (e : Fin (min m n) → ℕ) :
    (rectangularLeadingMinorProd R e).IsHomogeneous (∑ j, leadingMinorWeight e j) := by
  rw [rectangularLeadingMinorProd_eq_rename]
  exact (isHomogeneous_leadingMinorProd e).rename_isHomogeneous

/-- Products of rectangular leading minors are nonzero over a nontrivial ring. -/
theorem rectangularLeadingMinorProd_ne_zero [Nontrivial R] (e : Fin (min m n) → ℕ) :
    rectangularLeadingMinorProd R e ≠ 0 := by
  rw [rectangularLeadingMinorProd_eq_rename]
  exact (rename_injective _ ((Fin.castLE_injective _).prodMap (Fin.castLE_injective _))).ne
    (leadingMinorProd_ne_zero e)

/-- With lower triangular `L` and upper triangular `U`, substituting `L * X * U` acts on the
rectangular product by its joint diagonal weight, computed on the common leading indices.
The evaluation matrix can have entries in any commutative `R`-algebra. -/
theorem aeval_rectangularLeadingMinorProd_mul_mul [CommRing S] [Algebra R S]
    {L : Matrix (Fin m) (Fin m) R} {U : Matrix (Fin n) (Fin n) R}
    (hL : L.IsLowerTriangular) (hU : U.IsUpperTriangular)
    (X : Matrix (Fin m) (Fin n) S) (e : Fin (min m n) → ℕ) :
    aeval (fun ij : Fin m × Fin n ↦
      (L.map (algebraMap R S) * X * U.map (algebraMap R S)) ij.1 ij.2)
      (rectangularLeadingMinorProd R e) =
    (∏ j, (L (Fin.castLE (min_le_left m n) j) (Fin.castLE (min_le_left m n) j) *
      U (Fin.castLE (min_le_right m n) j) (Fin.castLE (min_le_right m n) j)) ^
        leadingMinorWeight e j) •
      aeval (fun ij : Fin m × Fin n ↦ X ij.1 ij.2) (rectangularLeadingMinorProd R e) := by
  let r := Fin.castLEEmb (min_le_left m n)
  let c := Fin.castLEEmb (min_le_right m n)
  have hr : IsLowerSet (Set.range r) := by
    rw [Fin.coe_castLEEmb, Fin.range_castLE]
    exact fun _ _ h hi ↦ lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) hi
  have hc : IsLowerSet (Set.range c) := by
    rw [Fin.coe_castLEEmb, Fin.range_castLE]
    exact fun _ _ h hi ↦ lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) hi
  have hblock := submatrix_mul_mul_of_isLowerTriangular_of_isUpperTriangular X
    (hL.map (algebraMap R S)) (hU.map (algebraMap R S)) r c hr hc
  rw [rectangularLeadingMinorProd_eq_rename, aeval_rename, aeval_rename]
  -- The composed evaluation is indexed by the entries of the common leading block.
  change aeval (fun ij : Fin (min m n) × Fin (min m n) ↦
    ((L.map (algebraMap R S) * X * U.map (algebraMap R S)).submatrix r c) ij.1 ij.2) _ = _
  have hL' : (L.submatrix r r).IsLowerTriangular :=
    fun _ _ hij ↦ hL (Fin.strictMono_castLE (min_le_left m n) hij)
  have hU' : (U.submatrix c c).IsUpperTriangular :=
    fun _ _ hij ↦ hU (Fin.strictMono_castLE (min_le_right m n) hij)
  rw [hblock, submatrix_map, submatrix_map, ← aeval_mvPolynomialSubst,
    mvPolynomialSubst_leadingMinorProd hL' hU', map_smul]
  rfl

/-- Under substitution of `gᵀ * X * h` for the generic rectangular matrix `X`, upper
triangular `g` and `h` act on the leading-minor product through its two diagonal weights. -/
theorem aeval_rectangularLeadingMinorProd_transpose_mul_mul
    {g : Matrix (Fin m) (Fin m) R} {h : Matrix (Fin n) (Fin n) R}
    (hg : g.IsUpperTriangular) (hh : h.IsUpperTriangular) (e : Fin (min m n) → ℕ) :
    aeval (fun ij : Fin m × Fin n ↦
      (gᵀ.map C * mvPolynomialX (Fin m) (Fin n) R * h.map C :
        Matrix (Fin m) (Fin n) (MvPolynomial (Fin m × Fin n) R)) ij.1 ij.2)
      (rectangularLeadingMinorProd R e) =
    (∏ j, (g (Fin.castLE (min_le_left m n) j) (Fin.castLE (min_le_left m n) j) *
      h (Fin.castLE (min_le_right m n) j) (Fin.castLE (min_le_right m n) j)) ^
        leadingMinorWeight e j) • rectangularLeadingMinorProd R e := by
  have hX : (fun ij : Fin m × Fin n ↦ mvPolynomialX (Fin m) (Fin n) R ij.1 ij.2) =
      (X : Fin m × Fin n → MvPolynomial (Fin m × Fin n) R) := by
    funext ij
    simp [mvPolynomialX_apply]
  simpa only [MvPolynomial.algebraMap_eq, transpose_apply, hX, aeval_X_left_apply] using
    aeval_rectangularLeadingMinorProd_mul_mul
      (L := gᵀ) (U := h) (fun _ _ hij ↦ hg hij) hh (mvPolynomialX (Fin m) (Fin n) R) e

/-- For the action by `X ↦ gᵀ * X * h`, upper unitriangular matrices in both factors fix
all products of rectangular leading minors. -/
theorem aeval_rectangularLeadingMinorProd_transpose_mul_mul_of_isUpperUnitriangular
    {g : Matrix (Fin m) (Fin m) R} {h : Matrix (Fin n) (Fin n) R}
    (hg : g.IsUpperUnitriangular) (hh : h.IsUpperUnitriangular) (e : Fin (min m n) → ℕ) :
    aeval (fun ij : Fin m × Fin n ↦
      (gᵀ.map C * mvPolynomialX (Fin m) (Fin n) R * h.map C :
        Matrix (Fin m) (Fin n) (MvPolynomial (Fin m × Fin n) R)) ij.1 ij.2)
      (rectangularLeadingMinorProd R e) = rectangularLeadingMinorProd R e := by
  rw [aeval_rectangularLeadingMinorProd_transpose_mul_mul hg.isUpperTriangular hh.isUpperTriangular]
  simp [hg.apply_diag, hh.apply_diag]

end TauCeti
