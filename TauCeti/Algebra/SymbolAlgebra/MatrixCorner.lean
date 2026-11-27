/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.SymbolAlgebra.CentralSimple
public import TauCeti.LinearAlgebra.Matrix.WeightedShift
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Algebra.Algebra.Hom
import TauCeti.Algebra.BrauerGroup.Basic

/-!
# Matrix corners of symbol algebras

If `a = c ^ s` and `ζ` has order `d * s`, the degree `d * s` symbol algebra is the
algebra of `s` by `s` matrices over the degree `d` symbol algebra with parameters
`ζ ^ s`, `c`, and `b`. The matrices of the generators are a diagonal matrix and a
forward shift whose wrap entry is the smaller algebra's second generator.

## References

* C. A. Weibel, *The K-book*, III.6.9 and Remark 6.10.4.
-/

public section

namespace TauCeti.SymbolAlgebra

/-- The diagonal generator in the matrix corner presentation. -/
def matrixCornerX {F A : Type*} [Inv F] [Pow F ℕ] [Zero A] [SMul F A]
    (s : ℕ) (ζ : F) (u : A) : Matrix (Fin s) (Fin s) A :=
  Matrix.diagonal fun i => ζ⁻¹ ^ (i : ℕ) • u

/-- The first generator matrix is diagonal with the prescribed scaled entries. -/
theorem matrixCornerX_eq_diagonal {F A : Type*} [Inv F] [Pow F ℕ] [Zero A] [SMul F A]
    (s : ℕ) (ζ : F) (u : A) :
    matrixCornerX s ζ u = Matrix.diagonal (fun i : Fin s => ζ⁻¹ ^ (i : ℕ) • u) := (rfl)

/-- The entries of the diagonal generator. -/
@[simp]
theorem matrixCornerX_apply {F A : Type*} [Inv F] [Pow F ℕ] [Zero A] [SMul F A]
    (s : ℕ) (ζ : F) (u : A) (i j : Fin s) :
    matrixCornerX s ζ u i j = if i = j then ζ⁻¹ ^ (i : ℕ) • u else 0 := by
  rw [matrixCornerX_eq_diagonal, Matrix.diagonal_apply]

section Field

variable {F : Type*} [Field F] (d s : ℕ) {ζ c b : F}

private theorem matrixCornerX_pow (hζ : ζ ^ (d * s) = 1) :
    matrixCornerX s ζ (x : SymbolAlgebra d (ζ ^ s) c b) ^ (d * s) =
      algebraMap F _ (c ^ s) := by
  rw [matrixCornerX_eq_diagonal, Matrix.diagonal_pow]
  have hx : (x : SymbolAlgebra d (ζ ^ s) c b) ^ (d * s) = algebraMap F _ (c ^ s) := by
    rw [pow_mul, x_pow, map_pow]
  have hz (i : Fin s) : (ζ⁻¹ ^ (i : ℕ)) ^ (d * s) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, inv_pow, hζ, inv_one, one_pow]
  have hd : (fun i : Fin s => ζ⁻¹ ^ (i : ℕ) •
      (x : SymbolAlgebra d (ζ ^ s) c b)) ^ (d * s) =
      fun _ => algebraMap F _ (c ^ s) := by
    funext i
    simp only [Pi.pow_apply, smul_pow, hx, hz, one_smul]
  rw [hd]
  rfl

private theorem matrixCornerY_pow_mul :
    Matrix.weightedShift s (y : SymbolAlgebra d (ζ ^ s) c b) ^ (d * s) =
      algebraMap F _ b := by
  rw [Nat.mul_comm d s, pow_mul, Matrix.weightedShift_pow_card, ← map_pow, y_pow]
  rfl

private theorem matrixCornerY_mul_matrixCornerX (hζ : ζ ≠ 0) :
    Matrix.weightedShift s (y : SymbolAlgebra d (ζ ^ s) c b) * matrixCornerX s ζ x =
      ζ • (matrixCornerX s ζ x * Matrix.weightedShift s y) := by
  ext i j
  simp only [matrixCornerX_eq_diagonal, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_mul,
    Matrix.weightedShift_apply]
  split_ifs with hij hwrap
  · simp only [hij, one_mul, mul_one, smul_smul, pow_succ]
    congr 1
    field_simp
  · have hi : (i : ℕ) = 0 := by simpa using hwrap.1
    have hj : (j : ℕ) + 1 = s := hwrap.2
    simp only [hi, pow_zero, one_smul, mul_smul_comm, y_mul_x, smul_smul]
    have hz : ζ⁻¹ ^ (j : ℕ) * ζ ^ s = ζ := by
      calc
        _ = ζ⁻¹ ^ (j : ℕ) * ζ ^ ((j : ℕ) + 1) := by rw [hj]
        _ = ζ := by rw [pow_succ, inv_pow]; field_simp
    rw [hz]
  · simp

/-- The diagonal-and-shift representation associated to a power `a = c ^ s`.
Its defining relations only require `ζ ^ (d * s) = 1` and `ζ ≠ 0`. -/
noncomputable def toMatrixOfPow (hζ : ζ ^ (d * s) = 1) (hζ₀ : ζ ≠ 0) :
    SymbolAlgebra (d * s) ζ (c ^ s) b →ₐ[F]
      Matrix (Fin s) (Fin s) (SymbolAlgebra d (ζ ^ s) c b) :=
  lift (matrixCornerX s ζ x) (Matrix.weightedShift s y)
    (matrixCornerX_pow d s hζ) (matrixCornerY_pow_mul d s)
    (matrixCornerY_mul_matrixCornerX d s hζ₀)

/-- The representation sends the first generator to the prescribed diagonal matrix. -/
@[simp]
theorem toMatrixOfPow_x (hζ : ζ ^ (d * s) = 1) (hζ₀ : ζ ≠ 0) :
    toMatrixOfPow d s (c := c) (b := b) hζ hζ₀ x = matrixCornerX s ζ x :=
  lift_x ..

/-- The representation sends the second generator to the forward shift with wrap `y`. -/
@[simp]
theorem toMatrixOfPow_y (hζ : ζ ^ (d * s) = 1) (hζ₀ : ζ ≠ 0) :
    toMatrixOfPow d s (c := c) (b := b) hζ hζ₀ y = Matrix.weightedShift s y :=
  lift_y ..

variable [NeZero d] [NeZero s]

/-- The diagonal-and-shift representation is bijective for positive `d` and `s` when `ζ`
is a primitive `(d * s)`-th root of unity and `c` and `b` are nonzero. -/
theorem bijective_toMatrixOfPow (hζ : IsPrimitiveRoot ζ (d * s)) (hc : c ≠ 0)
    (hb : b ≠ 0) :
    Function.Bijective (toMatrixOfPow d s (c := c) (b := b) hζ.pow_eq_one
      (hζ.ne_zero (NeZero.ne (d * s)))) := by
  have hζ' : IsPrimitiveRoot (ζ ^ s) d :=
    IsPrimitiveRoot.pow (Nat.pos_of_ne_zero (NeZero.ne (d * s))) hζ (Nat.mul_comm d s)
  have := isSimpleRing hζ (pow_ne_zero s hc) hb
  have := isSimpleRing hζ' hc hb
  have := finite (a := c ^ s) (b := b) hζ.pow_eq_one
  have := finite (a := c) (b := b) hζ'.pow_eq_one
  apply AlgHom.bijective_of_finrank_eq
  rw [finrank_eq hζ.pow_eq_one, Module.finrank_matrix, finrank_eq hζ'.pow_eq_one]
  simp only [Fintype.card_fin]
  ring

/-- A degree `d * s` symbol algebra with first parameter `c ^ s` is an `s` by `s`
matrix algebra over the degree `d` symbol algebra with root `ζ ^ s`. This includes
both the split case `d = 1` and the unchanged case `s = 1`. -/
noncomputable def algEquivMatrixOfPow (hζ : IsPrimitiveRoot ζ (d * s)) (hc : c ≠ 0)
    (hb : b ≠ 0) :
    SymbolAlgebra (d * s) ζ (c ^ s) b ≃ₐ[F]
      Matrix (Fin s) (Fin s) (SymbolAlgebra d (ζ ^ s) c b) :=
  AlgEquiv.ofBijective _ (bijective_toMatrixOfPow d s hζ hc hb)

/-- The first generator has diagonal entries `ζ⁻¹ ^ i • x` in the smaller algebra. -/
@[simp]
theorem algEquivMatrixOfPow_x (hζ : IsPrimitiveRoot ζ (d * s)) (hc : c ≠ 0)
    (hb : b ≠ 0) :
    algEquivMatrixOfPow d s hζ hc hb x = matrixCornerX s ζ x :=
  toMatrixOfPow_x ..

/-- The second generator is the forward shift whose wrap entry is the smaller `y`. -/
@[simp]
theorem algEquivMatrixOfPow_y (hζ : IsPrimitiveRoot ζ (d * s)) (hc : c ≠ 0)
    (hb : b ≠ 0) :
    algEquivMatrixOfPow d s hζ hc hb y = Matrix.weightedShift s y :=
  toMatrixOfPow_y ..

/-- Reducing the degree by a power in the first parameter preserves the Brauer class. -/
theorem brauerClass_eq_of_pow (hζ : IsPrimitiveRoot ζ (d * s)) (hc : c ≠ 0)
    (hb : b ≠ 0) :
    brauerClass hζ (pow_ne_zero s hc) hb =
      brauerClass (hζ.pow (NeZero.pos (d * s)) (Nat.mul_comm d s)) hc hb := by
  have hζ' : IsPrimitiveRoot (ζ ^ s) d := hζ.pow (NeZero.pos (d * s)) (Nat.mul_comm d s)
  have := isCentral hζ (pow_ne_zero s hc) hb
  have := isSimpleRing hζ (pow_ne_zero s hc) hb
  have := finite (a := c ^ s) (b := b) hζ.pow_eq_one
  have := isCentral hζ' hc hb
  have := isSimpleRing hζ' hc hb
  have := finite (a := c) (b := b) hζ'.pow_eq_one
  let A := CSA.of F (SymbolAlgebra (d * s) ζ (c ^ s) b)
  let B := CSA.of F (SymbolAlgebra d (ζ ^ s) c b)
  rw [brauerClass_eq_mk, brauerClass_eq_mk]
  exact (BrauerGroup.mk_eq_mk_of_algEquiv (A := A) (B := CSA.matrix B s)
    (algEquivMatrixOfPow d s hζ hc hb)).trans (BrauerGroup.mk_matrix B s)

end Field

end TauCeti.SymbolAlgebra
