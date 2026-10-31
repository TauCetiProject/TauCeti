/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul

/-!
# Valid one-dimensional convolution layers

`convolution h` is a single-channel convolution with filter length `k`, stride `s`,
input length `n`, and output length `m`, where `h : n = s * (m - 1) + k`.
It uses zero-based indices, no padding, and no filter reversal. `convolutionMatrix h w`
is its sparse matrix: row `i` places `w j` in column `s * i + j`.
`convolutionMatrix_mulVec` identifies matrix evaluation with the filter-sum definition.
`affineConvolution` adds one scalar bias shared by every output position.

These are realization maps, so the `realizedFunctions`, `parametrization`, `fiber`, and
`parameterSetoid` APIs from `TauCeti.Geometry.Neuromanifold.Basic` apply directly.
The bias-free parameters are exactly `Fin k → K`; the affine parameters are
`(Fin k → K) × K`.

The convention follows Vahid Shahverdi, *Algebraic Complexity and Neurovariety of
Linear Convolutional Networks*, [arXiv:2401.16613v1](https://arxiv.org/abs/2401.16613v1),
§2.1, equations (2.1)–(2.2). The usual layers have positive filter length, stride,
and output length. The formulas also allow empty index types and zero stride;
no positivity assumption is needed for index validity or the matrix comparison.
-/

public section

namespace TauCeti.Neuromanifold

variable {n k s m : ℕ}

/-- The input position read by filter coordinate `j` at output position `i`. -/
def convolutionIndex (h : n = s * (m - 1) + k) (i : Fin m) (j : Fin k) : Fin n :=
  ⟨s * i.val + j.val, by
    have hi : i.val ≤ m - 1 := by omega
    have hs := Nat.mul_le_mul_left s hi
    have hj := j.isLt
    omega⟩

/-- The convolution index is the unreversed, unpadded position `s * i + j`. -/
@[simp] theorem convolutionIndex_val (h : n = s * (m - 1) + k)
    (i : Fin m) (j : Fin k) : (convolutionIndex h i j).val = s * i.val + j.val := (rfl)

/-- A convolution window reads distinct input positions for distinct filter coordinates. -/
theorem convolutionIndex_injective (h : n = s * (m - 1) + k) (i : Fin m) :
    Function.Injective (convolutionIndex h i) := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  simp only [convolutionIndex_val] at hv
  omega

variable {K : Type*}

section Matrix

variable [AddCommMonoid K]

/-- The structured matrix of a valid convolution, with one shifted filter in each row. -/
def convolutionMatrix (h : n = s * (m - 1) + k) (w : Fin k → K) :
    Matrix (Fin m) (Fin n) K :=
  fun i a => ∑ j : Fin k, if a = convolutionIndex h i j then w j else 0

/-- The entry formula for the structured convolution matrix. -/
theorem convolutionMatrix_apply (h : n = s * (m - 1) + k) (w : Fin k → K)
    (i : Fin m) (a : Fin n) :
    convolutionMatrix h w i a =
      ∑ j : Fin k, if a = convolutionIndex h i j then w j else 0 := (rfl)

/-- Inside a convolution window, the matrix entry is the corresponding filter weight. -/
@[simp] theorem convolutionMatrix_apply_index (h : n = s * (m - 1) + k)
    (w : Fin k → K) (i : Fin m) (j : Fin k) :
    convolutionMatrix h w i (convolutionIndex h i j) = w j := by
  simp [convolutionMatrix, (convolutionIndex_injective h i).eq_iff]

/-- Outside its window, a convolution matrix row is zero. -/
theorem convolutionMatrix_apply_eq_zero (h : n = s * (m - 1) + k)
    (w : Fin k → K) (i : Fin m) (a : Fin n)
    (ha : ∀ j, a ≠ convolutionIndex h i j) : convolutionMatrix h w i a = 0 := by
  simp [convolutionMatrix, ha]

end Matrix

variable [NonUnitalNonAssocSemiring K]

/-- A bias-free valid convolution as a realization map on filter parameters. -/
def convolution (h : n = s * (m - 1) + k) :
    (Fin k → K) → (Fin n → K) → Fin m → K :=
  fun w x i => ∑ j : Fin k, w j * x (convolutionIndex h i j)

/-- Coordinate evaluation of valid convolution is the filter sum. -/
@[simp] theorem convolution_apply (h : n = s * (m - 1) + k)
    (w : Fin k → K) (x : Fin n → K) (i : Fin m) :
    convolution h w x i = ∑ j : Fin k, w j * x (convolutionIndex h i j) := (rfl)

/-- The structured matrix and filter-sum presentations define the same convolution. -/
theorem convolutionMatrix_mulVec (h : n = s * (m - 1) + k)
    (w : Fin k → K) (x : Fin n → K) :
    (convolutionMatrix h w).mulVec x = convolution h w x := by
  funext i
  simp only [Matrix.mulVec_apply_eq_sum, convolutionMatrix, Finset.sum_mul,
    convolution_apply]
  rw [Finset.sum_comm]
  simp [ite_mul]

/-- A zero filter realizes the zero function. -/
@[simp] theorem convolution_zero (h : n = s * (m - 1) + k) :
    convolution (K := K) h 0 = 0 := by
  funext x i
  simp

/-- Convolution takes the zero input to zero. -/
@[simp] theorem convolution_apply_zero (h : n = s * (m - 1) + k) (w : Fin k → K) :
    convolution h w 0 = 0 := by
  funext i
  simp

/-- Valid convolution with a scalar bias shared across all output positions. -/
def affineConvolution (h : n = s * (m - 1) + k) :
    ((Fin k → K) × K) → (Fin n → K) → Fin m → K :=
  fun p x i => convolution h p.1 x i + p.2

/-- Each affine convolution output is a filter sum plus the same scalar bias. -/
@[simp] theorem affineConvolution_apply (h : n = s * (m - 1) + k)
    (p : (Fin k → K) × K) (x : Fin n → K) (i : Fin m) :
    affineConvolution h p x i =
      (∑ j : Fin k, p.1 j * x (convolutionIndex h i j)) + p.2 := (rfl)

/-- Setting the shared bias to zero recovers the bias-free realization map. -/
@[simp] theorem affineConvolution_zero_bias (h : n = s * (m - 1) + k)
    (w : Fin k → K) : affineConvolution h (w, 0) = convolution h w := by
  funext x i
  simp

/-- Matrix evaluation of the affine convolution adds a constant output vector. -/
theorem affineConvolution_eq_mulVec_add (h : n = s * (m - 1) + k)
    (p : (Fin k → K) × K) (x : Fin n → K) :
    affineConvolution h p x = (convolutionMatrix h p.1).mulVec x + fun _ => p.2 := by
  rw [convolutionMatrix_mulVec]
  rfl

/-- At zero input, every affine convolution output is its shared bias. -/
@[simp] theorem affineConvolution_apply_zero (h : n = s * (m - 1) + k)
    (p : (Fin k → K) × K) : affineConvolution h p 0 = fun _ => p.2 := by
  funext i
  simp

end TauCeti.Neuromanifold
