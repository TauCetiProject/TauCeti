/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.LinearAlgebra.Matrix.Realify

/-!
# Complex matrix maps in real Euclidean coordinates

Splitting real and imaginary coordinates intertwines a complex matrix map with the
Euclidean linear map of its realification. This identity transports complex linear
images to real coordinates, including rectangular maps.
-/

public section

open scoped Matrix

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- Splitting a complex matrix-vector product into real and imaginary blocks gives the
Euclidean action of the realified matrix. -/
theorem complexToRealEuclidean_mulVec (L : Matrix κ ι ℂ) (z : ι → ℂ) :
    complexToRealEuclidean κ (L *ᵥ z) =
      L.realify.toEuclideanLin (complexToRealEuclidean ι z) := by
  ext k
  cases k <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Complex.mul_re, Complex.mul_im,
      Finset.sum_add_distrib, sub_eq_add_neg, add_comm]

end TauCeti
