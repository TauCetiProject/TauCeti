/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Traces and determinant pencils under rectangular congruence

For a rectangular matrix `M`, congruence `A ↦ M * A * Mᵀ` can be moved across a trace pairing
or a determinant pencil `det (1 + c • (B * _))` by congruating the test matrix `B` with the
transpose instead. These identities transport Wishart trace transforms along congruence.

## Main results

* `Matrix.trace_mul_congruence` — `trace (B * (M * A * Mᵀ)) = trace ((Mᵀ * B * M) * A)`.
* `Matrix.det_one_add_smul_transpose_mul_mul`,
  `Matrix.det_one_sub_smul_transpose_mul_mul` — the corresponding determinant pencil identities,
  instances of the Weinstein--Aronszajn identity `Matrix.det_one_add_mul_comm`.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapters 2–3.
-/

public section

namespace Matrix

/-- Moving a rectangular congruence across a trace pairing transposes the congruence matrix.
No symmetry hypotheses on `A` or `B` are needed. -/
theorem trace_mul_congruence {m n R : Type*} [Fintype m] [Fintype n]
    [NonUnitalCommSemiring R]
    (B : Matrix m m R) (M : Matrix m n R) (A : Matrix n n R) :
    (B * (M * A * Mᵀ)).trace = ((Mᵀ * B * M) * A).trace := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B * M * A) Mᵀ

/-- The Weinstein--Aronszajn identity in the form used by a rectangular congruence: the
determinant pencil can be computed either before or after applying the congruence. -/
theorem det_one_add_smul_transpose_mul_mul {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R] (c : R) (B : Matrix m m R)
    (M : Matrix m n R) (A : Matrix n n R) :
    det (1 + c • ((Mᵀ * B * M) * A)) = det (1 + c • (B * (M * A * Mᵀ))) := by
  calc
    det (1 + c • ((Mᵀ * B * M) * A)) = det (1 + Mᵀ * (c • (B * M * A))) := by
      simp only [Matrix.mul_assoc, Matrix.mul_smul]
    _ = det (1 + (c • (B * M * A)) * Mᵀ) :=
      Matrix.det_one_add_mul_comm Mᵀ (c • (B * M * A))
    _ = det (1 + c • (B * (M * A * Mᵀ))) := by
      simp only [Matrix.smul_mul, Matrix.mul_assoc]

/-- The subtractive form of `Matrix.det_one_add_smul_transpose_mul_mul`. This is the form of the
determinant pencil occurring in Wishart moment-generating functions. -/
theorem det_one_sub_smul_transpose_mul_mul {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R] (c : R) (B : Matrix m m R)
    (M : Matrix m n R) (A : Matrix n n R) :
    det (1 - c • ((Mᵀ * B * M) * A)) = det (1 - c • (B * (M * A * Mᵀ))) := by
  simpa only [sub_eq_add_neg, neg_smul] using
    det_one_add_smul_transpose_mul_mul (-c) B M A

end Matrix
