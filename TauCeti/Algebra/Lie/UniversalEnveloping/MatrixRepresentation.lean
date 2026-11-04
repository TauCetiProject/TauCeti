/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# The defining representation of a matrix Lie subalgebra

A Lie subalgebra of square matrices acts faithfully on coordinate vectors. This file extends that
action to the universal enveloping algebra and records its values on Lie generators. It also
shows that a Lie generator acts nilpotently exactly when its underlying matrix is nilpotent.

## Main definitions and results

* `LieSubalgebra.matrixRepresentation`: the defining representation extended to the
  universal enveloping algebra.
* `LieSubalgebra.matrixRepresentation_ι_injective`: faithfulness on the Lie algebra.
* `LieSubalgebra.isNilpotent_matrixRepresentation_ι_iff`: a Lie generator acts nilpotently
  exactly when its underlying matrix is nilpotent.
-/

public section

namespace LieSubalgebra

open Matrix

noncomputable section

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The defining action of a matrix Lie subalgebra, extended to its universal enveloping algebra. -/
def matrixRepresentation (K : LieSubalgebra R (Matrix n n R)) :
    UniversalEnvelopingAlgebra R K →ₐ[R] Module.End R (n → R) :=
  UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R K (n → R))

/-- The defining representation is the universal-enveloping extension of the matrix Lie-module
action. -/
theorem matrixRepresentation_def (K : LieSubalgebra R (Matrix n n R)) :
    matrixRepresentation K = UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R K (n → R)) :=
  (rfl)

/-- A Lie generator acts through its underlying matrix. -/
theorem matrixRepresentation_ι {K : LieSubalgebra R (Matrix n n R)} (x : K) :
    matrixRepresentation K (UniversalEnvelopingAlgebra.ι R x) =
      toLinAlgEquiv' (x : Matrix n n R) := by
  ext v
  simp [matrixRepresentation_def]

-- `simp` rewrites `ι` with Mathlib's `UniversalEnvelopingAlgebra.ι_apply`, so the left-hand sides
-- of `matrixRepresentation_ι` and of its pointwise and nilpotency forms are not in simp-normal
-- form. Following Mathlib's `UniversalEnvelopingAlgebra.lift_ι_apply'`, this restatement is the
-- `simp` lemma instead.
/-- The `simp`-normal form of `LieSubalgebra.matrixRepresentation_ι`. -/
@[simp]
theorem matrixRepresentation_mkAlgHom_ι {K : LieSubalgebra R (Matrix n n R)} (x : K) :
    matrixRepresentation K (UniversalEnvelopingAlgebra.mkAlgHom R K (TensorAlgebra.ι R x)) =
      toLinAlgEquiv' (x : Matrix n n R) :=
  matrixRepresentation_ι x

/-- Pointwise, a Lie generator acts by matrix-vector multiplication. -/
theorem matrixRepresentation_ι_apply {K : LieSubalgebra R (Matrix n n R)} (x : K) (v : n → R) :
    matrixRepresentation K (UniversalEnvelopingAlgebra.ι R x) v = (x : Matrix n n R) *ᵥ v := by
  rw [matrixRepresentation_ι, toLinAlgEquiv'_apply]

/-- The defining representation of a matrix Lie subalgebra is faithful on the Lie algebra. -/
theorem matrixRepresentation_ι_injective (K : LieSubalgebra R (Matrix n n R)) :
    Function.Injective fun x : K => matrixRepresentation K (UniversalEnvelopingAlgebra.ι R x) := by
  intro x y hxy
  simpa only [matrixRepresentation_ι, EmbeddingLike.apply_eq_iff_eq, SetLike.coe_eq_coe] using hxy

/-- A Lie generator acts nilpotently in the defining representation if and only if its underlying
matrix is nilpotent. -/
theorem isNilpotent_matrixRepresentation_ι_iff {K : LieSubalgebra R (Matrix n n R)} (x : K) :
    IsNilpotent (matrixRepresentation K (UniversalEnvelopingAlgebra.ι R x)) ↔
      IsNilpotent (x : Matrix n n R) := by
  rw [matrixRepresentation_ι, IsNilpotent.map_iff toLinAlgEquiv'.injective]

end

end LieSubalgebra
