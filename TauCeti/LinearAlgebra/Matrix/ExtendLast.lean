/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Extending matrices on configurations by one coordinate

`Matrix.extendLast` extends a matrix indexed by `Fin m → ι` to one indexed by
`Fin (m + 1) → ι`, for a finite type `ι`, acting as the identity on the last coordinate. It is
the Kronecker product `1 ⊗ₖ X`, reindexed along `Fin.snocEquiv`. The construction composes
Mathlib's tensor-product inclusion, Kronecker algebra equivalence, and matrix reindexing
equivalence.
-/

public section

open scoped Kronecker

namespace Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- A matrix on `m` coordinates with values in `ι` as a matrix on `m + 1` coordinates, acting as the
identity on the last one: the Kronecker product `1 ⊗ₖ X`, reindexed along `Fin.snocEquiv`.
Its entry at `s` and `t` is the entry of the original matrix at their first `m` coordinates
when their last coordinates agree, and `0` otherwise. -/
def extendLast : Matrix (Fin m → ι) (Fin m → ι) R →ₐ[R]
    Matrix (Fin (m + 1) → ι) (Fin (m + 1) → ι) R :=
  (reindexAlgEquiv R R (Fin.snocEquiv fun _ ↦ ι)).toAlgHom.comp <|
    (kroneckerAlgEquiv ι (Fin m → ι) R).toAlgHom.comp
      Algebra.TensorProduct.includeRight

/-- `extendLast X` is the Kronecker product of the identity on the last coordinate with `X`. -/
theorem extendLast_eq (X : Matrix (Fin m → ι) (Fin m → ι) R) :
    extendLast X = reindex (Fin.snocEquiv fun _ ↦ ι) (Fin.snocEquiv fun _ ↦ ι)
      ((1 : Matrix ι ι R) ⊗ₖ X) := by
  simp [extendLast]

@[simp]
theorem extendLast_apply (X : Matrix (Fin m → ι) (Fin m → ι) R)
    (s t : Fin (m + 1) → ι) :
    extendLast X s t = if s (Fin.last m) = t (Fin.last m) then X (Fin.init s) (Fin.init t)
      else 0 := by
  simp [extendLast_eq, one_apply]

end Matrix
