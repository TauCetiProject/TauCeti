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

`Matrix.extendLast` extends a matrix indexed by configurations `∀ i : Fin m, α i.castSucc` to
one indexed by `∀ i : Fin (m + 1), α i`, for finite types `α i`, acting as the identity on the
last coordinate. It is the Kronecker product `1 ⊗ₖ X`, reindexed along `Fin.snocEquiv`. The
construction composes Mathlib's tensor-product inclusion, Kronecker algebra equivalence, and
matrix reindexing equivalence.
-/

public section

open scoped Kronecker

namespace Matrix

variable {R : Type*} [CommSemiring R] {m : ℕ} {α : Fin (m + 1) → Type*} [∀ i, Fintype (α i)]
  [∀ i, DecidableEq (α i)]

/-- A matrix on the first `m` coordinates as a matrix on all `m + 1` coordinates, acting as the
identity on the last one: the Kronecker product `1 ⊗ₖ X`, reindexed along `Fin.snocEquiv`. -/
def extendLast : Matrix (∀ i : Fin m, α i.castSucc) (∀ i : Fin m, α i.castSucc) R →ₐ[R]
    Matrix (∀ i, α i) (∀ i, α i) R :=
  (reindexAlgEquiv R R (Fin.snocEquiv α)).toAlgHom.comp <|
    (kroneckerAlgEquiv (α (Fin.last m)) (∀ i : Fin m, α i.castSucc) R).toAlgHom.comp
      Algebra.TensorProduct.includeRight

/-- `extendLast X` is the Kronecker product of the identity on the last coordinate with `X`. -/
theorem extendLast_eq (X : Matrix (∀ i : Fin m, α i.castSucc) (∀ i : Fin m, α i.castSucc) R) :
    extendLast X = reindex (Fin.snocEquiv α) (Fin.snocEquiv α)
      ((1 : Matrix (α (Fin.last m)) (α (Fin.last m)) R) ⊗ₖ X) :=
  (rfl)

/-- The entry of `extendLast X` at `s` and `t` is the entry of `X` at their first `m` coordinates
when their last coordinates agree, and `0` otherwise. -/
@[simp]
theorem extendLast_apply
    (X : Matrix (∀ i : Fin m, α i.castSucc) (∀ i : Fin m, α i.castSucc) R) (s t : ∀ i, α i) :
    extendLast X s t = if s (Fin.last m) = t (Fin.last m) then X (Fin.init s) (Fin.init t)
      else 0 := by
  simp [extendLast_eq, Matrix.one_apply]

end Matrix
