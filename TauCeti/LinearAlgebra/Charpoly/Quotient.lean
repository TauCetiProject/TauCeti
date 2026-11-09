/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The characteristic polynomial on an invariant submodule and its quotient

An endomorphism `f` of a module `V` that preserves a submodule `W` restricts to an endomorphism
`f.restrict _` of `W` and induces an endomorphism `Submodule.mapQ W W f _` of `V ⧸ W`. When `W` and
`V ⧸ W` are free of finite rank, the characteristic polynomial of `f` is the product of those of
the two induced endomorphisms. In a basis of `V` made of a basis of `W` and a lift of a basis of
`V ⧸ W` (`Module.Basis.sumQuot`), the matrix of `f` is block upper triangular with these two
endomorphisms on the diagonal. This is the characteristic-polynomial analogue of Mathlib's
`LinearMap.det_eq_det_mul_det`, and its proof is the same.

No complement of `W` is chosen, so `W` need not be a direct summand stable under `f`: over a field
this computes the characteristic polynomial of `f` on `W` from those of `f` on `V` and on `V ⧸ W`
in every characteristic.

## Main results

* `LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`: the characteristic polynomial of
  `f` is the product of those of its restriction to `W` and of the endomorphism it induces on
  `V ⧸ W`.
-/

public section

open Module Module.Basis

namespace LinearMap

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Module.Free R V]
  [Module.Finite R V] (W : Submodule R V) [Module.Free R W] [Module.Finite R W]
  [Module.Free R (V ⧸ W)] [Module.Finite R (V ⧸ W)]

/-- **The characteristic polynomial is multiplicative on an invariant submodule and its
quotient.** If `f` preserves `W`, then the characteristic polynomial of `f` is the product of the
characteristic polynomials of the restriction of `f` to `W` and of the endomorphism of `V ⧸ W`
induced by `f`. -/
theorem charpoly_eq_charpoly_restrict_mul_charpoly_mapQ (f : V →ₗ[R] V) (hf : W ≤ W.comap f) :
    f.charpoly = (f.restrict hf).charpoly * (W.mapQ W f hf).charpoly := by
  classical
  let bW := Module.Free.chooseBasis R W
  let bQ := Module.Free.chooseBasis R (V ⧸ W)
  let b := sumQuot bW bQ
  let B := Matrix.of fun i l ↦ (b.repr (f (b (Sum.inr l)))) (Sum.inl i)
  suffices toMatrix b b f =
      Matrix.fromBlocks (toMatrix bW bW (f.restrict hf)) B 0 (toMatrix bQ bQ (W.mapQ W f hf)) by
    rw [← charpoly_toMatrix f b, this, Matrix.charpoly_fromBlocks_zero₂₁, charpoly_toMatrix,
      charpoly_toMatrix]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (f (bW k)) = 0 by simp [toMatrix_apply, b, this]
      rw [← mem_ker, Submodule.ker_mkQ]
      exact hf (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [toMatrix_apply, sumQuot_repr_inr, Matrix.fromBlocks_apply₂₂, b]
      rw [← sumQuot_inr bW bQ l, W.mapQ_apply, Submodule.mkQ_apply]

end LinearMap
