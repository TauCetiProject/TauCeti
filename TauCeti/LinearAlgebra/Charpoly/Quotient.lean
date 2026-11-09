/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Characteristic polynomials along an invariant submodule

If an endomorphism `e` of a finite free module `V` maps a submodule `W` into itself, then its
characteristic polynomial is the product of those of the restriction `e|W` and of the induced map
on the quotient `V ⧸ W` (`LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`), provided `W`
and `V ⧸ W` are themselves finite free. In a basis of `V` extending one of `W`, the matrix of `e` is
block upper triangular with these two diagonal blocks.

This is the characteristic-polynomial version of Mathlib's `LinearMap.det_eq_det_mul_det`, and the
proof follows that one. A typical use splits off an eigenline: if `e` fixes a vector `u`, then `e`
restricted to the span of `u` is the identity, and the characteristic polynomial of `e` is `X - 1`
times that of the map induced on `V ⧸ span {u}`.
-/

public section

open Module Polynomial

namespace LinearMap

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Module.Free R V]
  [Module.Finite R V] (W : Submodule R V) [Module.Free R W] [Module.Finite R W]
  [Module.Free R (V ⧸ W)]

open Module.Basis in
/-- **The characteristic polynomial along an invariant submodule.** If `e` maps `W` into itself,
its characteristic polynomial is the product of those of the restriction of `e` to `W` and of the
map `e` induces on `V ⧸ W`. -/
theorem charpoly_eq_charpoly_restrict_mul_charpoly_mapQ (e : V →ₗ[R] V) (he : W ≤ W.comap e) :
    e.charpoly = (e.restrict he).charpoly * (W.mapQ W e he).charpoly := by
  classical
  let m := Module.Free.ChooseBasisIndex R W
  let bW : Basis m R W := Module.Free.chooseBasis R W
  let n := Module.Free.ChooseBasisIndex R (V ⧸ W)
  let bQ : Basis n R (V ⧸ W) := Module.Free.chooseBasis R (V ⧸ W)
  let b := sumQuot bW bQ
  let A : Matrix m m R := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n R := Matrix.of fun i l ↦ (b.repr (e (b (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n R := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  -- In the basis `b` extending `bW`, the matrix of `e` is block upper triangular with diagonal
  -- blocks `A` and `D`.
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.charpoly_toMatrix e b, this, ← LinearMap.charpoly_toMatrix _ bW,
      ← LinearMap.charpoly_toMatrix _ bQ, Matrix.charpoly_fromBlocks_zero₂₁]
  ext u w
  cases u with
  | inl i =>
    cases w with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases w with
    | inl k =>
      suffices W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr, Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l, W.mapQ_apply, Submodule.mkQ_apply]

end LinearMap
