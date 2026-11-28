/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.LinearAlgebra.Determinant.SMul
import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# The determinant of the scalar action on a tensor product

Let `E` and `k` be algebras over a commutative ring `F`, with `E` commutative and `k` free over
`F`. Let `E` act on `k ⊗_F E` through the right factor (`Algebra.TensorProduct.rightAlgebra`).
This action commutes with the left action of `k`, and the determinant over `E` of `a ∈ k` is the
norm, `det_E(a | k ⊗_F E) = Nm_{k/F}(a)` (`TauCeti.smulDet_tensorProduct`). Mathlib's swap
`Algebra.TensorProduct.commRight` identifies `k ⊗_F E` with `E ⊗_F k` `E`-linearly. On
`E ⊗_F k`, `a` acts as multiplication by `1 ⊗ a`, whose determinant is the norm of `1 ⊗ a`, and
that is `Nm_{k/F}(a)` (`TauCeti.Algebra.norm_baseChange_tmul`).
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {F : Type*} [CommRing F] (E : Type*) [CommRing E] [Algebra F E] (k : Type*) [Ring k]
  [Algebra F k] [Module.Free F k]

-- `E` acts on `k ⊗_F E` through the right factor, commuting with the action of `k`.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The determinant over `E` of the action of `k` on `k ⊗_F E` is the norm.** Here `E` acts
through the right factor (`Algebra.TensorProduct.rightAlgebra`). If `k` is not finite over `F`,
both sides are the junk value `1`. -/
theorem smulDet_tensorProduct (a : k) :
    smulDet E k (k ⊗[F] E) a = algebraMap F E (Algebra.norm F a) := by
  rw [smulDet_apply, ← Algebra.norm_baseChange_tmul (A := E), Algebra.norm_apply,
    ← LinearMap.det_conj _ (Algebra.TensorProduct.commRight F E k).symm.toLinearEquiv]
  congr 1
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul x c => simp [TensorProduct.smul_tmul']

end TauCeti
