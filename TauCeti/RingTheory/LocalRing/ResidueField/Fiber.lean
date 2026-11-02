/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# The local rings of the fibre ring

For a prime `p` of `R` and a prime `Q` of the fibre ring `κ(p) ⊗[R] B` lying over the prime `q`
of `B`, Mathlib's `Ideal.Fiber.algEquivAux₂` identifies the local ring `(κ(p) ⊗[R] B)_Q` with
`B_q ⧸ p B_q`. This file records that this identification is compatible with the maps from `B`.

## Main results

* `Ideal.Fiber.algEquivAux₂_algebraMap_one_tmul`: `Ideal.Fiber.algEquivAux₂` sends `1 ⊗ b` to the
  class of `b`.
-/

public section

universe u v

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

namespace Ideal.Fiber

open Algebra.TensorProduct

variable (p : Ideal R) [p.IsPrime]

/-- The isomorphism `(κ(p) ⊗[R] B)_Q ≃ B_q ⧸ p B_q` of `Ideal.Fiber.algEquivAux₂`, where `q` is
the prime of `B` under `Q`, is compatible with the maps from `B`: it sends `1 ⊗ b` to the class
of `b`. -/
@[simp]
theorem algEquivAux₂_algebraMap_one_tmul (Q : Ideal (p.Fiber B)) [Q.IsPrime] (b : B) :
    algEquivAux₂ p Q (algebraMap _ (Localization.AtPrime Q) ((1 : p.ResidueField) ⊗ₜ[R] b)) =
      Ideal.Quotient.mk _ (algebraMap B (Localization.AtPrime (Q.comap includeRight)) b) := by
  -- `algEquivAux₂` is the restriction of scalars to `R` of a composite of `B`-algebra
  -- isomorphisms; unfold it and use that each factor commutes with the maps from `B`.
  let : Algebra B (p.Fiber B) := rightAlgebra
  unfold algEquivAux₂
  simp only [AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
  rw [← AlgEquiv.restrictScalars_apply B, ← right_algebraMap_apply,
    ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, AlgEquiv.commutes,
    Ideal.Quotient.mk_algebraMap]

end Ideal.Fiber
