/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Localization.Submodule

/-!
# The local rings of the fibre ring

For a prime `p` of `R` and a prime `Q` of the fibre ring `κ(p) ⊗[R] B` lying over the prime `q`
of `B`, Mathlib's `Ideal.Fiber.algEquivAux₂` identifies the local ring `(κ(p) ⊗[R] B)_Q` with
`B_q ⧸ p B_q`. This file records that this identification is compatible with the maps from `B`.
It also records that the fibre ring of a Noetherian algebra is Noetherian.

## Main results

* `Ideal.Fiber.algEquivAux₂_algebraMap_one_tmul`: `Ideal.Fiber.algEquivAux₂` sends `1 ⊗ b` to the
  class of `b`.
* `Ideal.Fiber.isNoetherianRing`: if `B` is Noetherian, so is the fibre ring `κ(p) ⊗[R] B`.
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
      algebraMap B (Localization.AtPrime (Q.comap includeRight) ⧸ _) b := by
  -- `algEquivAux₂` is the restriction of scalars to `R` of a composite of `B`-algebra
  -- isomorphisms; unfold it and use that each factor commutes with the maps from `B`.
  let : Algebra B (p.Fiber B) := rightAlgebra
  unfold algEquivAux₂
  simp only [AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
  rw [← AlgEquiv.restrictScalars_apply B, ← right_algebraMap_apply,
    ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, AlgEquiv.commutes]

/-- The fibre ring `κ(p) ⊗[R] B` of a Noetherian `R`-algebra `B` is Noetherian, being the quotient
`B_p ⧸ p B_p` of a localization of `B` (`Ideal.Fiber.algEquivQuotient`). -/
instance isNoetherianRing [IsNoetherianRing B] : IsNoetherianRing (p.Fiber B) :=
  let : Algebra B (p.Fiber B) := rightAlgebra
  isNoetherianRing_of_ringEquiv _ (algEquivQuotient p).symm.toRingEquiv

end Ideal.Fiber
