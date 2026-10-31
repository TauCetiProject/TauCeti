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
`B_q ⧸ p B_q`. This file records that this identification is compatible with the maps from `B`,
and packages it as a ring isomorphism onto the quotient of `B_q` by the extension of `p`.

## Main results

* `Ideal.Fiber.algEquivAux₂_algebraMap_one_tmul`: `Ideal.Fiber.algEquivAux₂` sends `1 ⊗ b` to the
  class of `b`;
* `Ideal.Fiber.localizationAtPrimeEquivQuotientMap`: the ring isomorphism
  `(κ(p) ⊗[R] B)_Q ≃ B_q ⧸ p B_q`, with `p B_q` the extension of `p` along `R → B_q`;
* `Ideal.Fiber.localizationAtPrimeEquivQuotientMap_algebraMap_one_tmul`: it sends `1 ⊗ b` to the
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

/-- The local ring `(κ(p) ⊗[R] B)_Q` of the fibre ring at a prime `Q`, lying over the prime `q`
of `B`, is isomorphic to `B_q ⧸ p B_q`, where `p B_q` is the extension of `p` along `R → B_q`.
This is `Ideal.Fiber.algEquivAux₂` as a ring isomorphism, with the ideal written as an extension
from `R`. -/
noncomputable def localizationAtPrimeEquivQuotientMap (Q : Ideal (p.Fiber B)) [Q.IsPrime] :
    Localization.AtPrime Q ≃+* Localization.AtPrime (Q.comap includeRight) ⧸
      p.map (algebraMap R (Localization.AtPrime (Q.comap includeRight))) :=
  (algEquivAux₂ p Q).toRingEquiv.trans
    (Ideal.quotEquivOfEq (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]))

/-- The isomorphism `(κ(p) ⊗[R] B)_Q ≃ B_q ⧸ p B_q` is compatible with the maps from `B`: it
sends `1 ⊗ b` to the class of `b`. -/
@[simp]
theorem localizationAtPrimeEquivQuotientMap_algebraMap_one_tmul (Q : Ideal (p.Fiber B))
    [Q.IsPrime] (b : B) :
    localizationAtPrimeEquivQuotientMap p Q
        (algebraMap _ (Localization.AtPrime Q) ((1 : p.ResidueField) ⊗ₜ[R] b)) =
      Ideal.Quotient.mk _ (algebraMap B (Localization.AtPrime (Q.comap includeRight)) b) := by
  simp [localizationAtPrimeEquivQuotientMap, -Ideal.Quotient.mk_algebraMap]

end Ideal.Fiber
