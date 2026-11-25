/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Star
public import TauCeti.Analysis.StarAlgebra.GNS.Basic

/-!
# The identity coefficient of a complex twisted group algebra as a positive functional

Over `ℂ`, for a group `G` and a factor set `α` with values on the unit circle
(`TauCeti.IsUnitaryFactorSet`), the coefficient at the identity of the star algebra `ℂ_α[G]`
satisfies `(star x * x)_1 = Σ_g |x_g|²`
(`TauCeti.TwistedMonoidAlgebra.repr_star_mul_self_apply_one`). It is therefore a positive
functional, with trivial GNS null space since it is faithful.

## Main definitions

* `TauCeti.TwistedMonoidAlgebra.identityCoefficient`: the coefficient at the identity as a
  positive functional.

## Main results

* `TauCeti.TwistedMonoidAlgebra.nullSubmodule_identityCoefficient`: the coefficient at the
  identity has trivial GNS null space.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 3.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

open scoped ComplexOrder

variable {G : Type*} [Group G] {α : G → G → ℂˣ} [IsFactorSet α] [IsUnitaryFactorSet α]

/-- Over `ℂ`, **the coefficient at the identity** as a positive functional on `ℂ_α[G]`. -/
noncomputable def identityCoefficient : StarPositiveFunctional (twistedMonoidAlgebra ℂ G α) where
  toLinearMap := (basis ℂ G α).coord 1
  square_nonneg := repr_star_mul_self_apply_one_nonneg

/-- `identityCoefficient` evaluates as the coefficient at the identity. -/
@[simp]
theorem identityCoefficient_apply (x : twistedMonoidAlgebra ℂ G α) :
    identityCoefficient x = (basis ℂ G α).repr x 1 :=
  (rfl)

/-- The coefficient at the identity is faithful: its GNS null space is trivial. -/
theorem nullSubmodule_identityCoefficient :
    (identityCoefficient : StarPositiveFunctional (twistedMonoidAlgebra ℂ G α)).nullSubmodule =
      ⊥ := by
  ext x
  simp

end TauCeti.TwistedMonoidAlgebra
