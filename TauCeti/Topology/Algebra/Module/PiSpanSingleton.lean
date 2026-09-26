/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import TauCeti.LinearAlgebra.Quotient.PiSpanSingleton

/-!
# Continuity of the reduction of `X → R` modulo one vector with a unit coordinate

Over a topological commutative ring `R`, the reduction

`LinearMap.piSplitAtQuot x₀ w hw q : (X → R) →ₗ[R] ({x // x ≠ x₀} → R) × R ⧸ (q)`

of `TauCeti.LinearAlgebra.Quotient.PiSpanSingleton`, which sends `u` to the coordinates
`u x - u x₀ * w x` for `x ≠ x₀` together with the class of `u x₀` modulo `q`, is continuous for
the product topology on `X → R` and the quotient topology on `R ⧸ (q)`. Since the coordinate
formula involves only subtraction and multiplication by the constants `w x`, continuity of these
two operations on `R` suffices.

The reduction is also packaged as a continuous homomorphism between the multiplicative type tags
of the two additive groups, which is the form in which it is applied to abelian pro-`p` groups
written multiplicatively.

## Main definitions

* `TauCeti.ContinuousMonoidHom.piSplitAtQuotMultiplicative`: the reduction as a continuous
  homomorphism `Multiplicative (X → R) →ₜ* Multiplicative (({x // x ≠ x₀} → R) × R ⧸ (q))`.

## Main results

* `TauCeti.LinearMap.continuous_piSplitAtQuot`: the reduction is continuous.
* `TauCeti.ContinuousMonoidHom.piSplitAtQuotMultiplicative_ofAdd`: the value of the
  multiplicative form on `ofAdd u` is `ofAdd` of the reduction of `u`.
-/

public section

namespace TauCeti

open Multiplicative

variable {R : Type*} [CommRing R] [TopologicalSpace R] [ContinuousSub R] [ContinuousMul R]
  {X : Type*} (x₀ : X) (w : X → R) (hw : w x₀ = 1) (q : R)

/-- The reduction `(X → R) → ({x // x ≠ x₀} → R) × R ⧸ (q)` of `TauCeti.LinearMap.piSplitAtQuot`
is continuous, for the product topology on `X → R` and the quotient topology on `R ⧸ (q)`. -/
theorem LinearMap.continuous_piSplitAtQuot : Continuous (LinearMap.piSplitAtQuot x₀ w hw q) := by
  have h : ⇑(LinearMap.piSplitAtQuot x₀ w hw q) = fun u : X → R ↦
      (fun x : {x // x ≠ x₀} ↦ u x - u x₀ * w x,
        (Submodule.Quotient.mk (u x₀) : R ⧸ Ideal.span {q})) :=
    funext (LinearMap.piSplitAtQuot_apply x₀ w hw q)
  rw [h]
  refine Continuous.prodMk (continuous_pi fun x ↦ ?_)
    (continuous_quot_mk.comp (continuous_apply x₀))
  exact (continuous_apply (x : X)).sub ((continuous_apply x₀).mul continuous_const)

/-- The reduction `TauCeti.LinearMap.piSplitAtQuot` as a continuous homomorphism
`Multiplicative (X → R) →ₜ* Multiplicative (({x // x ≠ x₀} → R) × R ⧸ (q))` between the
multiplicative type tags. -/
noncomputable def ContinuousMonoidHom.piSplitAtQuotMultiplicative :
    Multiplicative (X → R) →ₜ* Multiplicative (({x // x ≠ x₀} → R) × (R ⧸ Ideal.span {q})) where
  toMonoidHom := (LinearMap.piSplitAtQuot x₀ w hw q).toAddMonoidHom.toMultiplicative
  continuous_toFun :=
    continuous_ofAdd.comp ((LinearMap.continuous_piSplitAtQuot x₀ w hw q).comp continuous_toAdd)

@[simp]
theorem ContinuousMonoidHom.piSplitAtQuotMultiplicative_ofAdd (u : X → R) :
    ContinuousMonoidHom.piSplitAtQuotMultiplicative x₀ w hw q (ofAdd u) =
      ofAdd (LinearMap.piSplitAtQuot x₀ w hw q u) :=
  (rfl)

end TauCeti
