/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient

/-!
# External tensor products of local coefficient systems

For local coefficient systems `L` on `X` and `K` on `Y`, of modules over a commutative ring `S`,
the external tensor product `L.externalTensor K` is the local system on `X × Y` whose fibre at
`(x, y)` is `L(x) ⊗[S] K(y)` (`TauCeti.LocalCoefficientSystem.externalTensor_obj`). It is the
pointwise tensor product of the pullbacks of `L` and `K` along the two projections, so parallel
transport along a path in `X × Y` is the tensor product of the transports along its two
components (`TauCeti.LocalCoefficientSystem.transport_externalTensor_tmul`). These are the
coefficients of the Künneth formula with local coefficients, for instance for the Morse complex of
a product manifold.

Mathlib's external product of diagrams (`CategoryTheory.MonoidalCategory.externalProduct`) has
the same values, but is a functor on the product `πX × πY` of the fundamental groupoids rather
than on the fundamental groupoid of `X × Y`. The construction here is on `π(X × Y)`, through the
pullback of local systems, so that it is again a local coefficient system and the transport API
applies to it.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw-Hill, 1966, §5.5 (the cross product with
  coefficients in a tensor product of coefficient systems).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory TensorProduct

universe w v₁ v₂

namespace TauCeti

namespace LocalCoefficientSystem

variable {S : Type w} [CommRing S] {X : TopCat.{v₁}} {Y : TopCat.{v₂}}

/-- **The external tensor product of local coefficient systems.** For `L` on `X` and `K` on `Y`,
the local system on `X × Y` whose fibre at `(x, y)` is `L(x) ⊗ K(y)`: the tensor product of the
pullbacks of `L` and `K` along the two projections. -/
@[expose] def externalTensor (L : LocalCoefficientSystem.{w, v₁, w} S X)
    (K : LocalCoefficientSystem.{w, v₂, w} S Y) :
    LocalCoefficientSystem.{w, max v₁ v₂, w} S (TopCat.of (X × Y)) :=
  (pullback (X := TopCat.of (X × Y)) ContinuousMap.fst).obj L ⊗
    (pullback (X := TopCat.of (X × Y)) ContinuousMap.snd).obj K

variable (L : LocalCoefficientSystem.{w, v₁, w} S X) (K : LocalCoefficientSystem.{w, v₂, w} S Y)

/-- The fibre of the external tensor product at `(x, y)` is the tensor product of the fibres of
the factors at `x` and at `y`. -/
@[simp]
theorem externalTensor_obj (x : X) (y : Y) :
    (L.externalTensor K).obj (FundamentalGroupoid.mk ((x, y) : X × Y)) =
      L.obj (FundamentalGroupoid.mk x) ⊗ K.obj (FundamentalGroupoid.mk y) :=
  (rfl)

/-- **Transport in an external tensor product.** Parallel transport along a path class `γ` in
`X × Y` is the tensor product of the transports along its images in `X` and in `Y`. -/
@[simp]
theorem transport_externalTensor_tmul {a b : X × Y} (γ : Path.Homotopic.Quotient a b)
    (u : L.obj (FundamentalGroupoid.mk a.1)) (v : K.obj (FundamentalGroupoid.mk a.2)) :
    transport (L.externalTensor K) γ (u ⊗ₜ[S] v) =
      transport L (γ.map ContinuousMap.fst) u ⊗ₜ[S] transport K (γ.map ContinuousMap.snd) v := by
  -- The transport of the external tensor product unfolds to the tensor product of the maps of the
  -- pulled-back systems, whose fibres are those of `L` and `K` only up to unfolding `pullback`;
  -- the steps are chained with `Eq.trans` rather than `rw`, which cannot see through it.
  refine (transport_apply (X := TopCat.of (X × Y)) (L.externalTensor K) γ (u ⊗ₜ[S] v)).trans ?_
  refine (ModuleCat.MonoidalCategory.tensorHom_tmul
    (((pullback (X := TopCat.of (X × Y)) ContinuousMap.fst).obj L).map γ)
    (((pullback (X := TopCat.of (X × Y)) ContinuousMap.snd).obj K).map γ) u v).trans ?_
  exact congrArg₂ _ (transport_apply L _ u).symm (transport_apply K _ v).symm

end LocalCoefficientSystem

end TauCeti
