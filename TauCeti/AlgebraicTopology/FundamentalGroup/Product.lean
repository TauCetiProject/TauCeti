/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.Product
public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# The fundamental group of a product space

Mathlib knows that the fundamental *groupoid* preserves products
(`FundamentalGroupoidFunctor.prodIso`, `…piIso`), but the corresponding group-level
statement is missing: the fundamental *group* of a product is the product of the
fundamental groups. This file supplies it, both for binary and for indexed products.

The two equivalences are built directly from the path-class product operations
`Path.Homotopic.prod` / `Path.Homotopic.pi` and their coordinate projections, which already
descend homotopy and composition through the quotient. The forward map is the pair (resp.
tuple) of the maps induced by the coordinate projections, packaged through Mathlib's
`FundamentalGroup.map`; the inverse assembles a loop in the product from its coordinate
loops. The projection-product round trips
(`Path.Homotopic.prod_projLeft_projRight`, `…projLeft_prod`, `…projRight_prod`,
`…pi_proj`, `…proj_pi`) make both composites the identity, and `FundamentalGroup.map`
being a `MonoidHom` supplies multiplicativity.

This is the group-level input the universal-covers roadmap calls for when computing
`π₁(Tᵏ)` (Stage 4, "applications": `π_n(Tᵏ)`); see
`TauCeti/AlgebraicTopology/UniversalCover/TorusFundamentalGroup.lean` for the torus
application built on top.

When one factor is simply connected its fundamental group is a subsingleton, so the product
formula collapses to the fundamental group of the other factor; this is the standard fact
that a simply connected factor does not change `π₁`. The maps are built directly from the
same projection/product operations, using `Subsingleton (FundamentalGroup _ _)` (Mathlib's
`SimplyConnectedSpace` instance) to discard the trivial coordinate.

## Main declarations

* `TauCeti.FundamentalGroup.prodMulEquiv`: `π₁(X × Y, (x, y)) ≃* π₁(X, x) × π₁(Y, y)`.
* `TauCeti.FundamentalGroup.piMulEquiv`: `π₁(Π i, X i, x) ≃* Π i, π₁(X i, x i)`.
* `TauCeti.FundamentalGroup.prodMulEquivOfSimplyConnectedRight`: for simply connected `Y`,
  `π₁(X × Y, (x, y)) ≃* π₁(X, x)`.
* `TauCeti.FundamentalGroup.prodMulEquivOfSimplyConnectedLeft`: for simply connected `X`,
  `π₁(X × Y, (x, y)) ≃* π₁(Y, y)`.
-/

public section

namespace TauCeti

open Path.Homotopic

noncomputable section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The fundamental group of a binary product is the product of the fundamental groups:
`π₁(X × Y, (x, y)) ≃* π₁(X, x) × π₁(Y, y)`. The forward map is the pair of the maps induced
by the two coordinate projections; the inverse sends a pair of loop classes to their product
`Path.Homotopic.prod`. -/
@[expose] def FundamentalGroup.prodMulEquiv (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃*
      FundamentalGroup X x × FundamentalGroup Y y where
  toFun γ :=
    (FundamentalGroup.map (ContinuousMap.fst : C(X × Y, X)) (x, y) γ,
      FundamentalGroup.map (ContinuousMap.snd : C(X × Y, Y)) (x, y) γ)
  invFun γ := prod γ.1 γ.2
  left_inv γ := prod_projLeft_projRight γ
  right_inv γ := Prod.ext (projLeft_prod γ.1 γ.2) (projRight_prod γ.1 γ.2)
  map_mul' γ δ :=
    Prod.ext ((FundamentalGroup.map (ContinuousMap.fst : C(X × Y, X)) (x, y)).map_mul γ δ)
      ((FundamentalGroup.map (ContinuousMap.snd : C(X × Y, Y)) (x, y)).map_mul γ δ)

@[simp]
theorem FundamentalGroup.prodMulEquiv_apply (x : X) (y : Y)
    (γ : FundamentalGroup (X × Y) (x, y)) :
    FundamentalGroup.prodMulEquiv x y γ =
      (FundamentalGroup.map (ContinuousMap.fst : C(X × Y, X)) (x, y) γ,
        FundamentalGroup.map (ContinuousMap.snd : C(X × Y, Y)) (x, y) γ) :=
  rfl

@[simp]
theorem FundamentalGroup.prodMulEquiv_symm_apply (x : X) (y : Y)
    (γ : FundamentalGroup X x × FundamentalGroup Y y) :
    (FundamentalGroup.prodMulEquiv x y).symm γ = prod γ.1 γ.2 :=
  rfl

/-- If the right factor is simply connected, the fundamental group of the product is the
fundamental group of the left factor: `π₁(X × Y, (x, y)) ≃* π₁(X, x)`. It is the product
formula `prodMulEquiv` followed by the collapse of the trivial second factor. -/
@[expose] def FundamentalGroup.prodMulEquivOfSimplyConnectedRight [SimplyConnectedSpace Y]
    (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃* FundamentalGroup X x :=
  (FundamentalGroup.prodMulEquiv x y).trans MulEquiv.prodUnique

@[simp]
theorem FundamentalGroup.prodMulEquivOfSimplyConnectedRight_apply [SimplyConnectedSpace Y]
    (x : X) (y : Y) (γ : FundamentalGroup (X × Y) (x, y)) :
    FundamentalGroup.prodMulEquivOfSimplyConnectedRight x y γ =
      FundamentalGroup.map (ContinuousMap.fst : C(X × Y, X)) (x, y) γ :=
  rfl

@[simp]
theorem FundamentalGroup.prodMulEquivOfSimplyConnectedRight_symm_apply [SimplyConnectedSpace Y]
    (x : X) (y : Y) (γ : FundamentalGroup X x) :
    (FundamentalGroup.prodMulEquivOfSimplyConnectedRight x y).symm γ =
      prod γ (1 : FundamentalGroup Y y) :=
  rfl

/-- If the left factor is simply connected, the fundamental group of the product is the
fundamental group of the right factor: `π₁(X × Y, (x, y)) ≃* π₁(Y, y)`. It is the product
formula `prodMulEquiv` followed by the collapse of the trivial first factor. -/
@[expose] def FundamentalGroup.prodMulEquivOfSimplyConnectedLeft [SimplyConnectedSpace X]
    (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃* FundamentalGroup Y y :=
  (FundamentalGroup.prodMulEquiv x y).trans MulEquiv.uniqueProd

@[simp]
theorem FundamentalGroup.prodMulEquivOfSimplyConnectedLeft_apply [SimplyConnectedSpace X]
    (x : X) (y : Y) (γ : FundamentalGroup (X × Y) (x, y)) :
    FundamentalGroup.prodMulEquivOfSimplyConnectedLeft x y γ =
      FundamentalGroup.map (ContinuousMap.snd : C(X × Y, Y)) (x, y) γ :=
  rfl

@[simp]
theorem FundamentalGroup.prodMulEquivOfSimplyConnectedLeft_symm_apply [SimplyConnectedSpace X]
    (x : X) (y : Y) (γ : FundamentalGroup Y y) :
    (FundamentalGroup.prodMulEquivOfSimplyConnectedLeft x y).symm γ =
      prod (1 : FundamentalGroup X x) γ :=
  rfl

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- The fundamental group of an indexed product is the product of the fundamental groups:
`π₁(Π i, X i, x) ≃* Π i, π₁(X i, x i)`. The forward map records the loop's image under each
coordinate projection; the inverse assembles a loop from its coordinate loops via
`Path.Homotopic.pi`. -/
@[expose] def FundamentalGroup.piMulEquiv (x : ∀ i, X i) :
    FundamentalGroup (∀ i, X i) x ≃* ∀ i, FundamentalGroup (X i) (x i) where
  toFun γ i := FundamentalGroup.map (ContinuousMap.eval i) x γ
  invFun γ := pi γ
  left_inv γ := pi_proj γ
  right_inv γ := funext fun i => proj_pi i γ
  map_mul' γ δ := funext fun i => (FundamentalGroup.map (ContinuousMap.eval i) x).map_mul γ δ

@[simp]
theorem FundamentalGroup.piMulEquiv_apply (x : ∀ i, X i)
    (γ : FundamentalGroup (∀ i, X i) x) (i : ι) :
    FundamentalGroup.piMulEquiv x γ i = FundamentalGroup.map (ContinuousMap.eval i) x γ :=
  rfl

@[simp]
theorem FundamentalGroup.piMulEquiv_symm_apply (x : ∀ i, X i)
    (γ : ∀ i, FundamentalGroup (X i) (x i)) :
    (FundamentalGroup.piMulEquiv x).symm γ = pi γ :=
  rfl

end

end TauCeti
