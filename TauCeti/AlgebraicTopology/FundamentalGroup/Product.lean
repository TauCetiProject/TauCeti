/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.Product

/-!
# The fundamental group of a product space

Mathlib knows that the fundamental *groupoid* preserves products
(`FundamentalGroupoidFunctor.prodIso`, `…piIso`), but the corresponding group-level
statement is missing: the fundamental *group* of a product is the product of the
fundamental groups. This file supplies it, both for binary and for indexed products, together
with its simplest consequence: a product of two simply connected spaces is simply connected.

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
`TauCeti/AlgebraicTopology/UniversalCover/Torus/FundamentalGroup.lean` for the torus
application built on top.

## Main declarations

* `TauCeti.FundamentalGroup.prodMulEquiv`: `π₁(X × Y, (x, y)) ≃* π₁(X, x) × π₁(Y, y)`.
* `TauCeti.FundamentalGroup.piMulEquiv`: `π₁(Π i, X i, x) ≃* Π i, π₁(X i, x i)`.
* `TauCeti.instSimplyConnectedSpaceProd`: a product of two simply connected spaces is simply
  connected.
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
  invFun γ := .of (prod γ.1.asHom γ.2.asHom)
  left_inv γ := CategoryTheory.End.ext (prod_projLeft_projRight γ.asHom)
  right_inv γ := Prod.ext (CategoryTheory.End.ext (projLeft_prod γ.1.asHom γ.2.asHom))
    (CategoryTheory.End.ext (projRight_prod γ.1.asHom γ.2.asHom))
  map_mul' γ δ :=
    Prod.ext ((FundamentalGroup.map (ContinuousMap.fst : C(X × Y, X)) (x, y)).map_mul γ δ)
      ((FundamentalGroup.map (ContinuousMap.snd : C(X × Y, Y)) (x, y)).map_mul γ δ)

@[simp]
theorem FundamentalGroup.prodMulEquiv_apply (x : X) (y : Y) (γ : FundamentalGroup (X × Y) (x, y)) :
    FundamentalGroup.prodMulEquiv x y γ =
      (FundamentalGroup.map (ContinuousMap.fst : C(X × Y, X)) (x, y) γ,
        FundamentalGroup.map (ContinuousMap.snd : C(X × Y, Y)) (x, y) γ) :=
  rfl

@[simp]
theorem FundamentalGroup.prodMulEquiv_symm_apply (x : X) (y : Y)
    (γ : FundamentalGroup X x × FundamentalGroup Y y) :
    (FundamentalGroup.prodMulEquiv x y).symm γ = .of (prod γ.1.asHom γ.2.asHom) :=
  rfl

/-- **A product of two simply connected spaces is simply connected.** A path class in `X × Y`
is the product of its two coordinate classes (`Path.Homotopic.prod_projLeft_projRight`), and
those are unique. -/
instance instSimplyConnectedSpaceProd [SimplyConnectedSpace X] [SimplyConnectedSpace Y] :
    SimplyConnectedSpace (X × Y) := by
  refine simply_connected_iff_paths_homotopic.mpr ⟨inferInstance, fun a b ↦ ⟨fun p q ↦ ?_⟩⟩
  rw [← prod_projLeft_projRight p, ← prod_projLeft_projRight q,
    Subsingleton.elim (projLeft p) (projLeft q), Subsingleton.elim (projRight p) (projRight q)]

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- The fundamental group of an indexed product is the product of the fundamental groups:
`π₁(Π i, X i, x) ≃* Π i, π₁(X i, x i)`. The forward map records the loop's image under each
coordinate projection; the inverse assembles a loop from its coordinate loops via
`Path.Homotopic.pi`. -/
@[expose] def FundamentalGroup.piMulEquiv (x : ∀ i, X i) :
    FundamentalGroup (∀ i, X i) x ≃* ∀ i, FundamentalGroup (X i) (x i) where
  toFun γ i := FundamentalGroup.map (ContinuousMap.eval i) x γ
  invFun γ := .of (pi fun i => (γ i).asHom)
  left_inv γ := CategoryTheory.End.ext (pi_proj γ.asHom)
  right_inv γ := funext fun i => CategoryTheory.End.ext (proj_pi i fun i => (γ i).asHom)
  map_mul' γ δ := funext fun i => (FundamentalGroup.map (ContinuousMap.eval i) x).map_mul γ δ

@[simp]
theorem FundamentalGroup.piMulEquiv_apply (x : ∀ i, X i)
    (γ : FundamentalGroup (∀ i, X i) x) (i : ι) :
    FundamentalGroup.piMulEquiv x γ i = FundamentalGroup.map (ContinuousMap.eval i) x γ :=
  rfl

@[simp]
theorem FundamentalGroup.piMulEquiv_symm_apply (x : ∀ i, X i)
    (γ : ∀ i, FundamentalGroup (X i) (x i)) :
    (FundamentalGroup.piMulEquiv x).symm γ = .of (pi fun i => (γ i).asHom) :=
  rfl

end

end TauCeti
