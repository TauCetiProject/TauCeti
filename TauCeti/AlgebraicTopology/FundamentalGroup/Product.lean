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
(`FundamentalGroupoidFunctor.prodIso`, `FundamentalGroupoidFunctor.piIso`). This file records
the group-level statement: the fundamental *group* of a product is the product of the
fundamental groups, both for binary and for indexed products. It also records the simplest
consequence for path classes: a product of two simply connected spaces is simply connected.

In both equivalences the forward map is the product of the homomorphisms `FundamentalGroup.map`
induced by the coordinate projections, and the inverse assembles a loop class in the product
from its coordinate loop classes by `Path.Homotopic.prod`, respectively `Path.Homotopic.pi`.

## Main declarations

* `FundamentalGroup.prodMulEquiv`: `π₁(X × Y, (x, y)) ≃* π₁(X, x) × π₁(Y, y)`.
* `FundamentalGroup.piMulEquiv`: `π₁(Π i, X i, x) ≃* Π i, π₁(X i, x i)`.
* `TauCeti.instSimplyConnectedSpaceProd`: a product of two simply connected spaces is simply
  connected.
-/

public section

open Path.Homotopic

noncomputable section

namespace FundamentalGroup

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The fundamental group of a binary product is the product of the fundamental groups:
`π₁(X × Y, (x, y)) ≃* π₁(X, x) × π₁(Y, y)`. The forward map is the pair of the maps induced
by the two coordinate projections; the inverse sends a pair of loop classes to their product
`Path.Homotopic.prod`. -/
def prodMulEquiv (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃* FundamentalGroup X x × FundamentalGroup Y y where
  __ := (map (.fst : C(X × Y, X)) (x, y)).prod (map (.snd : C(X × Y, Y)) (x, y))
  invFun γ := .of (prod γ.1.asHom γ.2.asHom)
  left_inv γ := CategoryTheory.End.ext (prod_projLeft_projRight γ.asHom)
  right_inv γ := Prod.ext (CategoryTheory.End.ext (projLeft_prod γ.1.asHom γ.2.asHom))
    (CategoryTheory.End.ext (projRight_prod γ.1.asHom γ.2.asHom))

@[simp]
theorem prodMulEquiv_apply (x : X) (y : Y) (γ : FundamentalGroup (X × Y) (x, y)) :
    prodMulEquiv x y γ =
      (map (.fst : C(X × Y, X)) (x, y) γ, map (.snd : C(X × Y, Y)) (x, y) γ) :=
  (rfl)

@[simp]
theorem prodMulEquiv_symm_apply (x : X) (y : Y)
    (γ : FundamentalGroup X x × FundamentalGroup Y y) :
    (prodMulEquiv x y).symm γ = .of (prod γ.1.asHom γ.2.asHom) :=
  (rfl)

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- The fundamental group of an indexed product is the product of the fundamental groups:
`π₁(Π i, X i, x) ≃* Π i, π₁(X i, x i)`. The forward map records the loop's image under each
coordinate projection; the inverse assembles a loop from its coordinate loops via
`Path.Homotopic.pi`. -/
def piMulEquiv (x : ∀ i, X i) :
    FundamentalGroup (∀ i, X i) x ≃* ∀ i, FundamentalGroup (X i) (x i) where
  __ := MonoidHom.pi fun i ↦ map (.eval i) x
  invFun γ := .of (pi fun i ↦ (γ i).asHom)
  left_inv γ := CategoryTheory.End.ext (pi_proj γ.asHom)
  right_inv γ := funext fun i ↦ CategoryTheory.End.ext (proj_pi i fun i ↦ (γ i).asHom)

@[simp]
theorem piMulEquiv_apply (x : ∀ i, X i) (γ : FundamentalGroup (∀ i, X i) x) (i : ι) :
    piMulEquiv x γ i = map (.eval i) x γ :=
  (rfl)

@[simp]
theorem piMulEquiv_symm_apply (x : ∀ i, X i) (γ : ∀ i, FundamentalGroup (X i) (x i)) :
    (piMulEquiv x).symm γ = .of (pi fun i ↦ (γ i).asHom) :=
  (rfl)

end FundamentalGroup

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A product of two simply connected spaces is simply connected.** A path class in `X × Y`
is the product of its two coordinate classes (`Path.Homotopic.prod_projLeft_projRight`), and
those are unique. -/
instance instSimplyConnectedSpaceProd [SimplyConnectedSpace X] [SimplyConnectedSpace Y] :
    SimplyConnectedSpace (X × Y) := by
  refine simply_connected_iff_paths_homotopic.mpr ⟨inferInstance, fun a b ↦ ⟨fun p q ↦ ?_⟩⟩
  rw [← prod_projLeft_projRight p, ← prod_projLeft_projRight q,
    Subsingleton.elim (projLeft p) (projLeft q), Subsingleton.elim (projRight p) (projRight q)]

end TauCeti

end
