/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.CategoryTheory.Groupoid.SingleObj
public import TauCeti.CategoryTheory.Groupoid.ConnectedFunctor
public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# The local system of a representation of the fundamental group

On a path-connected pointed space `(X, x)`, every representation `ρ` of `π₁(X, x)` on an
`R`-module `V` is the monodromy representation of a local system: every fiber is `V`, and a path
class from `y` to `z` acts by `ρ` of the loop at `x` obtained by closing it up with chosen paths
from `x` to `y` and to `z`.  The chosen path at `x` itself is the constant one, so the monodromy at
`x` is `ρ` on the nose (`monodromyRepresentation_ofRepresentation`).  Conversely, every local
system `L` is the local system of its monodromy representation at `x`, up to an isomorphism which
is the identity at `x` (`ofRepresentationMonodromyIso`), so `ofRepresentation` inverts the
monodromy representation up to isomorphism.

The functor out of the fundamental groupoid is `TauCeti.Groupoid.functorOfEndHom`, which only
uses that every point is joined to `x`.

## Main definitions

* `TauCeti.LocalCoefficientSystem.pathFromBase`: the chosen path classes out of the basepoint.
* `TauCeti.LocalCoefficientSystem.ofRepresentation`: the local system of a representation.
* `TauCeti.LocalCoefficientSystem.ofRepresentationMonodromyIso`: a local system is the local system
  of its monodromy representation.

## Main results

* `TauCeti.LocalCoefficientSystem.monodromyRepresentation_ofRepresentation`: its monodromy at the
  basepoint is the given representation.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Graduate Texts in Mathematics 61, Springer,
  1978, Chapter VI, §1 (local systems on a path-connected space and `π₁`-modules).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 2 and 7.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {X : TopCat.{v}} [PathConnectedSpace X] (x : X)

/-- Chosen path classes out of the basepoint of a path-connected space, normalized to be the
identity at the basepoint: a chosen path to `y` preceded by the inverse of the chosen loop at
`x`. -/
def pathFromBase (y : FundamentalGroupoid X) : FundamentalGroupoid.mk x ⟶ y :=
  inv (show FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x from
      (⟦PathConnectedSpace.somePath x x⟧ : Path.Homotopic.Quotient x x)) ≫
    (⟦PathConnectedSpace.somePath x y.as⟧ : Path.Homotopic.Quotient x y.as)

/-- The chosen path class from the basepoint to itself is the identity. -/
@[simp]
theorem pathFromBase_mk : pathFromBase x (FundamentalGroupoid.mk x) = 𝟙 _ :=
  IsIso.inv_hom_id _

variable {R : Type u} [Ring R] {V : Type w} [AddCommGroup V] [Module R V]

/-- **The local system of a representation of the fundamental group**: on a path-connected space,
every fiber is `V`, and a path class from `y` to `z` acts by `ρ` of the loop at `x` closed up by
the chosen paths `pathFromBase x y` and `pathFromBase x z`. -/
-- Exposed so that the fibers are `V` by definition downstream: identifying the DG local system
-- of this local system with a given module needs its carrier to be that module.
@[expose] def ofRepresentation (ρ : Representation R (FundamentalGroup X x) V) :
    LocalCoefficientSystem.{u, v, w} R X :=
  Groupoid.functorOfEndHom (FundamentalGroupoid.mk x) (pathFromBase x)
      (((ModuleCat.endRingEquiv (ModuleCat.of R V)).symm :
        Module.End R V →* End (ModuleCat.of R V)).comp ρ) ⋙
    Groupoid.singleObjFunctor (ModuleCat.of R V)

/-- Every fiber of the local system of a representation on `V` is `V`. -/
@[simp]
theorem ofRepresentation_obj (ρ : Representation R (FundamentalGroup X x) V)
    (y : FundamentalGroupoid X) : (ofRepresentation x ρ).obj y = ModuleCat.of R V :=
  (rfl)

/-- A path class acts on the fibers, all equal to `V`, by `ρ` of the loop at the basepoint
closed up by the chosen paths. -/
theorem ofRepresentation_map_apply (ρ : Representation R (FundamentalGroup X x) V)
    {y z : FundamentalGroupoid X} (p : y ⟶ z) (v : V) :
    (ofRepresentation x ρ).map p v = ρ (pathFromBase x y ≫ p ≫ inv (pathFromBase x z)) v := by
  -- Unfold `ofRepresentation`: its second factor `Groupoid.singleObjFunctor` is the identity on
  -- morphisms (`Groupoid.singleObjFunctor_map`), which `rw` cannot apply since the objects of the
  -- first factor are the unique object of `SingleObj` only by unfolding `functorOfEndHom_obj`.
  change ((Groupoid.functorOfEndHom (FundamentalGroupoid.mk x) (pathFromBase x)
    (((ModuleCat.endRingEquiv (ModuleCat.of R V)).symm :
        Module.End R V →* End (ModuleCat.of R V)).comp ρ)).map p).hom v = _
  rw [Groupoid.functorOfEndHom_map, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
    ModuleCat.endRingEquiv_symm_apply_hom]

/-- **The monodromy of the local system of a representation is that representation.** -/
@[simp]
theorem monodromyRepresentation_ofRepresentation
    (ρ : Representation R (FundamentalGroup X x) V) :
    monodromyRepresentation (ofRepresentation x ρ) x = ρ := by
  ext g v
  refine (ofRepresentation_map_apply x ρ g v).trans ?_
  rw [pathFromBase_mk, IsIso.inv_id, Category.id_comp, Category.comp_id]
  rfl

/-- **A local system is the local system of its monodromy representation**: on a path-connected
space, the isomorphism `ofRepresentation x (monodromyRepresentation L x) ≅ L` which is the
identity of the fiber at `x`. -/
def ofRepresentationMonodromyIso (L : LocalCoefficientSystem.{u, v, w} R X) :
    ofRepresentation x (monodromyRepresentation L x) ≅ L :=
  Groupoid.natIsoOfEnd (FundamentalGroupoid.nonempty_hom _) (Iso.refl (L.obj _)) fun g ↦ by
    ext v
    -- The fiber of `ofRepresentation` at `x` is `ModuleCat.of R (L.obj _)`, equal to `L.obj _`
    -- only up to eta, so the identities are removed by `change` rather than `Category.comp_id`.
    change (ofRepresentation x (monodromyRepresentation L x)).map g v = L.map g v
    refine (ofRepresentation_map_apply x _ g v).trans ?_
    rw [pathFromBase_mk, IsIso.inv_id, Category.id_comp, Category.comp_id]
    exact monodromyRepresentation_apply L x g v

/-- The isomorphism `ofRepresentationMonodromyIso` is the identity at the basepoint. -/
@[simp]
theorem ofRepresentationMonodromyIso_app_mk (L : LocalCoefficientSystem.{u, v, w} R X) :
    (ofRepresentationMonodromyIso x L).app (FundamentalGroupoid.mk x) = Iso.refl _ :=
  Groupoid.natIsoOfEnd_app_self _ _ _

end TauCeti.LocalCoefficientSystem
