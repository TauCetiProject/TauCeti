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
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

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

The construction is functorial. A linear map intertwining two representations induces the
morphism of their local systems which is that map on every fiber (`ofRepresentationMap`), and it
is the only morphism with that component at `x` (`eq_ofRepresentationMap`); conversely the
component at `x` of any morphism of local systems intertwines the representations
(`ofRepresentationHomEquiv`). An equivalence of representations induces an isomorphism of their
local systems in the same way (`ofRepresentationIso`). On the category `Rep R π₁(X, x)` this is a
fully faithful functor (`ofRepresentationFunctor`), essentially surjective because every local
system is the local system of its monodromy, hence an equivalence. In particular it preserves
limits and colimits, so a short exact sequence of representations gives a short exact sequence of
local systems (`shortExact_map_ofRepresentationFunctor`). Composing with `Rep.resFunctor`
gives the same for the local systems of representations of any group `G` pulled back along a
homomorphism `π₁(X, x) →* G`, which is how the coefficients of group (co)homology of `G` become
local systems on a space with fundamental group `G`.

The functor out of the fundamental groupoid is `TauCeti.Groupoid.functorOfEndHom`, which only
uses that every point is joined to `x`.

## Main definitions

* `TauCeti.LocalCoefficientSystem.pathFromBase`: the chosen path classes out of the basepoint.
* `TauCeti.LocalCoefficientSystem.ofRepresentation`: the local system of a representation.
* `TauCeti.LocalCoefficientSystem.ofRepresentationMap`: an intertwining map induces a morphism of
  local systems.
* `TauCeti.LocalCoefficientSystem.ofRepresentationHomEquiv`: morphisms between the local systems
  of two representations are the intertwining maps.
* `TauCeti.LocalCoefficientSystem.ofRepresentationIso`: equivalent representations have isomorphic
  local systems.
* `TauCeti.LocalCoefficientSystem.ofRepresentationFunctor`: the local system of a representation,
  as a functor out of `Rep R π₁(X, x)`; it is an equivalence onto local systems on `X`.
* `TauCeti.LocalCoefficientSystem.ofRepresentationMonodromyIso`: a local system is the local system
  of its monodromy representation.

## Main results

* `TauCeti.LocalCoefficientSystem.monodromyRepresentation_ofRepresentation`: its monodromy at the
  basepoint is the given representation.
* `TauCeti.LocalCoefficientSystem.eq_ofRepresentationMap`, `eq_ofRepresentationIso`: a morphism or
  isomorphism of such local systems is determined by its component at the basepoint.
* `TauCeti.LocalCoefficientSystem.shortExact_map_ofRepresentationFunctor`: short exact sequences
  of representations give short exact sequences of local systems.

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
    (ofRepresentation x ρ).map p v =
      ρ (FundamentalGroup.fromArrow (pathFromBase x y ≫ p ≫ inv (pathFromBase x z))) v := by
  -- Unfold `ofRepresentation`: its second factor `Groupoid.singleObjFunctor` is the identity on
  -- morphisms (`Groupoid.singleObjFunctor_map`), which `rw` cannot apply since the objects of the
  -- first factor are the unique object of `SingleObj` only by unfolding `functorOfEndHom_obj`.
  change ((Groupoid.functorOfEndHom (FundamentalGroupoid.mk x) (pathFromBase x)
    (((ModuleCat.endRingEquiv (ModuleCat.of R V)).symm :
        Module.End R V →* End (ModuleCat.of R V)).comp ρ)).map p).asHom.hom v = _
  rw [Groupoid.functorOfEndHom_map, MonoidHom.comp_apply, MonoidHom.coe_ofClass]
  -- `endRingEquiv.symm f` is `End.of (ModuleCat.ofHom f)` by definition, whose linear map is `f`.
  rfl

/-- **The monodromy of the local system of a representation is that representation.** -/
@[simp]
theorem monodromyRepresentation_ofRepresentation
    (ρ : Representation R (FundamentalGroup X x) V) :
    monodromyRepresentation (ofRepresentation x ρ) x = ρ := by
  ext g v
  refine (ofRepresentation_map_apply x ρ g.asHom v).trans ?_
  rw [pathFromBase_mk, IsIso.inv_id, Category.id_comp, Category.comp_id]
  rfl

section Map

variable {W : Type w} [AddCommGroup W] [Module R W] {ρ : Representation R (FundamentalGroup X x) V}
  {σ : Representation R (FundamentalGroup X x) W}

/-- **An intertwining map of representations is a morphism of their local systems**: a linear map
`f : V → W` intertwining `ρ` and `σ` is the morphism `ofRepresentation x ρ ⟶ ofRepresentation x σ`
which is `f` on every fiber. It is the only morphism with component `f` at the basepoint
(`eq_ofRepresentationMap`). -/
def ofRepresentationMap (f : ρ.IntertwiningMap σ) :
    ofRepresentation x ρ ⟶ ofRepresentation x σ where
  app _ := ModuleCat.ofHom f.toLinearMap
  naturality _ _ p := by
    ext v
    -- Every fiber is `V`, respectively `W`, only by unfolding `ofRepresentation_obj`, so the
    -- composites in `ModuleCat` are evaluated by `change` rather than by `ModuleCat.hom_comp`.
    change f ((ofRepresentation x ρ).map p v) = (ofRepresentation x σ).map p (f v)
    refine (congrArg f (ofRepresentation_map_apply x ρ p v)).trans ?_
    refine (Representation.IntertwiningMap.isIntertwining _ _ f _ v).trans ?_
    exact (ofRepresentation_map_apply x σ p (f v)).symm

/-- The morphism of local systems induced by an intertwining map is that map on every fiber. -/
@[simp]
theorem ofRepresentationMap_app_apply (f : ρ.IntertwiningMap σ) (y : FundamentalGroupoid X)
    (v : V) : ((ofRepresentationMap x f).app y).hom v = f v :=
  (rfl)

/-- A morphism between the local systems of two representations is the morphism induced by an
intertwining map as soon as its component at the basepoint is that map. -/
theorem eq_ofRepresentationMap (f : ρ.IntertwiningMap σ)
    (α : ofRepresentation x ρ ⟶ ofRepresentation x σ)
    (hα : ∀ v : V, (α.app (FundamentalGroupoid.mk x)).hom v = f v) :
    α = ofRepresentationMap x f :=
  Groupoid.natTrans_ext (FundamentalGroupoid.nonempty_hom _) (ModuleCat.hom_ext (LinearMap.ext hα))

/-- The identity map of a representation induces the identity of its local system. -/
@[simp]
theorem ofRepresentationMap_id :
    ofRepresentationMap x (Representation.IntertwiningMap.id ρ) = 𝟙 (ofRepresentation x ρ) :=
  ((eq_ofRepresentationMap x _ _ fun _ ↦ rfl).symm)

/-- The morphism of local systems induced by a composite of intertwining maps is the composite of
the induced morphisms. -/
@[simp]
theorem ofRepresentationMap_comp {U : Type w} [AddCommGroup U] [Module R U]
    {τ : Representation R (FundamentalGroup X x) U} (f : ρ.IntertwiningMap σ)
    (g : σ.IntertwiningMap τ) :
    ofRepresentationMap x (g.comp f) = ofRepresentationMap x f ≫ ofRepresentationMap x g :=
  ((eq_ofRepresentationMap x _ _ fun _ ↦ rfl).symm)

/-- **Morphisms between the local systems of representations are intertwining maps**: taking the
component at the basepoint is a bijection from morphisms
`ofRepresentation x ρ ⟶ ofRepresentation x σ` to intertwining maps from `ρ` to `σ`, whose inverse
is `ofRepresentationMap`. -/
def ofRepresentationHomEquiv :
    (ofRepresentation x ρ ⟶ ofRepresentation x σ) ≃ ρ.IntertwiningMap σ where
  toFun α :=
    { toLinearMap := (α.app (FundamentalGroupoid.mk x)).hom
      isIntertwining' := fun g ↦ by
        ext v
        -- The monodromy of both local systems at the basepoint is the given representation, and
        -- `α` commutes with the monodromy along the loop `g`.
        have hρ := congrArg (fun r ↦ r g v) (monodromyRepresentation_ofRepresentation x ρ)
        have hσ := congrArg (fun r ↦ r g ((α.app _).hom v))
          (monodromyRepresentation_ofRepresentation x σ)
        exact (congrArg (α.app _).hom hρ.symm).trans ((α.naturality_apply g.asHom v).trans hσ) }
  invFun := ofRepresentationMap x
  left_inv α := (eq_ofRepresentationMap x _ α fun _ ↦ rfl).symm
  right_inv _ := rfl

/-- The intertwining map of a morphism of local systems is its component at the basepoint. -/
@[simp]
theorem ofRepresentationHomEquiv_apply_apply (α : ofRepresentation x ρ ⟶ ofRepresentation x σ)
    (v : V) : ofRepresentationHomEquiv x α v = (α.app (FundamentalGroupoid.mk x)).hom v :=
  (rfl)

/-- The inverse of `ofRepresentationHomEquiv` is `ofRepresentationMap`. -/
@[simp]
theorem ofRepresentationHomEquiv_symm_apply (f : ρ.IntertwiningMap σ) :
    (ofRepresentationHomEquiv x).symm f = ofRepresentationMap x f :=
  (rfl)

/-- **Equivalent representations have isomorphic local systems**: an equivalence `e` of
representations of `π₁(X, x)` is an isomorphism of their local systems which is `e` on every
fiber. -/
def ofRepresentationIso (e : ρ.Equiv σ) : ofRepresentation x ρ ≅ ofRepresentation x σ where
  hom := ofRepresentationMap x e.toIntertwiningMap
  inv := ofRepresentationMap x e.symm.toIntertwiningMap
  hom_inv_id := by
    rw [← ofRepresentationMap_comp, ← ofRepresentationMap_id]
    exact congrArg _ (Representation.IntertwiningMap.ext (LinearMap.ext e.symm_apply_apply))
  inv_hom_id := by
    rw [← ofRepresentationMap_comp, ← ofRepresentationMap_id]
    exact congrArg _ (Representation.IntertwiningMap.ext (LinearMap.ext e.apply_symm_apply))

/-- The isomorphism of local systems induced by an equivalence of representations is the morphism
induced by the underlying intertwining map. -/
theorem ofRepresentationIso_hom (e : ρ.Equiv σ) :
    (ofRepresentationIso x e).hom = ofRepresentationMap x e.toIntertwiningMap :=
  (rfl)

/-- The inverse of the isomorphism of local systems induced by an equivalence of representations
is the morphism induced by the inverse equivalence. -/
theorem ofRepresentationIso_inv (e : ρ.Equiv σ) :
    (ofRepresentationIso x e).inv = ofRepresentationMap x e.symm.toIntertwiningMap :=
  (rfl)

/-- The isomorphism of local systems induced by an equivalence of representations is that
equivalence on every fiber. -/
@[simp]
theorem ofRepresentationIso_hom_app_apply (e : ρ.Equiv σ) (y : FundamentalGroupoid X) (v : V) :
    ((ofRepresentationIso x e).hom.app y).hom v = e v :=
  (rfl)

/-- The inverse of the isomorphism of local systems induced by an equivalence of representations
is the inverse equivalence on every fiber. -/
@[simp]
theorem ofRepresentationIso_inv_app_apply (e : ρ.Equiv σ) (y : FundamentalGroupoid X) (w : W) :
    ((ofRepresentationIso x e).inv.app y).hom w = e.symm w :=
  (rfl)

/-- An isomorphism between the local systems of two representations is the isomorphism induced by
an equivalence of representations as soon as its component at the basepoint is that
equivalence. -/
theorem eq_ofRepresentationIso (e : ρ.Equiv σ) (α : ofRepresentation x ρ ≅ ofRepresentation x σ)
    (hα : ∀ v : V, (α.hom.app (FundamentalGroupoid.mk x)).hom v = e v) :
    α = ofRepresentationIso x e :=
  Iso.ext (eq_ofRepresentationMap x _ α.hom hα)

end Map

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
    exact monodromyRepresentation_apply L x (FundamentalGroup.fromArrow g) v

/-- The isomorphism `ofRepresentationMonodromyIso` is the identity at the basepoint. -/
@[simp]
theorem ofRepresentationMonodromyIso_app_mk (L : LocalCoefficientSystem.{u, v, w} R X) :
    (ofRepresentationMonodromyIso x L).app (FundamentalGroupoid.mk x) = Iso.refl _ :=
  Groupoid.natIsoOfEnd_app_self _ _ _

section Functor

variable (R) in
/-- **The local system of a representation, as a functor** from representations of `π₁(X, x)` over
`R` to local coefficient systems on `X`: a morphism of representations goes to the morphism of
local systems which is that morphism on every fiber. -/
-- Exposed, like `ofRepresentation`, so that the fibers of `(ofRepresentationFunctor x R).obj A`
-- are the module of `A` by definition: the statement of `ofRepresentationFunctor_map` needs it.
@[expose, simps]
def ofRepresentationFunctor :
    Rep.{w} R (FundamentalGroup X x) ⥤ LocalCoefficientSystem.{u, v, w} R X where
  obj A := ofRepresentation x A.ρ
  map f := ofRepresentationMap x f.hom
  map_id _ := ofRepresentationMap_id x
  map_comp f g := ofRepresentationMap_comp x f.hom g.hom

variable (R) in
/-- **The local system functor is fully faithful**: a morphism between the local systems of two
representations is induced by a unique morphism of representations, its component at the
basepoint. -/
def ofRepresentationFunctorFullyFaithful : (ofRepresentationFunctor x R).FullyFaithful where
  preimage α := Rep.ofHom (ofRepresentationHomEquiv x α)
  map_preimage α := (ofRepresentationHomEquiv x).symm_apply_apply α
  preimage_map f := Rep.hom_ext ((ofRepresentationHomEquiv x).apply_symm_apply f.hom)

instance : (ofRepresentationFunctor x R).Full :=
  (ofRepresentationFunctorFullyFaithful x R).full

instance : (ofRepresentationFunctor x R).Faithful :=
  (ofRepresentationFunctorFullyFaithful x R).faithful

/-- Every local system is the local system of its monodromy representation
(`ofRepresentationMonodromyIso`), so the local system functor is essentially surjective. -/
instance : (ofRepresentationFunctor x R).EssSurj :=
  ⟨fun L ↦ ⟨Rep.of (monodromyRepresentation L x), ⟨ofRepresentationMonodromyIso x L⟩⟩⟩

/-- **Local systems are representations of the fundamental group**: on a path-connected space,
the local system functor is an equivalence between representations of `π₁(X, x)` and local
systems on `X`. -/
instance : (ofRepresentationFunctor x R).IsEquivalence where

instance : (ofRepresentationFunctor x R).Additive where
  -- Both sums are computed componentwise on the underlying linear maps.
  map_add := rfl

/-- **A short exact sequence of representations gives a short exact sequence of local
systems**: for a short exact sequence `0 → A₁ → A₂ → A₃ → 0` of representations of `π₁(X, x)`,
the sequence of their local systems `0 → L(A₁) → L(A₂) → L(A₃) → 0` is short exact. -/
theorem shortExact_map_ofRepresentationFunctor
    {S : ShortComplex (Rep.{w} R (FundamentalGroup X x))} (hS : S.ShortExact) :
    (S.map (ofRepresentationFunctor x R)).ShortExact :=
  hS.map_of_exact _

end Functor

end TauCeti.LocalCoefficientSystem
