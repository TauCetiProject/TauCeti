/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.FundamentalGroupAction

/-!
# The associated-cover functor

The balanced product with the universal cover is functorial in a fundamental-group set:
an equivariant map of labels sends `⟦u, a⟧` to `⟦u, f a⟧`. Its fibre identification is natural,
so this concrete construction is naturally isomorphic to the inverse of the fibre-action
classification. Consequently it preserves colimits, including coproducts of actions. No
transitivity or nonemptiness is required: disconnected and empty covers are included.

The underlying construction and monodromy calculation are
`TauCeti.UniversalCover.actionCoveringSpace` and
`TauCeti.UniversalCover.actionCoveringSpaceFiberEquiv_apply_monodromy`.
The categorical comparison uses Mathlib's `CategoryTheory.Iso.isoCompInverse`.
-/

public section
noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti.UniversalCover

variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

/-- The action on labels used by the associated-cover functor. -/
local instance (A : Action (Type u) (FundamentalGroup X x₀)) :
    MulAction (FundamentalGroup X x₀) A.V := Action.instMulAction A

/-- Label sets carry the discrete topology in the associated-cover functor. -/
local instance (A : Action (Type u) (FundamentalGroup X x₀)) : TopologicalSpace A.V := ⊥
local instance (A : Action (Type u) (FundamentalGroup X x₀)) : DiscreteTopology A.V := ⟨rfl⟩

/-- The associated cover, functorially in the fundamental-group set. Equivariant maps act on
labels and leave the universal-cover coordinate fixed. The body is exposed so that the concrete
total-space and fibre types are available to consumers. -/
@[expose] def actionCoveringSpaceFunctor :
    Action (Type u) (FundamentalGroup X x₀) ⥤ CoveringSpace (TopCat.of X) where
  obj A := actionCoveringSpace x₀ A.V
  map f := actionCoveringSpaceMap x₀ f.hom fun g a => by
    exact congrArg (fun k => k a) (f.comm g)
  map_id A := actionCoveringSpaceMap_id x₀
  map_comp f k := actionCoveringSpaceMap_comp x₀ f.hom _ k.hom _

/-- The functor's object is the balanced-product cover with discrete labels. -/
@[simp]
theorem actionCoveringSpaceFunctor_obj (A : Action (Type u) (FundamentalGroup X x₀)) :
    (actionCoveringSpaceFunctor x₀).obj A = actionCoveringSpace x₀ A.V :=
  (rfl)

/-- The functor acts on an equivariant map by the corresponding map of associated covers. -/
@[simp]
theorem actionCoveringSpaceFunctor_map {A B : Action (Type u) (FundamentalGroup X x₀)}
    (f : A ⟶ B) :
    (actionCoveringSpaceFunctor x₀).map f =
      actionCoveringSpaceMap x₀ f.hom (fun g a => congrArg (fun k => k a) (f.comm g)) :=
  (rfl)

/-- The monodromy set of an associated cover is canonically the original action. -/
def actionCoveringSpaceFiberIso (A : Action (Type u) (FundamentalGroup X x₀)) :
    (CoveringSpace.fiberActionFunctor x₀).obj ((actionCoveringSpaceFunctor x₀).obj A) ≅ A :=
  Action.mkIso (actionCoveringSpaceFiberEquiv x₀ A.V).toIso fun g => by
    ext e
    exact actionCoveringSpaceFiberEquiv_apply_monodromy x₀ A.V g e

/-- The forward fibre-action isomorphism is the canonical numbering of the associated cover. -/
@[simp]
theorem actionCoveringSpaceFiberIso_hom_apply
    (A : Action (Type u) (FundamentalGroup X x₀))
    (e : ⇑(actionCoveringSpace x₀ A.V).proj ⁻¹' {x₀}) :
    (actionCoveringSpaceFiberIso x₀ A).hom.hom e = actionCoveringSpaceFiberEquiv x₀ A.V e :=
  (rfl)

/-- The inverse fibre-action isomorphism recovers the point with the given label. -/
@[simp]
theorem actionCoveringSpaceFiberIso_inv_apply
    (A : Action (Type u) (FundamentalGroup X x₀)) (a : A.V) :
    (actionCoveringSpaceFiberIso x₀ A).inv.hom a =
      (actionCoveringSpaceFiberEquiv x₀ A.V).symm a :=
  (rfl)

/-- The canonical identification of the associated cover's fibre with its labels is natural
in equivariant maps. -/
def actionCoveringSpaceFunctorCompFiberIso :
    actionCoveringSpaceFunctor x₀ ⋙ CoveringSpace.fiberActionFunctor x₀ ≅ 𝟭 _ :=
  NatIso.ofComponents (actionCoveringSpaceFiberIso x₀) fun {A B} f => by
    ext e
    -- Extensionality leaves `e` in the composite functor's wrapped fibre type. Rewriting the
    -- object equality would transport `e` and its dependent occurrences; instead, normalize
    -- its definitionally equal concrete fibre type and the composed morphism applications.
    change ⇑(actionCoveringSpace x₀ A.V).proj ⁻¹' {x₀} at e
    change (actionCoveringSpaceFiberIso x₀ _).hom.hom
        (((CoveringSpace.fiberActionFunctor x₀).map
          (actionCoveringSpaceMap x₀ f.hom (fun g a =>
            congrArg (fun k => k a) (f.comm g)))).hom e) =
      f.hom ((actionCoveringSpaceFiberIso x₀ _).hom.hom e)
    rw [CoveringSpace.fiberActionFunctor_map_hom]
    -- The map lemma leaves `TypeCat.ofHom` and `Action.mkIso` wrappers around the fibre map
    -- and fibre equivalence. Reducing their applications exposes the existing fibre-map API.
    change actionCoveringSpaceFiberEquiv x₀ B.V
        (Function.fiberMap (actionCoveringSpaceMap x₀ f.hom _).hom.left.hom
          (CoveringSpace.proj_hom_comp_hom_left_hom _) x₀ e) =
      f.hom (actionCoveringSpaceFiberEquiv x₀ A.V e)
    exact actionCoveringSpaceFiberEquiv_map x₀ f.hom _ e

/-- The forward component of the natural identification is the canonical fibre isomorphism. -/
@[simp]
theorem actionCoveringSpaceFunctorCompFiberIso_hom_app
    (A : Action (Type u) (FundamentalGroup X x₀)) :
    (actionCoveringSpaceFunctorCompFiberIso x₀).hom.app A =
      (actionCoveringSpaceFiberIso x₀ A).hom :=
  (rfl)

/-- The inverse component recovers the fibre point with the given label. -/
@[simp]
theorem actionCoveringSpaceFunctorCompFiberIso_inv_app
    (A : Action (Type u) (FundamentalGroup X x₀)) :
    (actionCoveringSpaceFunctorCompFiberIso x₀).inv.app A =
      (actionCoveringSpaceFiberIso x₀ A).inv :=
  (rfl)

/-- The balanced-product construction is naturally isomorphic to the chosen inverse of the
fibre-action classification. -/
def actionCoveringSpaceFunctorIsoInverse :
    actionCoveringSpaceFunctor x₀ ≅
      (CoveringSpace.fiberActionEquivalence (X := TopCat.of X) x₀).inverse := by
  let e : actionCoveringSpaceFunctor x₀ ⋙
      (CoveringSpace.fiberActionEquivalence (X := TopCat.of X) x₀).functor ≅ 𝟭 _ := by
    rw [CoveringSpace.fiberActionEquivalence_functor]
    exact actionCoveringSpaceFunctorCompFiberIso x₀
  exact e.isoCompInverse ≪≫
    (CoveringSpace.fiberActionEquivalence (X := TopCat.of X) x₀).inverse.leftUnitor

/-- The explicit associated-cover functor is an equivalence of categories. Mathlib therefore
supplies preservation of all colimits, in particular coproducts and the empty cover. -/
instance actionCoveringSpaceFunctor_isEquivalence :
    (actionCoveringSpaceFunctor x₀).IsEquivalence :=
  Functor.isEquivalence_of_iso (actionCoveringSpaceFunctorIsoInverse x₀).symm

end TauCeti.UniversalCover
