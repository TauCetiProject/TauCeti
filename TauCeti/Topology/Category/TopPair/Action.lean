/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Action
public import TauCeti.Topology.Category.TopPair

/-!
# Continuous actions on pairs as functors to `TopPair`

Let a monoid `G` act on a space `X` by continuous maps `g • ·`, and let `S ⊆ X` be a subset which
every `g • ·` carries into itself. Then each `g • ·` is a map of pairs `(X, S) ⟶ (X, S)`, and these
form a functor `SingleObj G ⥤ TopPair` sending the unique object to `(X, S)`
(`TopPair.ofSubsetActionFunctor`), the analogue for pairs of the action functor
`TopCat.actionFunctor X G`.

Composed with a relative homology theory, it is the action of `G` on the relative homology of
`(X, S)`; for instance, for the quotient covering of a finite group action `G` and coefficients on
which `|G|` is invertible, the relative homology of the base is the object of invariants of this
action, by the transfer (`IsQuotientCoveringMap.isLimitHomologyMapConePairTransferCone`).
-/

public section

open CategoryTheory

universe w

namespace TopPair

variable (X : TopCat.{w}) (G : Type*) [Monoid G] [MulAction G X] [ContinuousConstSMul G X]
  (S : Set X) (hS : ∀ g : G, Set.MapsTo (g • ·) S S)

/-- A continuous action of a monoid `G` on a space `X` preserving a subset `S`, as the functor
`SingleObj G ⥤ TopPair` sending the unique object to the pair `(X, S)` and `g` to the map of pairs
induced by `g • ·`. -/
@[expose]
def ofSubsetActionFunctor : SingleObj G ⥤ TopPair.{w} :=
  SingleObj.functor
    { toFun g := .of (ofSubsetMap (TopCat.ofHom ⟨(g • · : X → X), continuous_const_smul g⟩) (hS g))
      map_one' := End.ext <| hom_ext_of_fst _ <| by
        rw [ofSubsetMap_fst]
        exact ConcreteCategory.hom_ext _ _ fun x ↦ one_smul G (α := X) x
      map_mul' g h := End.ext <| (ofSubsetMap_comp_ofSubsetMap_of_comp_eq (hS h) (hS g) (hS (g * h))
        (ConcreteCategory.hom_ext _ _ fun x ↦ (mul_smul g h x).symm)).symm }

@[simp]
lemma ofSubsetActionFunctor_obj (Y : SingleObj G) : (ofSubsetActionFunctor X G S hS).obj Y =
    ofSubset S :=
  (rfl)

lemma ofSubsetActionFunctor_map (g : G) :
    (ofSubsetActionFunctor X G S hS).map (X := SingleObj.star G) (Y := SingleObj.star G) g =
      ofSubsetMap (TopCat.ofHom ⟨(g • · : X → X), continuous_const_smul g⟩) (hS g) :=
  (rfl)

@[simp]
lemma ofSubsetActionFunctor_map_fst_apply (g : G) (x : X) :
    Hom.fst ((ofSubsetActionFunctor X G S hS).map (X := SingleObj.star G)
      (Y := SingleObj.star G) g) x = g • x :=
  ofSubsetMap_fst_apply _ _ x

end TopPair
