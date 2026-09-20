/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.Groupoid.Subgroupoid

/-!
# Basic results on fundamental groupoids

This file records basic facts about fundamental groupoids used when comparing the fundamental
groupoid of a space with those of its subspaces: the functor induced by an injective continuous
map is injective on objects (as `CategoryTheory.Subgroupoid.im` requires), membership of a
path class in a subgroupoid is unchanged by transporting its endpoints along equalities, and
the induced functor of a composite acts on a single morphism as the composite of the induced
functors.

## Main declarations

* `ContinuousMap.fundamentalGroupoid_map_obj_injective`: an injective continuous map
  induces a functor of fundamental groupoids that is injective on objects.
* `Path.Homotopic.Quotient.cast_mem_arrows_iff`: membership of a path class in a
  subgroupoid of the fundamental groupoid is unchanged by casting its endpoints along equalities.
* `FundamentalGroupoid.map_comp_map`: the morphism-level form of `FundamentalGroupoid.map_comp`.
-/

public section

open CategoryTheory

namespace Path.Homotopic.Quotient

/-- Membership of a path class in a subgroupoid of the fundamental groupoid is unchanged by
casting its endpoints along equalities. -/
@[simp]
theorem cast_mem_arrows_iff
    {X : Type*} [TopologicalSpace X]
    {S : CategoryTheory.Subgroupoid (_root_.FundamentalGroupoid X)} {a b a' b' : X}
    (q : Path.Homotopic.Quotient a b) (ha : a' = a) (hb : b' = b) :
    (q.cast (x' := a') (y' := b') ha hb :
        _root_.FundamentalGroupoid.mk a' ⟶ _root_.FundamentalGroupoid.mk b') ∈
        S.arrows (_root_.FundamentalGroupoid.mk a') (_root_.FundamentalGroupoid.mk b') ↔
      (q : _root_.FundamentalGroupoid.mk a ⟶ _root_.FundamentalGroupoid.mk b) ∈
        S.arrows (_root_.FundamentalGroupoid.mk a) (_root_.FundamentalGroupoid.mk b) := by
  subst ha hb
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]

end Path.Homotopic.Quotient

namespace FundamentalGroupoid

/-- The morphism-level form of `FundamentalGroupoid.map_comp`. The source and target of the two
sides agree definitionally, so unlike the equality of functors this form needs no `eqToHom`. -/
theorem map_comp_map {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (g : C(Y, Z)) (f : C(X, Y)) {a b : _root_.FundamentalGroupoid X} (p : a ⟶ b) :
    (map (g.comp f)).map p = (map g).map ((map f).map p) := by
  rcases p
  rfl

end FundamentalGroupoid

namespace ContinuousMap

/-- The functor between fundamental groupoids induced by an injective continuous map is injective
on objects. -/
theorem fundamentalGroupoid_map_obj_injective {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace A] (f : C(X, A)) (hf : Function.Injective f) :
    Function.Injective (_root_.FundamentalGroupoid.map f).obj := by
  rintro ⟨a⟩ ⟨b⟩ h
  exact congrArg _root_.FundamentalGroupoid.mk (hf (congrArg _root_.FundamentalGroupoid.as h))

end ContinuousMap
