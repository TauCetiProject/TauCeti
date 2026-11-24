/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.CategoryTheory.Groupoid.Subgroupoid
public import Mathlib.CategoryTheory.IsConnected

/-!
# Basic results on fundamental groupoids

This file records basic facts about fundamental groupoids: over a path-connected space every pair
of objects is joined by a morphism so the fundamental groupoid is connected as a category, and
when comparing the fundamental groupoid of a space with those of its subspaces, the functor
induced by a continuous map is injective on objects exactly when the map is injective (as
`CategoryTheory.Subgroupoid.im` requires), membership of a path class in a subgroupoid is
unchanged by transporting its endpoints along equalities, a path that stays at its start has the
class of an identity, and the induced functor of a composite
acts on a single morphism as the composite of the induced functors.

## Main declarations

* `FundamentalGroupoid.nonempty_hom`, `FundamentalGroupoid.instIsConnected`: the fundamental
  groupoid of a path-connected space has nonempty hom-sets and is connected as a category.
* `ContinuousMap.fundamentalGroupoid_map_obj_injective_iff`: the functor of fundamental groupoids
  induced by a continuous map is injective on objects if and only if the map is injective.
* `Path.Homotopic.Quotient.cast_mem_arrows_iff`: membership of a path class in a
  subgroupoid of the fundamental groupoid is unchanged by casting its endpoints along equalities.
* `Path.Homotopic.Quotient.mk_eq_eqToHom_of_forall_apply_eq`: a path that stays at its start has
  the class of an identity, read along the equality of its endpoints.
* `FundamentalGroupoid.map_comp_map`: the morphism-level form of `FundamentalGroupoid.map_comp`.
* `FundamentalGroupoidFunctor.homotopicMapsNatIso_app`: the component at `x` of the natural
  isomorphism induced by a homotopy is the class of its trace at `x`.
-/

public section

open CategoryTheory

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The component at `x` of the natural isomorphism `homotopicMapsNatIso H` induced by a homotopy
`H` is the class of the trace `H.evalAt x.as` of the homotopy at `x`. -/
@[simp]
lemma FundamentalGroupoidFunctor.homotopicMapsNatIso_app {f₀ f₁ : C(X, Y)}
    (H : f₀.Homotopy f₁) (x : FundamentalGroupoid X) :
    (FundamentalGroupoidFunctor.homotopicMapsNatIso H).app x = ⟦H.evalAt x.as⟧ :=
  rfl

namespace Path.Homotopic.Quotient

/-- Membership of a path class in a subgroupoid of the fundamental groupoid is unchanged by
casting its endpoints along equalities. -/
@[simp]
theorem cast_mem_arrows_iff {S : Subgroupoid (FundamentalGroupoid X)} {a b a' b' : X}
    (q : Path.Homotopic.Quotient a b) (ha : a' = a) (hb : b' = b) :
    (q.cast (x' := a') (y' := b') ha hb : FundamentalGroupoid.mk a' ⟶ FundamentalGroupoid.mk b') ∈
        S.arrows (FundamentalGroupoid.mk a') (FundamentalGroupoid.mk b') ↔
      (q : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b) ∈
        S.arrows (FundamentalGroupoid.mk a) (FundamentalGroupoid.mk b) := by
  subst ha hb
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]

/-- A path whose points all equal its start has the class of an identity, read along the
equality of its endpoints. -/
theorem mk_eq_eqToHom_of_forall_apply_eq {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a b) (h : ∀ r, p r = a) :
    (Path.Homotopic.Quotient.mk p : _root_.FundamentalGroupoid.mk a ⟶
        _root_.FundamentalGroupoid.mk b) =
      eqToHom (congrArg _root_.FundamentalGroupoid.mk ((h 1).symm.trans p.target)) := by
  obtain rfl : b = a := p.target.symm.trans (h 1)
  obtain rfl : p = Path.refl _ := Path.ext (funext h)
  rw [eqToHom_refl]
  exact (_root_.FundamentalGroupoid.id_eq_path_refl _).symm

end Path.Homotopic.Quotient

namespace FundamentalGroupoid

/-- In the fundamental groupoid of a path-connected space every object receives a morphism from
every other one, so the groupoid is connected. -/
theorem nonempty_hom [PathConnectedSpace X] (x y : FundamentalGroupoid X) : Nonempty (x ⟶ y) :=
  ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x.as y.as)⟩

/-- The fundamental groupoid of a path-connected space is connected as a category. -/
instance instIsConnected [PathConnectedSpace X] :
    CategoryTheory.IsConnected (FundamentalGroupoid X) :=
  zigzag_isConnected fun x y ↦ .of_hom (nonempty_hom x y).some

/-- The morphism-level form of `FundamentalGroupoid.map_comp`. The source and target of the two
sides agree definitionally, so unlike the equality of functors this form needs no `eqToHom`. -/
theorem map_comp_map (g : C(Y, Z)) (f : C(X, Y)) {a b : FundamentalGroupoid X} (p : a ⟶ b) :
    (map (g.comp f)).map p = (map g).map ((map f).map p) := by
  simp only [map_map]
  exact Path.Homotopic.Quotient.map_comp

end FundamentalGroupoid

namespace ContinuousMap

/-- The functor between fundamental groupoids induced by a continuous map is injective on objects
if and only if the map is injective. -/
@[simp]
theorem fundamentalGroupoid_map_obj_injective_iff (f : C(X, Y)) :
    Function.Injective (FundamentalGroupoid.map f).obj ↔ Function.Injective f := by
  -- On objects, `map f` is `f` conjugated by the equivalence `FundamentalGroupoid.equiv`.
  have h : (FundamentalGroupoid.map f).obj =
      (FundamentalGroupoid.equiv Y).symm ∘ f ∘ FundamentalGroupoid.equiv X := by
    ext x
    simp
  rw [h, EquivLike.comp_injective, EquivLike.injective_comp]

end ContinuousMap
