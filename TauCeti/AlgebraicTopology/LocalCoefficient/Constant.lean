/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# Constant local coefficient systems and global trivializations

Over a path-connected space `X`, `FundamentalGroupoid X` is connected as a category
(`FundamentalGroupoid.instIsConnected`), so by `CategoryTheory.nat_trans_from_is_connected` every
morphism or isomorphism between constant local systems takes the same value at every point and comes
from `ModuleCat` (`constantFunctor_iso_eq_mapIso`), making
`TauCeti.LocalCoefficientSystem.constantFunctor` fully faithful. Consequently, once a local system
`L` admits a reference trivialization `e₀ : L ≅ (constantFunctor X).obj M`, all trivializations
`L ≅ (constantFunctor X).obj N` correspond bijectively to linear equivalences `M ≃ₗ[R] N`
(`trivializationEquivLinearEquiv`); in particular, global markings by `M` form a principal
homogeneous set under `M ≃ₗ[R] M`.

Without any connectedness hypothesis on `X`, any trivializable local system has trivial path
endomorphisms and trivial monodromy representation at every basepoint
(`monodromyRepresentation_eq_trivial_of_iso_constant`, `monodromyIsoTrivial`).

## Main definitions

* `TauCeti.LocalCoefficientSystem.constantAppIso`: the fiber isomorphism `L.obj x ≅ M` extracted
  from a trivialization `L ≅ (constantFunctor X).obj M`, typed directly with target `M`.
* `TauCeti.LocalCoefficientSystem.constantMonodromyIso`,
  `TauCeti.LocalCoefficientSystem.monodromyIsoTrivial`: the monodromy of a constant or
  trivializable local system at `x` is isomorphic in `Rep` to the trivial representation.
* `TauCeti.LocalCoefficientSystem.trivializationEquivLinearEquiv`: over a path-connected space,
  equivalence `(L ≅ (constantFunctor X).obj N) ≃ (M ≃ₗ[R] N)` induced by a reference
  trivialization `e₀ : L ≅ (constantFunctor X).obj M`.

## Main results

* `TauCeti.LocalCoefficientSystem.monodromyRepresentation_eq_trivial_of_iso_constant`: a
  trivializable local system has trivial monodromy representation at every point.
* `TauCeti.LocalCoefficientSystem.constantFunctor_iso_eq_mapIso`: over a path-connected space,
  every isomorphism between constant local systems is induced by its component at a point.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}

/-- The fiber isomorphism `L.obj x ≅ M` at `x` induced by a trivialization
`e : L ≅ (constantFunctor X).obj M`, typed directly with target `M` rather than
`((constantFunctor X).obj M).obj x`. -/
def constantAppIso {L : LocalCoefficientSystem.{u, v, w} R X} {M : ModuleCat.{w} R}
    (e : L ≅ (constantFunctor (R := R) X).obj M) (x : FundamentalGroupoid X) : L.obj x ≅ M where
  hom := e.hom.app x
  inv := e.inv.app x
  hom_inv_id := e.hom_inv_id_app x
  inv_hom_id := e.inv_hom_id_app x

@[simp]
theorem constantAppIso_hom {L : LocalCoefficientSystem.{u, v, w} R X} {M : ModuleCat.{w} R}
    (e : L ≅ (constantFunctor (R := R) X).obj M) (x : FundamentalGroupoid X) :
    (constantAppIso e x).hom = e.hom.app x :=
  (rfl)

@[simp]
theorem constantAppIso_inv {L : LocalCoefficientSystem.{u, v, w} R X} {M : ModuleCat.{w} R}
    (e : L ≅ (constantFunctor (R := R) X).obj M) (x : FundamentalGroupoid X) :
    (constantAppIso e x).inv = e.inv.app x :=
  (rfl)

/-- Under a trivialization `e : L ≅ (constantFunctor X).obj M`, transport along any path class `p`
factors through `M` as `(constantAppIso e x).hom ≫ (constantAppIso e y).inv`. -/
theorem map_eq_of_iso_constant {L : LocalCoefficientSystem.{u, v, w} R X} {M : ModuleCat.{w} R}
    (e : L ≅ (constantFunctor (R := R) X).obj M) {x y : FundamentalGroupoid X} (p : x ⟶ y) :
    L.map p = (constantAppIso e x).hom ≫ (constantAppIso e y).inv := by
  rw [← cancel_mono (constantAppIso e y).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  ext a
  exact e.hom.naturality_apply p a

/-- Under a trivialization of `L`, every loop class acts as the identity on its fiber. -/
theorem map_end_eq_id_of_iso_constant {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e : L ≅ (constantFunctor (R := R) X).obj M)
    {x : FundamentalGroupoid X} (p : x ⟶ x) :
    L.map p = 𝟙 (L.obj x) := by
  rw [map_eq_of_iso_constant e p, Iso.hom_inv_id]

/-- A local system admitting a trivialization has trivial monodromy representation at every
basepoint. -/
theorem monodromyRepresentation_eq_trivial_of_iso_constant
    {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e : L ≅ (constantFunctor (R := R) X).obj M) (x : X) :
    monodromyRepresentation L x =
      Representation.trivial R (FundamentalGroup X x) (L.obj (.mk x)) := by
  ext g a
  simp [map_end_eq_id_of_iso_constant e g.asHom]

/-- The monodromy representation of a trivializable local system is trivial in the sense of
`Representation.IsTrivial`. -/
theorem isTrivial_monodromyRepresentation_of_iso_constant
    {L : LocalCoefficientSystem.{u, v, w} R X} {M : ModuleCat.{w} R}
    (e : L ≅ (constantFunctor (R := R) X).obj M) (x : X) :
    (monodromyRepresentation L x).IsTrivial := by
  rw [monodromyRepresentation_eq_trivial_of_iso_constant e x]
  infer_instance

/-- The monodromy object of a constant local system at `x` is canonically isomorphic in `Rep` to
`(Rep.trivialFunctor R (FundamentalGroup X x)).obj M`. -/
def constantMonodromyIso (X : TopCat.{v}) (M : ModuleCat.{w} R) (x : X) :
    (monodromyFunctor R X x).obj ((constantFunctor (R := R) X).obj M) ≅
      (Rep.trivialFunctor R (FundamentalGroup X x)).obj M where
  hom := Rep.ofHom ⟨LinearMap.id, fun _ ↦ rfl⟩
  inv := Rep.ofHom ⟨LinearMap.id, fun _ ↦ rfl⟩

theorem constantMonodromyIso_hom_apply (X : TopCat.{v}) (M : ModuleCat.{w} R) (x : X) (m : M) :
    (constantMonodromyIso X M x).hom m = m :=
  (rfl)

theorem constantMonodromyIso_inv_apply (X : TopCat.{v}) (M : ModuleCat.{w} R) (x : X) (m : M) :
    (constantMonodromyIso X M x).inv m = m :=
  (rfl)

/-- A trivialization `e : L ≅ (constantFunctor X).obj M` identifies the monodromy representation
`(monodromyFunctor R X x).obj L` in `Rep` with the trivial representation on `M`. -/
def monodromyIsoTrivial {L : LocalCoefficientSystem.{u, v, w} R X} {M : ModuleCat.{w} R}
    (e : L ≅ (constantFunctor (R := R) X).obj M) (x : X) :
    (monodromyFunctor R X x).obj L ≅ (Rep.trivialFunctor R (FundamentalGroup X x)).obj M :=
  (monodromyFunctor R X x).mapIso e ≪≫ constantMonodromyIso X M x

theorem monodromyIsoTrivial_hom_apply {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e : L ≅ (constantFunctor (R := R) X).obj M) (x : X)
    (a : L.obj (.mk x)) :
    (monodromyIsoTrivial e x).hom a = e.hom.app (.mk x) a :=
  (rfl)

theorem monodromyIsoTrivial_inv_apply {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e : L ≅ (constantFunctor (R := R) X).obj M) (x : X) (m : M) :
    (monodromyIsoTrivial e x).inv m = e.inv.app (.mk x) m :=
  (rfl)

instance [Nonempty X] :
    (constantFunctor (R := R) X :
      ModuleCat.{w} R ⥤ LocalCoefficientSystem.{u, v, w} R X).Faithful :=
  inferInstanceAs (Functor.const (FundamentalGroupoid X)).Faithful

section PathConnected

variable [PathConnectedSpace X]

instance :
    (constantFunctor (R := R) X :
      ModuleCat.{w} R ⥤ LocalCoefficientSystem.{u, v, w} R X).Full :=
  inferInstanceAs (Functor.const (FundamentalGroupoid X)).Full

/-- Over a path-connected space, every isomorphism between constant local systems is induced by its
component at any chosen point. -/
theorem constantFunctor_iso_eq_mapIso {M N : ModuleCat.{w} R}
    (e : (constantFunctor (R := R) X).obj M ≅ (constantFunctor (R := R) X).obj N)
    (x : FundamentalGroupoid X) :
    e = (constantFunctor (R := R) X).mapIso (e.app x) :=
  Iso.ext <| NatTrans.ext <| funext fun y ↦ nat_trans_from_is_connected e.hom y x

/-- Given a reference trivialization `e₀ : L ≅ (constantFunctor X).obj M` over a path-connected
space `X`, all trivializations `L ≅ (constantFunctor X).obj N` correspond bijectively to linear
equivalences `M ≃ₗ[R] N`. When `N = M`, this exhibits the set of global markings of `L` by `M` as
a torsor under `M ≃ₗ[R] M`. -/
def trivializationEquivLinearEquiv {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e₀ : L ≅ (constantFunctor (R := R) X).obj M) (N : ModuleCat.{w} R) :
    (L ≅ (constantFunctor (R := R) X).obj N) ≃ (M ≃ₗ[R] N) where
  toFun e :=
    ((constantAppIso e₀ (.mk (Classical.arbitrary X))).symm ≪≫
      constantAppIso e (.mk (Classical.arbitrary X))).toLinearEquiv
  invFun α := e₀ ≪≫ (constantFunctor (R := R) X).mapIso α.toModuleIso
  left_inv e := by
    let x₀ : FundamentalGroupoid X := .mk (Classical.arbitrary X)
    ext x a
    have hconst := ConcreteCategory.congr_hom
      (nat_trans_from_is_connected (e₀.symm ≪≫ e).hom x₀ x) ((constantAppIso e₀ x).hom a)
    refine hconst.trans ?_
    -- After replacing `x₀` by `x`, `e₀.inv.app x` and `e₀.hom.app x` cancel via `constantAppIso`.
    change (constantAppIso e x).hom ((constantAppIso e₀ x).inv ((constantAppIso e₀ x).hom a)) =
      (constantAppIso e x).hom a
    rw [(constantAppIso e₀ x).hom_inv_id_apply]
  right_inv α := by
    let x₀ : FundamentalGroupoid X := .mk (Classical.arbitrary X)
    ext m
    -- Evaluate at `x₀`, where `e₀.inv.app x₀` and `e₀.hom.app x₀` cancel via `constantAppIso`.
    change α ((constantAppIso e₀ x₀).hom ((constantAppIso e₀ x₀).inv m)) = α m
    rw [(constantAppIso e₀ x₀).inv_hom_id_apply]

/-- Evaluating `trivializationEquivLinearEquiv` agrees with comparing the two trivializations at
any point of the path-connected base. -/
theorem trivializationEquivLinearEquiv_apply {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e₀ : L ≅ (constantFunctor (R := R) X).obj M) (N : ModuleCat.{w} R)
    (e : L ≅ (constantFunctor (R := R) X).obj N) (x : FundamentalGroupoid X) :
    trivializationEquivLinearEquiv e₀ N e =
      ((constantAppIso e₀ x).symm ≪≫ constantAppIso e x).toLinearEquiv := by
  have h : (constantAppIso e₀ (.mk (Classical.arbitrary X))).symm ≪≫
        constantAppIso e (.mk (Classical.arbitrary X)) =
      (constantAppIso e₀ x).symm ≪≫ constantAppIso e x :=
    Iso.ext (nat_trans_from_is_connected (e₀.symm ≪≫ e).hom (.mk (Classical.arbitrary X)) x)
  exact congrArg Iso.toLinearEquiv h

@[simp]
theorem trivializationEquivLinearEquiv_symm_apply {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e₀ : L ≅ (constantFunctor (R := R) X).obj M) (N : ModuleCat.{w} R)
    (α : M ≃ₗ[R] N) :
    (trivializationEquivLinearEquiv e₀ N).symm α =
      e₀ ≪≫ (constantFunctor (R := R) X).mapIso α.toModuleIso :=
  (rfl)

@[simp]
theorem trivializationEquivLinearEquiv_self {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e₀ : L ≅ (constantFunctor (R := R) X).obj M) :
    trivializationEquivLinearEquiv e₀ M e₀ = LinearEquiv.refl R M := by
  ext m
  simp [trivializationEquivLinearEquiv]

theorem trivializationEquivLinearEquiv_symm_refl {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e₀ : L ≅ (constantFunctor (R := R) X).obj M) :
    (trivializationEquivLinearEquiv e₀ M).symm (LinearEquiv.refl R M) = e₀ :=
  (trivializationEquivLinearEquiv e₀ M).symm_apply_eq.mpr
    (trivializationEquivLinearEquiv_self e₀).symm

end PathConnected

end TauCeti.LocalCoefficientSystem
